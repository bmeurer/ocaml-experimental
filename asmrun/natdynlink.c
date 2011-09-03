/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*                  Benedikt Meurer, University of Siegen              */
/*                                                                     */
/*    Copyright 2011 Lehrstuhl für Compilerbau und Softwareanalyse,    */
/*    Universität Siegen. All rights reserved. This file is distri-    */
/*    buted under the terms of the Q Public License version 1.0.       */
/*                                                                     */
/***********************************************************************/

/* $Id$ */

/* Dynamic link and JIT support for the native runtime */

#include <sys/types.h>
#include <sys/mman.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "misc.h"
#include "mlvalues.h"
#include "memory.h"
#include "stack.h"
#include "callback.h"
#include "alloc.h"
#include "natdynlink.h"
#include "osdeps.h"
#include "fail.h"

#if 0
# define D(fmt, ...) do { fprintf(stderr, (fmt), ##__VA_ARGS__); } while (0)
#else
# define D(fmt, ...) do {} while (0)
#endif

struct symbol {
  struct symbol *next;
  void          *addr;
  char           name[1];
};

#define SYMTBLSZ 113

static struct symbol *symtbl[SYMTBLSZ] = { NULL, };

static uint32 symhash(const void *v){
  /* This actually implements the widely used string hash apparently
   * posted by Daniel Bernstein to comp.lang.c once upon a time... */
  const signed char *p = v;
  uint32 h = 5381;
  while (*p != '\0')
    h = (h << 5) + h + *p++;
  return h % SYMTBLSZ;
}

static void addsym(char *name, void *addr){
  mlsize_t namelen = strlen(name);
  struct symbol *sym = malloc(sizeof(struct symbol) + namelen);
  struct symbol **symtblp = &symtbl[symhash(name)];
  memcpy(sym->name, name, namelen + 1);
  sym->addr = addr;
  sym->next = *symtblp;
  *symtblp = sym;
}

static void *getsym(void *handle, char *module, char *name){
  void *addr = NULL;
  struct symbol *sym;
  char *fullname = name;
  if (module != NULL) {
    fullname = malloc(strlen(module) + strlen(name) + 5);
    sprintf(fullname, "caml%s%s", module, name);
  }
  for (sym = symtbl[symhash(fullname)]; sym != NULL; sym = sym->next){
    if (strcmp(sym->name, fullname) == 0){
      addr = sym->addr;
      break;
    }
  }
  if (!addr) addr = caml_dlsym(handle, fullname);
  D("getsym(\"%s\") = %p\n", fullname, addr);
  if (name != fullname) free(fullname);
  return addr;
}

static void *getglobalsym(char *name){
  return getsym(caml_rtld_default(), NULL, name);
}

extern char caml_globals_map[];

CAMLprim value caml_natdynlink_getmap(value unit)
{
  return (value)caml_globals_map;
}

CAMLprim value caml_natdynlink_globals_inited(value unit)
{
  return Val_int(caml_globals_inited);
}

CAMLprim value caml_natdynlink_open(value filename, value global)
{
  CAMLparam1 (filename);
  CAMLlocal1 (res);
  void *sym;
  void *handle;

  handle = caml_dlopen(String_val(filename), 1, Int_val(global));

  if (NULL == handle)
    CAMLreturn(caml_copy_string(caml_dlerror()));

  sym = getsym(handle, NULL, "caml_plugin_header");
  if (NULL == sym){
    caml_dlclose(handle);
    CAMLreturn(caml_copy_string("not an OCaml plugin"));
  }

  res = caml_alloc_tuple(2);
  Field(res, 0) = (value) handle;
  Field(res, 1) = (value) (sym);
  CAMLreturn(res);
}

CAMLprim value caml_natdynlink_run(void *handle, value symbol) {
  CAMLparam1 (symbol);
  CAMLlocal1 (result);
  void *sym,*sym2;

#define optsym(n) getsym(handle,unit,n)
  char *unit;
  void (*entrypoint)(void);

  unit = String_val(symbol);

  sym = optsym("__frametable");
  if (NULL != sym) caml_register_frametable(sym);

  sym = optsym("");
  if (NULL != sym) caml_register_dyn_global(sym);

  sym = optsym("__data_begin");
  sym2 = optsym("__data_end");
  if (NULL != sym && NULL != sym2)
    caml_page_table_add(In_static_data, sym, sym2);

  sym = optsym("__code_begin");
  sym2 = optsym("__code_end");
  if (NULL != sym && NULL != sym2)
    caml_page_table_add(In_code_area, sym, sym2);

  entrypoint = optsym("__entry");
  if (NULL != entrypoint) result = caml_callback((value)(&entrypoint), 0);
  else result = Val_unit;

#undef optsym

  CAMLreturn (result);
}

CAMLprim value caml_natdynlink_run_toplevel(value filename, value symbol)
{
  CAMLparam2 (filename, symbol);
  CAMLlocal2 (res, v);
  void *handle;

  /* TODO: dlclose in case of error... */

  handle = caml_dlopen(String_val(filename), 1, 1);

  if (NULL == handle) {
    res = caml_alloc(1,1);
    v = caml_copy_string(caml_dlerror());
    Store_field(res, 0, v);
  } else {
    res = caml_alloc(1,0);
    v = caml_natdynlink_run(handle, symbol);
    Store_field(res, 0, v);
  }
  CAMLreturn(res);
}

CAMLprim value caml_natdynlink_loadsym(value symbol)
{
  CAMLparam1 (symbol);
  CAMLlocal1 (sym);

  sym = (value)getglobalsym(String_val(symbol));
  if (!sym) caml_failwith(String_val(symbol));
  CAMLreturn(sym);
}

/* JIT support */

CAMLprim value caml_natdynlink_run_jit(value symbol)
{
  D("caml_natdynlink_run_jit(\"%s\")\n", String_val(symbol));
  return caml_natdynlink_run(caml_rtld_default(), symbol);
}

CAMLprim value caml_natdynlink_malloc(value text_size, value data_size)
{
#define ABS(x) (((x) < 0) ? -(x) : (x))
#define ALIGN(x, n) ((((x) + ((n) - 1)) / (n)) * (n))
  CAMLparam2 (text_size, data_size);
  CAMLlocal1 (res);
  static char *data_ptr = NULL, *data_end = NULL;
  static char *text_ptr = NULL, *text_end = NULL;
  mlsize_t tsize = ALIGN(Long_val(text_size), 16);
  mlsize_t dsize = ALIGN(Long_val(data_size), 16);
  mlsize_t psize, size;
  char *area, *text, *data;

  /* Memory allocation tries to reuse already allocated memory,
   * which works in many cases. For 64bit architectures we ensure
   * that all data memory is within 32bit range from the text
   * memory allocated.
   */
  for (;;){
    /* Check if leftover space is sufficient */
    if (dsize < data_end - data_ptr && tsize < text_end - text_ptr){
      text = text_ptr; text_ptr += tsize;
      data = data_ptr; data_ptr += dsize;
      break;
    }

    psize = getpagesize();
    if (dsize < data_end - data_ptr){
      /* Need new text area */
      size = 2 * ALIGN(tsize, psize);
      area = (char *)mmap(NULL, size,
                          PROT_EXEC | PROT_READ | PROT_WRITE,
                          MAP_ANON | MAP_PRIVATE, -1, 0);
      if (area == (char *)MAP_FAILED) caml_raise_out_of_memory();
      text_ptr = area;
      text_end = area + size;
    }
    else if (tsize < text_end - text_ptr){
      /* Need new data area */
      size = 2 * ALIGN(dsize, psize);
      area = (char *)mmap(NULL, size,
                          PROT_READ | PROT_WRITE,
                          MAP_ANON | MAP_PRIVATE, -1, 0);
      if (area == (char *)MAP_FAILED) caml_raise_out_of_memory();
      data_ptr = area;
      data_end = area + size;
    }
    else{
      /* Need both new data and new text area */
      mlsize_t tsize_aligned = 2 * ALIGN(tsize, psize);
      mlsize_t dsize_aligned = 2 * ALIGN(dsize, psize);
      size = tsize_aligned + dsize_aligned;
      area = (char *)mmap(NULL, size,
                          PROT_EXEC | PROT_READ | PROT_WRITE,
                          MAP_ANON | MAP_PRIVATE, -1, 0);
      if (area == (char *)MAP_FAILED) caml_raise_out_of_memory();
      mprotect(area + tsize_aligned, dsize_aligned, PROT_READ | PROT_WRITE);
      text_ptr = area;
      text_end = text_ptr + tsize_aligned;
      data_ptr = text_end;
      data_end = data_ptr + dsize_aligned;
    }

#ifdef ARCH_SIXTYFOUR
    if (ABS(text_end - data_ptr) >= 2147483647
        || ABS(data_end - text_ptr) >= 2147483647){
      /* Out of 32bit addressing range, try again... */
      munmap(area, size);
      text_ptr = text_end = NULL;
      data_ptr = data_end = NULL;
    }
#endif
  }

  res = caml_alloc_tuple(2);
  Field(res, 0) = (value)caml_copy_nativeint((intnat)text);
  Field(res, 1) = (value)caml_copy_nativeint((intnat)data);
  CAMLreturn(res);
#undef ALIGN
#undef ABS
}

CAMLprim value caml_natdynlink_memcpy(value dst, value src, value size)
{
  D("caml_natdynlink_memcpy(%p, %p, %ld)\n", (void *)Nativeint_val(dst), String_val(src), Long_val(size));
  memcpy((void *)Nativeint_val(dst), String_val(src), Long_val(size));
  return Val_unit;
}

CAMLprim value caml_natdynlink_addsym(value name, value addr)
{
  D("caml_natdynlink_addsym(\"%s\", %p)\n", String_val(name), (void *)Nativeint_val(addr));
  addsym(String_val(name), (void *)Nativeint_val(addr));
  return Val_unit;
}

CAMLprim value caml_natdynlink_getsym(value name)
{
  void *addr;
  addr = getglobalsym(String_val(name));
  if (!addr) caml_failwith(String_val(name));
  return caml_copy_nativeint((intnat)addr);
}
