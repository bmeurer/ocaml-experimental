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

/* JIT C part of the runtime system for ocamlnat */

#include <sys/types.h>
#include <sys/mman.h>
#include <string.h>
#include <unistd.h>
#include "fail.h"
#include "memory.h"
#include "mlvalues.h"
#include "osdeps.h"

typedef struct caml_natjit_sym {
  struct caml_natjit_sym *next;
  intnat                  addr;
  char                    name[1];
} caml_natjit_sym;

static caml_natjit_sym *caml_natjit_symbols = NULL;

CAMLprim value caml_natjit_pagesize()
{
  return Val_long(getpagesize());
}

CAMLprim value caml_natjit_alloc(value size)
{
  CAMLparam1 (size);
  CAMLlocal1 (addr);

  addr = (value)mmap(NULL, Long_val(size),
                     PROT_READ | PROT_WRITE,
                     MAP_ANON | MAP_PRIVATE,
                     -1, 0);
  if (addr == (value)MAP_FAILED) caml_raise_out_of_memory();
  addr = caml_copy_nativeint(addr);
  CAMLreturn(addr);
}

CAMLprim value caml_natjit_memcpy(value dst, value src, value size)
{
  memcpy((void *)dst, String_val(src), Long_val(size));
  return Val_unit;
}

CAMLprim value caml_natjit_mkexec(value addr, value size)
{
  if (mprotect((void *)Nativeint_val(addr), Long_val(size),
               PROT_EXEC | PROT_READ) < 0) {
    caml_failwith("mprotect");
  }
  return Val_unit;
}

/* TODO: Need to fix caml_natdynlink_loadsym as well */
CAMLprim value caml_natjit_lookupsym(value symbol)
{
  CAMLparam1 (symbol);
  CAMLlocal1 (addr);
  caml_natjit_sym *sym;
  char *name;

  name = String_val(symbol);
  for (addr = (value)NULL, sym = caml_natjit_symbols; sym; sym = sym->next) {
    if (strcmp(sym->name, name) == 0) {
      addr = sym->addr;
      break;
    }
  }
  if (!addr) addr = (value)caml_globalsym(name);
  if (!addr) caml_failwith(name);
  addr = caml_copy_nativeint(addr);
  CAMLreturn(addr);
}

CAMLprim value caml_natjit_registersym(value symbol, value addr)
{
  CAMLparam2 (symbol, addr);
  caml_natjit_sym *sym;
  const char *name = String_val(symbol);
  size_t namelen = strlen(name);

  sym = (caml_natjit_sym *)malloc(sizeof(*sym) + namelen);
  if (!sym) caml_raise_out_of_memory();
  memcpy(sym->name, name, namelen + 1);
  sym->addr = Nativeint_val(addr);
  sym->next = caml_natjit_symbols;
  caml_natjit_symbols = sym;
  CAMLreturn(Val_unit);
}

