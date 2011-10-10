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

/* JIT support for the native toplevel */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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

CAMLprim value caml_natjit_getint16(value str, value ofs)
{
  return Val_long(*(const int16_t *)(String_val(str) + Long_val(ofs)));
}

CAMLprim value caml_natjit_getint32(value str, value ofs)
{
  return caml_copy_int32(*(const int32 *)(String_val(str) + Long_val(ofs)));
}

CAMLprim value caml_natjit_getint64(value str, value ofs)
{
  return caml_copy_int64(*(const int64 *)(String_val(str) + Long_val(ofs)));
}

CAMLprim value caml_natjit_putint16(value str, value ofs, value val)
{
  *((int16_t *)(String_val(str) + Long_val(ofs))) = Long_val(val);
  return Val_unit;
}

CAMLprim value caml_natjit_putint32(value str, value ofs, value val)
{
  *((int32 *)(String_val(str) + Long_val(ofs))) = Int32_val(val);
  return Val_unit;
}

CAMLprim value caml_natjit_putint64(value str, value ofs, value val)
{
  *((int64 *)(String_val(str) + Long_val(ofs))) = Int64_val(val);
  return Val_unit;
}

CAMLprim value caml_natjit_malloc(value text_size, value data_size)
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
   * which works in many cases. For the amd64 case we ensure
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

    psize = caml_getpagesize();
    if (dsize < data_end - data_ptr){
      /* Need new text area */
      size = 2 * ALIGN(tsize, psize);
      area = caml_mmap_rwx(size);
      if (area == NULL) caml_raise_out_of_memory();
      text_ptr = area;
      text_end = area + size;
    }
    else if (tsize < text_end - text_ptr){
      /* Need new data area */
      size = 2 * ALIGN(dsize, psize);
      area = caml_mmap_rwx(size);
      if (area == NULL) caml_raise_out_of_memory();
      caml_mprotect_rw(area, size);
      data_ptr = area;
      data_end = area + size;
    }
    else{
      /* Need both new data and new text area */
      mlsize_t tsize_aligned = 2 * ALIGN(tsize, psize);
      mlsize_t dsize_aligned = 2 * ALIGN(dsize, psize);
      size = tsize_aligned + dsize_aligned;
      area = (char *)caml_mmap_rwx(size);
      if (area == NULL) caml_raise_out_of_memory();
      caml_mprotect_rw(area + tsize_aligned, dsize_aligned);
      text_ptr = area;
      text_end = text_ptr + tsize_aligned;
      data_ptr = text_end;
      data_end = data_ptr + dsize_aligned;
    }

#ifdef TARGET_amd64
    if (ABS(text_end - data_ptr) >= 2147483647
        || ABS(data_end - text_ptr) >= 2147483647){
      /* Out of 32bit addressing range, try again... */
      caml_munmap(area, size);
      text_ptr = text_end = NULL;
      data_ptr = data_end = NULL;
    }
#endif
  }

  D("caml_natjit_malloc(%d, %d) = (%p, %p)\n", Long_val(text_size), Long_val(data_size), text, data);
  res = caml_alloc_tuple(2);
  Field(res, 0) = (value)caml_copy_nativeint((intnat)text);
  Field(res, 1) = (value)caml_copy_nativeint((intnat)data);
  CAMLreturn(res);
#undef ALIGN
#undef ABS
}

CAMLprim value caml_natjit_memcpy(value dst, value src, value size)
{
  D("caml_natjit_memcpy(%p, %p, %ld)\n", (void *)Nativeint_val(dst), String_val(src), Long_val(size));
  memcpy((void *)Nativeint_val(dst), String_val(src), Long_val(size));
  return Val_unit;
}


