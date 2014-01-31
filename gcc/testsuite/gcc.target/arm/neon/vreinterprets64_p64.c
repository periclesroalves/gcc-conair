/* Test the `vreinterprets64_p64' ARM Neon intrinsic.  */
/* This file was autogenerated by neon-testgen.  */

/* { dg-do assemble } */
/* { dg-require-effective-target arm_crypto_ok } */
/* { dg-options "-save-temps -O0" } */
/* { dg-add-options arm_crypto } */

#include "arm_neon.h"

void test_vreinterprets64_p64 (void)
{
  int64x1_t out_int64x1_t;
  poly64x1_t arg0_poly64x1_t;

  out_int64x1_t = vreinterpret_s64_p64 (arg0_poly64x1_t);
}

/* { dg-final { cleanup-saved-temps } } */
