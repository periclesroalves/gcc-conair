/* { dg-do compile } */
/* { dg-options "-mavx512f -O2" } */
/* { dg-final { scan-assembler-times "vsqrtps\[ \\t\]+\[^\n\]*%zmm\[0-9\]\[^\{\]" 6 } } */
/* { dg-final { scan-assembler-times "vsqrtps\[ \\t\]+\[^\n\]*%zmm\[0-9\]\{%k\[1-7\]\}\[^\{\]" 2 } } */
/* { dg-final { scan-assembler-times "vsqrtps\[ \\t\]+\[^\n\]*%zmm\[0-9\]\{%k\[1-7\]\}\{z\}" 2 } } */
/* { dg-final { scan-assembler-times "vsqrtps\[ \\t\]+\[^\n\]*\{rn-sae\}\[^\n\]*%zmm\[0-9\]" 1 } } */
/* { dg-final { scan-assembler-times "vsqrtps\[ \\t\]+\[^\n\]*\{ru-sae\}\[^\n\]*%zmm\[0-9\]\{%k\[1-7\]\}\[^\{\]" 1 } } */
/* { dg-final { scan-assembler-times "vsqrtps\[ \\t\]+\[^\n\]*\{rz-sae\}\[^\n\]*%zmm\[0-9\]\{%k\[1-7\]\}\{z\}" 1 } } */

#include <immintrin.h>

volatile __m512 x;
volatile __mmask16 m;

void extern
avx512f_test (void)
{
  x = _mm512_sqrt_ps (x);
  x = _mm512_mask_sqrt_ps (x, m, x);
  x = _mm512_maskz_sqrt_ps (m, x);
  x = _mm512_sqrt_round_ps (x, _MM_FROUND_TO_NEAREST_INT);
  x = _mm512_mask_sqrt_round_ps (x, m, x, _MM_FROUND_TO_POS_INF);
  x = _mm512_maskz_sqrt_round_ps (m, x, _MM_FROUND_TO_ZERO);
}
