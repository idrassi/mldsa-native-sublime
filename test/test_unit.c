/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "notrandombytes/notrandombytes.h"

#include "../mldsa/src/poly_kl.h"

#ifndef NUM_RANDOM_TESTS
#ifdef MLDSA_DEBUG
#define NUM_RANDOM_TESTS 1000
#else
#define NUM_RANDOM_TESTS 10000
#endif
#endif /* !NUM_RANDOM_TESTS */

#define CHECK(x)                                              \
  do                                                          \
  {                                                           \
    int r;                                                    \
    r = (x);                                                  \
    if (!r)                                                   \
    {                                                         \
      fprintf(stderr, "ERROR (%s,%d)\n", __FILE__, __LINE__); \
      return 1;                                               \
    }                                                         \
  } while (0)

/* Declarations for _c functions exposed by MLD_STATIC_TESTABLE= */
void mld_polyz_unpack_c(mld_poly *r, const uint8_t a[MLDSA_POLYZ_PACKEDBYTES]);
#if defined(MLD_USE_NATIVE_POLYZ_UNPACK_17) || \
    defined(MLD_USE_NATIVE_POLYZ_UNPACK_19)

/* Backend unit test helper functions */
static void print_i32_array(const char *label, const int32_t *array, size_t len)
{
  size_t i;
  fprintf(stderr, "%s:\n", label);
  for (i = 0; i < len; i++)
  {
    if (i % 8 == 0)
    {
      fprintf(stderr, "  ");
    }
    fprintf(stderr, "%8d", array[i]);
    if (i % 8 == 7)
    {
      fprintf(stderr, "\n");
    }
    else
    {
      fprintf(stderr, " ");
    }
  }
  if (len % 8 != 0)
  {
    fprintf(stderr, "\n");
  }
}

static int compare_i32_arrays(const int32_t *a, const int32_t *b, unsigned len,
                              const char *test_name, const int32_t *input)
{
  unsigned i;
  for (i = 0; i < len; i++)
  {
    if (a[i] != b[i])
    {
      fprintf(stderr, "FAIL: %s\n", test_name);
      fprintf(stderr,
              "  First difference at index %u: native=%d, reference=%d\n", i,
              a[i], b[i]);
      if (input)
      {
        print_i32_array("Input", input, len);
      }
      print_i32_array("Native result", a, len);
      print_i32_array("Reference result", b, len);
      return 0;
    }
  }
  return 1;
}

#if defined(MLD_USE_NATIVE_POLYZ_UNPACK_17) || \
    defined(MLD_USE_NATIVE_POLYZ_UNPACK_19)
static int test_mld_polyz_unpack_core(const uint8_t *input,
                                      const char *test_name)
{
  mld_poly test_poly, ref_poly;

  mld_polyz_unpack(&test_poly, input);
  mld_polyz_unpack_c(&ref_poly, input);

  CHECK(compare_i32_arrays(test_poly.coeffs, ref_poly.coeffs, MLDSA_N,
                           test_name, NULL));
  return 0;
}

static int test_native_polyz_unpack(void)
{
  uint8_t test_bytes[MLDSA_POLYZ_PACKEDBYTES];
  int i;

  memset(test_bytes, 0, MLDSA_POLYZ_PACKEDBYTES);
  CHECK(test_mld_polyz_unpack_core(test_bytes, "polyz_unpack_zeros") == 0);


  for (i = 0; i < NUM_RANDOM_TESTS; i++)
  {
    randombytes(test_bytes, MLDSA_POLYZ_PACKEDBYTES);
    CHECK(test_mld_polyz_unpack_core(test_bytes, "polyz_unpack_random") == 0);
  }

  return 0;
}
#endif /* MLD_USE_NATIVE_POLYZ_UNPACK_17 || MLD_USE_NATIVE_POLYZ_UNPACK_19 */


static int test_backend_units(void)
{
  /* Set fixed seed for reproducible tests */
  randombytes_reset();

#if defined(MLD_USE_NATIVE_POLYZ_UNPACK_17) || \
    defined(MLD_USE_NATIVE_POLYZ_UNPACK_19)
  CHECK(test_native_polyz_unpack() == 0);
#endif

  return 0;
}
#endif /* MLD_USE_NATIVE_POLYZ_UNPACK_17 || MLD_USE_NATIVE_POLYZ_UNPACK_19 */

int main(void)
{
  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  /* Run backend unit tests */
#if defined(MLD_USE_NATIVE_POLYZ_UNPACK_17)
  CHECK(test_backend_units() == 0);
#endif


  return 0;
}
