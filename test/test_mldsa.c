/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../mldsa/sign.h"
#include "../mldsa/sys.h"
#include "notrandombytes/notrandombytes.h"

#ifndef NTESTS
#define NTESTS 100
#endif
#define MLEN 59
#define CTXLEN 1

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

static int test_sign(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t sm[MLEN + CRYPTO_BYTES];
  uint8_t m[MLEN];
  uint8_t m2[MLEN + CRYPTO_BYTES];
  uint8_t ctx[CTXLEN];
  size_t smlen;
  size_t mlen;
  int rc;


  CHECK(crypto_sign_keypair(pk, sk) == 0);
  randombytes(ctx, CTXLEN);
  MLD_CT_TESTING_SECRET(ctx, sizeof(ctx));
  randombytes(m, MLEN);
  MLD_CT_TESTING_SECRET(m, sizeof(m));

  CHECK(crypto_sign(sm, &smlen, m, MLEN, ctx, CTXLEN, sk) == 0);

  rc = crypto_sign_open(m2, &mlen, sm, smlen, ctx, CTXLEN, pk);

  /* Constant time: Declassify outputs to check them. */
  MLD_CT_TESTING_DECLASSIFY(rc, sizeof(int));
  MLD_CT_TESTING_DECLASSIFY(m, sizeof(m));
  MLD_CT_TESTING_DECLASSIFY(m2, sizeof(m2));

  if (rc)
  {
    printf("ERROR: crypto_sign_open\n");
    return 1;
  }

  if (memcmp(m, m2, MLEN))
  {
    printf("ERROR: crypto_sign_open - wrong message\n");
    return 1;
  }

  if (smlen != MLEN + CRYPTO_BYTES)
  {
    printf("ERROR: crypto_sign_open - wrong smlen\n");
    return 1;
  }

  if (mlen != MLEN)
  {
    printf("ERROR: crypto_sign_open - wrong mlen\n");
    return 1;
  }

  return 0;
}

static int test_wrong_pk(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t sm[MLEN + CRYPTO_BYTES];
  uint8_t m[MLEN];
  uint8_t m2[MLEN + CRYPTO_BYTES] = {0};
  uint8_t ctx[CTXLEN];
  size_t smlen;
  size_t mlen;
  int rc;
  size_t idx;
  size_t i;

  CHECK(crypto_sign_keypair(pk, sk) == 0);
  randombytes(ctx, CTXLEN);
  MLD_CT_TESTING_SECRET(ctx, sizeof(ctx));
  randombytes(m, MLEN);
  MLD_CT_TESTING_SECRET(m, sizeof(m));

  CHECK(crypto_sign(sm, &smlen, m, MLEN, ctx, CTXLEN, sk) == 0);

  /* flip bit in public key */
  randombytes((uint8_t *)&idx, sizeof(size_t));
  idx %= CRYPTO_PUBLICKEYBYTES;

  pk[idx] ^= 1;

  rc = crypto_sign_open(m2, &mlen, sm, smlen, ctx, CTXLEN, pk);

  /* Constant time: Declassify outputs to check them. */
  MLD_CT_TESTING_DECLASSIFY(rc, sizeof(int));
  MLD_CT_TESTING_DECLASSIFY(m2, sizeof(m2));

  if (!rc)
  {
    printf("ERROR: wrong_pk: crypto_sign_open\n");
    return 1;
  }

  for (i = 0; i < MLEN; i++)
  {
    if (m2[i] != 0)
    {
      printf("ERROR: wrong_pk: crypto_sign_open - message should be zero\n");
      return 1;
    }
  }
  return 0;
}

static int test_wrong_sig(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t sm[MLEN + CRYPTO_BYTES];
  uint8_t m[MLEN];
  uint8_t m2[MLEN + CRYPTO_BYTES] = {0};
  uint8_t ctx[CTXLEN];
  size_t smlen;
  size_t mlen;
  int rc;
  size_t idx;
  size_t i;

  CHECK(crypto_sign_keypair(pk, sk) == 0);
  randombytes(ctx, CTXLEN);
  MLD_CT_TESTING_SECRET(ctx, sizeof(ctx));
  randombytes(m, MLEN);
  MLD_CT_TESTING_SECRET(m, sizeof(m));

  CHECK(crypto_sign(sm, &smlen, m, MLEN, ctx, CTXLEN, sk) == 0);

  /* flip bit in signed message */
  randombytes((uint8_t *)&idx, sizeof(size_t));
  idx %= MLEN + CRYPTO_BYTES;

  sm[idx] ^= 1;

  rc = crypto_sign_open(m2, &mlen, sm, smlen, ctx, CTXLEN, pk);

  /* Constant time: Declassify outputs to check them. */
  MLD_CT_TESTING_DECLASSIFY(rc, sizeof(int));
  MLD_CT_TESTING_DECLASSIFY(m2, sizeof(m2));

  if (!rc)
  {
    printf("ERROR: wrong_sig: crypto_sign_open\n");
    return 1;
  }

  for (i = 0; i < MLEN; i++)
  {
    if (m2[i] != 0)
    {
      printf("ERROR: wrong_sig: crypto_sign_open - message should be zero\n");
      return 1;
    }
  }
  return 0;
}


static int test_wrong_ctx(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t sm[MLEN + CRYPTO_BYTES];
  uint8_t m[MLEN];
  uint8_t m2[MLEN + CRYPTO_BYTES] = {0};
  uint8_t ctx[CTXLEN];
  size_t smlen;
  size_t mlen;
  int rc;
  size_t idx;
  size_t i;

  CHECK(crypto_sign_keypair(pk, sk) == 0);
  randombytes(ctx, CTXLEN);
  MLD_CT_TESTING_SECRET(ctx, sizeof(ctx));
  randombytes(m, MLEN);
  MLD_CT_TESTING_SECRET(m, sizeof(m));

  CHECK(crypto_sign(sm, &smlen, m, MLEN, ctx, CTXLEN, sk) == 0);

  /* flip bit in ctx */
  randombytes((uint8_t *)&idx, sizeof(size_t));
  idx %= CTXLEN;

  ctx[idx] ^= 1;

  rc = crypto_sign_open(m2, &mlen, sm, smlen, ctx, CTXLEN, pk);

  /* Constant time: Declassify outputs to check them. */
  MLD_CT_TESTING_DECLASSIFY(rc, sizeof(int));
  MLD_CT_TESTING_DECLASSIFY(m2, sizeof(m2));

  if (!rc)
  {
    printf("ERROR: wrong_sig: crypto_sign_open\n");
    return 1;
  }

  for (i = 0; i < MLEN; i++)
  {
    if (m2[i] != 0)
    {
      printf("ERROR: wrong_sig: crypto_sign_open - message should be zero\n");
      return 1;
    }
  }
  return 0;
}

int main(void)
{
  unsigned i;
  int r;

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  for (i = 0; i < NTESTS; i++)
  {
    r = test_sign();
    r |= test_wrong_pk();
    r |= test_wrong_sig();
    r |= test_wrong_ctx();
    if (r)
    {
      return 1;
    }
  }

  printf("CRYPTO_SECRETKEYBYTES:  %d\n", CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_PUBLICKEYBYTES:  %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_BYTES: %d\n", CRYPTO_BYTES);

  return 0;
}
