// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

int mld_attempt_signature_generation(uint8_t *sig, const uint8_t *mu,
                                     const uint8_t rhoprime[MLDSA_CRHBYTES],
                                     uint16_t nonce,
                                     const polyvecl mat[MLDSA_K],
                                     const polyvecl *s1, const polyveck *s2,
                                     const polyveck *t0);

void harness(void)
{
  uint8_t *sig;
  uint8_t *mu;
  uint8_t *rhoprime;
  uint16_t nonce;
  polyvecl *mat;
  polyvecl *s1;
  polyveck *s2;
  polyveck *t0;

  int r;
  r = mld_attempt_signature_generation(sig, mu, rhoprime, nonce, mat, s1, s2,
                                       t0);
}
