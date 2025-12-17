// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

int mld_attempt_signature_generation_alloc(
    uint8_t sig[MLDSA_CRYPTO_BYTES], const uint8_t *mu,
    const uint8_t rhoprime[MLDSA_CRHBYTES], uint16_t nonce,
    const mld_polymat *mat, const mld_polyvecl *s1, const mld_polyveck *s2,
    const mld_polyveck *t0, uint8_t challenge_bytes[MLDSA_CTILDEBYTES],
    mld_polyvecl *y, mld_polyveck *h, mld_polyvecl *z, mld_polyveck *w1,
    mld_polyveck *w0, mld_poly *cp);

void harness(void)
{
  uint8_t *sig;
  uint8_t *mu;
  uint8_t *rhoprime;
  uint16_t nonce;
  mld_polymat *mat;
  mld_polyvecl *s1;
  mld_polyveck *s2;
  mld_polyveck *t0;
  uint8_t *challenge_bytes;
  mld_polyvecl *y;
  mld_polyveck *h;
  mld_polyvecl *z;
  mld_polyveck *w1;
  mld_polyveck *w0;
  mld_poly *cp;

  int r;
  r = mld_attempt_signature_generation_alloc(sig, mu, rhoprime, nonce, mat, s1,
                                             s2, t0, challenge_bytes, y, h, z,
                                             w1, w0, cp);
}
