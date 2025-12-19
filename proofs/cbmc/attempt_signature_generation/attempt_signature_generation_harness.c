// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

int mld_attempt_signature_generation(const uint8_t rhoprime[MLDSA_CRHBYTES],
                                     uint16_t nonce,
                                     const mld_polyveck *s2,
                                     mld_poly *cp);

void harness(void)
{
  uint8_t *rhoprime;
  uint16_t nonce;
  mld_polymat *mat;
  mld_polyveck *s2;
  mld_poly *cp;

  int r;
  r = mld_attempt_signature_generation(rhoprime, nonce, s2, cp);
}
