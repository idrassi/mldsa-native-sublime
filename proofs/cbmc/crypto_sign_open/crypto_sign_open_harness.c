// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "api.h"
#include "sign.h"

void harness(void)
{
  uint8_t *m;
  size_t *mlen;
  const uint8_t *sm;
  size_t smlen;
  const uint8_t *ctx;
  size_t ctxlen;
  const uint8_t *pk;

  crypto_sign_open(m, mlen, sm, smlen, ctx, ctxlen, pk);
}
