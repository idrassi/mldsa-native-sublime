// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "api.h"
#include "sign.h"

void harness(void)
{
  const uint8_t *sig;
  size_t siglen;
  const uint8_t *m;
  size_t mlen;
  const uint8_t *pre;
  size_t prelen;
  const uint8_t *pk;
  int externalmu;

  crypto_sign_verify_internal(sig, siglen, m, mlen, pre, prelen, pk,
                              externalmu);
}
