// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "api.h"
#include "sign.h"

void harness(void)
{
  uint8_t *pk, *sk;
  int r;
  r = crypto_sign_keypair(pk, sk);
}
