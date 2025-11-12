// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "packing.h"

void harness(void)
{
  uint8_t *pk;
  const uint8_t *sk;
  mld_pack_pk_from_sk(pk, sk);
}
