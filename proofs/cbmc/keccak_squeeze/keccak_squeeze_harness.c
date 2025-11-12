// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "fips202/fips202.h"

static int keccak_squeeze(uint8_t *out, size_t outlen,
                          uint64_t s[MLD_KECCAK_LANES], int pos, int r);

void harness(void)
{
  uint8_t *out;
  size_t outlen;
  uint64_t *s;
  int pos, r, r2;

  r2 = keccak_squeeze(out, outlen, s, pos, r);
}
