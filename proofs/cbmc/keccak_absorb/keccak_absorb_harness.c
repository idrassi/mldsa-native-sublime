// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "fips202/fips202.h"

extern int keccak_absorb(uint64_t s[MLD_KECCAK_LANES], int pos, int r,
                         const uint8_t *in, size_t inlen);

void harness(void)
{
  uint64_t *s;
  int pos, r, r2;
  const uint8_t *in;
  size_t inlen;
  uint8_t p;

  r2 = keccak_absorb(s, pos, r, in, inlen);
}
