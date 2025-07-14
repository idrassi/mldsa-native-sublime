// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "poly.h"


void harness(void)
{
  mld_poly *c;
  uint8_t *seed;
  poly_challenge(c, seed);
}
