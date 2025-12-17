// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

void mld_cbmc_workaround_8813(mld_polyvecl **p1, mld_polyveck **p2);

void harness(void)
{
  mld_polyvecl **p1;
  mld_polyveck **p2;

  mld_cbmc_workaround_8813(p1, p2);
}
