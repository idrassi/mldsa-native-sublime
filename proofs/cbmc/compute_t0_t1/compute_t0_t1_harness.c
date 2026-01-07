// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

static void mld_compute_t0_t1(mld_poly *t1, mld_poly *t0, mld_polyvecl *matrow,
                              const mld_polyvecl *s1, const mld_poly *s2,
                              mld_poly *t);
void harness(void)
{
  mld_poly *t0;
  mld_poly *t1;
  mld_polyvecl *matrow;
  mld_polyvecl *s1;
  mld_poly *s2;
  mld_poly *t;

  mld_compute_t0_t1(t1, t0, matrow, s1, s2, t);
}
