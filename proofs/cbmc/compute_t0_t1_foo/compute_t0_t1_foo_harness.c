// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

void mld_compute_t0_t1_foo(mld_polyveck *t1, mld_polyveck *t0, mld_polymat *mat,
                           const mld_polyvecl *s1, const mld_polyveck *s2,
                           mld_poly *t);
void harness(void)
{
  mld_polyveck *t0;
  mld_polyveck *t1;
  mld_polymat *mat;
  mld_polyvecl *s1;
  mld_polyveck *s2;
  mld_poly *t;

  mld_compute_t0_t1_foo(t1, t0, mat, s1, s2, t);
}
