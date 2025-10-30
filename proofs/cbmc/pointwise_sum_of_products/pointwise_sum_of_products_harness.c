// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "polyvec.h"

#define mld_pointwise_sum_of_products \
  MLD_NAMESPACE_KL(mld_pointwise_sum_of_products)
int64_t mld_pointwise_sum_of_products(const mld_polyvecl *u,
                                      const mld_polyvecl *v, unsigned int i);

void harness(void)
{
  mld_polyvecl *u, *v;
  unsigned int i;
  int64_t r;
  r = mld_pointwise_sum_of_products(u, v, i);
}
