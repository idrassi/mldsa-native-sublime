// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "poly.h"

#define mld_rej_eta_c MLD_ADD_PARAM_SET(mld_rej_eta_c)
static int mld_rej_eta_c(int32_t *a, int target, int offset, const uint8_t *buf,
                         int buflen);

void harness(void)
{
  int32_t *a;
  int target;
  int offset;
  const uint8_t *buf;
  int buflen;

  mld_rej_eta_c(a, target, offset, buf, buflen);
}
