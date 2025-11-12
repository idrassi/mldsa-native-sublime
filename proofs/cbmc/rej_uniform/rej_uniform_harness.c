// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "poly.h"

static int mld_rej_uniform(int32_t *a, int target, int offset,
                           const uint8_t *buf, int buflen);

void harness(void)
{
  int32_t *a;
  int target, offset, buflen, r;
  const uint8_t *buf;

  r = mld_rej_uniform(a, target, offset, buf, buflen);
}
