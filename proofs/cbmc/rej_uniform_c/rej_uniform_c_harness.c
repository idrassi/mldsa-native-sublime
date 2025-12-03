// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "poly.h"

static int mld_rej_uniform_c(int32_t *a, int target, int offset,
                             const uint8_t *buf, int buflen);

void harness(void)
{
  int32_t *a;
  int target;
  int offset;
  const uint8_t *buf;
  int buflen;

  mld_rej_uniform_c(a, target, offset, buf, buflen);
}
