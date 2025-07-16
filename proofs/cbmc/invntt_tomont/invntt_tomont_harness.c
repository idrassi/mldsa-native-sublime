// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <stdint.h>
#include "ntt.h"
#include "params.h"

void harness(void)
{
  int32_t *a;
  mld_invntt_tomont(a);
}
