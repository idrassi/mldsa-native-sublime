// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <stdint.h>
#include "params.h"

void mld_invntt_layer(int32_t r[MLDSA_N], int layer);

void harness(void)
{
  int32_t *r;
  int layer;
  mld_invntt_layer(r, layer);
}
