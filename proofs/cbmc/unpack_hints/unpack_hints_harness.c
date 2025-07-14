// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "packing.h"

int unpack_hints(mld_polyveck *h,
                 const uint8_t packed_hints[MLDSA_POLYVECH_PACKEDBYTES]);

void harness(void)
{
  uint8_t *sig;
  mld_polyveck *h;
  int r;
  r = unpack_hints(h, sig);
}
