/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H
#define MLD_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H

#include "../../../../common.h"

#define mld_keccakf1600x4_permute24 \
  MLD_NAMESPACE(KeccakP1600times4_PermuteAll_24rounds)
void mld_keccakf1600x4_permute24(void *states);

#define mld_keccakf1600x1_permute24 MLD_NAMESPACE(KeccakP1600_Permute_24rounds)
void mld_keccakf1600x1_permute24(void *state);

#endif /* !MLD_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H */
