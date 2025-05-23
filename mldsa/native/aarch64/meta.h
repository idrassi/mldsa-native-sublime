/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_NATIVE_AARCH64_META_H
#define MLD_NATIVE_AARCH64_META_H

/* Set of primitives that this backend replaces */
#define MLD_USE_NATIVE_NTT
#define MLD_USE_NATIVE_INTT
#define MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLD_ARITH_BACKEND_AARCH64


#if !defined(__ASSEMBLER__)
#include "src/arith_native_aarch64.h"

static MLD_INLINE void mld_ntt_native(int32_t data[MLDSA_N])
{
  mld_ntt_asm(data, mld_aarch64_ntt_zetas_layer123456,
              mld_aarch64_ntt_zetas_layer78);
}

static MLD_INLINE void mld_intt_native(int32_t data[MLDSA_N])
{
  mld_intt_asm(data, mld_aarch64_intt_zetas_layer78,
               mld_aarch64_intt_zetas_layer123456);
}

static MLD_INLINE void mld_polyvecl_pointwise_acc_montgomery_l4_native(
    int32_t w[MLDSA_N], const int32_t u[4 * MLDSA_N],
    const int32_t v[4 * MLDSA_N])
{
  mld_polyvecl_pointwise_acc_montgomery_l4_asm(w, u, v);
}

static MLD_INLINE void mld_polyvecl_pointwise_acc_montgomery_l5_native(
    int32_t w[MLDSA_N], const int32_t u[5 * MLDSA_N],
    const int32_t v[5 * MLDSA_N])
{
  mld_polyvecl_pointwise_acc_montgomery_l5_asm(w, u, v);
}

static MLD_INLINE void mld_polyvecl_pointwise_acc_montgomery_l7_native(
    int32_t w[MLDSA_N], const int32_t u[7 * MLDSA_N],
    const int32_t v[7 * MLDSA_N])
{
  mld_polyvecl_pointwise_acc_montgomery_l7_asm(w, u, v);
}

#endif /* !__ASSEMBLER__ */

#endif /* !MLD_NATIVE_AARCH64_META_H */
