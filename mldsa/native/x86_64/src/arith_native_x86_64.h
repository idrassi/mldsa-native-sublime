/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLD_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#define MLD_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#include "../../../common.h"

#include <immintrin.h>
#include <stdint.h>
#include "consts.h"
#define mld_ntt_avx2 MLD_NAMESPACE(ntt_avx2)
void mld_ntt_avx2(__m256i *r, const __m256i *mld_qdata);

#define mld_invntt_avx2 MLD_NAMESPACE(invntt_avx2)
void mld_invntt_avx2(__m256i *r, const __m256i *mld_qdata);

#define mld_nttunpack_avx2 MLD_NAMESPACE(nttunpack_avx2)
void mld_nttunpack_avx2(__m256i *r);

#define mld_poly_pointwise_montgomery_asm \
  MLD_NAMESPACE(poly_pointwise_montgomery_asm)
void mld_poly_pointwise_montgomery_asm(int32_t *c, const int32_t *a,
                                       const int32_t *b);

#define mld_polyveck_pointwise_poly_montgomery_k4_asm \
  MLD_NAMESPACE(polyveck_pointwise_poly_montgomery_k4_asm)
void mld_polyveck_pointwise_poly_montgomery_k4_asm(int32_t *r, const int32_t *a,
                                                   const int32_t *v);

#define mld_polyveck_pointwise_poly_montgomery_k6_asm \
  MLD_NAMESPACE(polyveck_pointwise_poly_montgomery_k6_asm)
void mld_polyveck_pointwise_poly_montgomery_k6_asm(int32_t *r, const int32_t *a,
                                                   const int32_t *v);

#define mld_polyveck_pointwise_poly_montgomery_k8_asm \
  MLD_NAMESPACE(polyveck_pointwise_poly_montgomery_k8_asm)
void mld_polyveck_pointwise_poly_montgomery_k8_asm(int32_t *r, const int32_t *a,
                                                   const int32_t *v);

#endif /* !MLD_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H */
