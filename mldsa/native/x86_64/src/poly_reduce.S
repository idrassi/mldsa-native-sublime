/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * This file is derived from the public domain
 * AVX2 Dilithium implementation @[REF_AVX2].
 */

#include "../../../common.h"

#if defined(MLD_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED)

#include "consts.h"

        .intel_syntax noprefix
        .text

#define a rdi
#define offset rax
#define count rcx

.balign 16
.global MLD_ASM_NAMESPACE(poly_reduce_avx2)
MLD_ASM_FN_SYMBOL(poly_reduce_avx2)

// Canonical reduction of polynomial coefficients for ML-DSA
// Input a[256] (signed 32-bit words); output a[256] (signed 32-bit words)
//
// This reduces each element of the 256-element array of 32-bit signed
// integers modulo 8380417 with the result being centered around zero,
// specifically -6283009 <= r <= 6283008, in-place.

// Load constants using inline approach
        mov     eax, 8380417
        movd    xmm0, eax
        vpbroadcastd ymm0, xmm0                   // q in all lanes
        
        mov     eax, 4194304                      // 1 << 22
        movd    xmm1, eax
        vpbroadcastd ymm1, xmm1                   // offset in all lanes
        
// Setup loop counter
        xor     offset, offset                    // byte offset = 0
        mov     count, 1024                       // Total bytes (MLDSA_N * sizeof(int32_t))
        
poly_reduce_loop:
// Load 8 int32_t values
        vmovdqa ymm2, [a+offset]                  // f = _mm256_load_si256(&rr[i])
        
// Perform reduction
        vpaddd  ymm3, ymm2, ymm1                  // g = f + offset
        vpsrad  ymm3, ymm3, 23                    // g = g >> 23
        
// Multiply by q using vpmulld
        vpmulld ymm3, ymm3, ymm0                  // g = g * q
        
// Subtract from original value
        vpsubd  ymm2, ymm2, ymm3                  // f = f - g
        
// Store result
        vmovdqa [a+offset], ymm2                  // _mm256_store_si256(&rr[i], f)
        
// Increment counter and check loop condition
        add     offset, 32                        // Move to next 32 bytes (8 int32_t values)
        cmp     offset, count                     // Compare with total bytes
        jb      poly_reduce_loop
        
// Return
        ret

#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT && !MLD_CONFIG_MULTILEVEL_NO_SHARED */
