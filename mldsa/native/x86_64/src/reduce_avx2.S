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

.text
.balign 16                                      /* Ensure 16-byte alignment for AVX2 code */
.global MLD_ASM_NAMESPACE(poly_reduce_avx2)
MLD_ASM_FN_SYMBOL(poly_reduce_avx2)
    /* Load constants */
    vpbroadcastd    .Lmldsa_q(%rip), %ymm0      /* q in all lanes */
    vpbroadcastd    .Loffset(%rip), %ymm1       /* offset (1 << 22) in all lanes */
    
    /* Setup loop counter */
    xor             %rax, %rax                  /* byte offset = 0 */
    mov             $MLDSA_N*4, %rcx            /* Total bytes to process (MLDSA_N * sizeof(int32_t)) */
    
.Lloop:
    /* Load 8 int32_t values */
    vmovdqa         (%rdi,%rax), %ymm2          /* f = _mm256_load_si256(&rr[i]) */
    
    /* Perform reduction */
    vpaddd          %ymm1, %ymm2, %ymm3         /* g = f + offset */
    vpsrad          $23, %ymm3, %ymm3           /* g = g >> 23 */
    
    /* Multiply by q using vpmulld */
    vpmulld         %ymm0, %ymm3, %ymm3         /* g = g * q */
    
    /* Subtract from original value */
    vpsubd          %ymm3, %ymm2, %ymm2         /* f = f - g */
    
    /* Store result */
    vmovdqa         %ymm2, (%rdi,%rax)          /* _mm256_store_si256(&rr[i], f) */
    
    /* Increment counter and check loop condition */
    add             $32, %rax                   /* Move to next 32 bytes (8 int32_t values) */
    cmp             %rcx, %rax                  /* Compare with total bytes */
    jb              .Lloop
    
    /* Return */
    ret

/* Constants section */
.section .rodata
.balign 32                                      /* 32-byte alignment for AVX2 constants */
.Lmldsa_q:
    .int MLDSA_Q                                /* Only need one value for vpbroadcastd */
.Loffset:
    .int (1 << 22)                              /* Only need one value for vpbroadcastd */

#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT && !MLD_CONFIG_MULTILEVEL_NO_SHARED */
