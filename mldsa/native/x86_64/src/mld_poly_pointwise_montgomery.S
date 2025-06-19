/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_X86_64_DEFAULT)

.macro montgomery_reduce_avx2 res, a, qinv, q
    // Montgomery reduction implementation using AVX2 instructions
    // Input: a (product of coefficients)
    // Output: res (reduced result)
    // Constants: qinv (QINV = 58728449), q (MLDSA_Q = 8380417)
    
    // 1. t = a & 0xFFFFFFFF (low 32 bits)
    // 2. m = t * QINV & 0xFFFFFFFF
    vpmulld \qinv, \a, %ymm5  // ymm5 = t * QINV (low 32 bits)
    
    // 3. t = (a + m*Q) >> 32
    vpmulld \q, %ymm5, %ymm6  // ymm6 = m * Q (low 32 bits)
    vpaddq \a, %ymm6, %ymm7   // ymm7 = a + m*Q
    vpsrlq $32, %ymm7, \res   // res = (a + m*Q) >> 32
.endm

.text
.global MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
.balign 4
MLD_ASM_FN_SYMBOL(poly_pointwise_montgomery_asm)
    // Save registers
    push %rbx
    push %r12
    push %r13
    
    // Load parameters
    // rdi: pointer to output polynomial c
    // rsi: pointer to input polynomial a
    // rdx: pointer to input polynomial b
    
    // Load constants
    movabs $58728449, %rax       // QINV = 58728449
    vpbroadcastd %eax, %ymm0     // Broadcast QINV to all elements of ymm0
    
    movabs $8380417, %rax        // MLDSA_Q = 8380417
    vpbroadcastd %eax, %ymm1     // Broadcast MLDSA_Q to all elements of ymm1
    
    // Process 8 coefficients at a time (32 iterations for 256 coefficients)
    mov $32, %rbx
    
loop_start:
    // Load 8 coefficients from each polynomial
    vmovdqa (%rsi), %ymm2        // Load 8 coefficients from a
    vmovdqa (%rdx), %ymm3        // Load 8 coefficients from b
    
    // Multiply coefficients
    vpmulld %ymm2, %ymm3, %ymm4  // ymm4 = a[i] * b[i] (low 32 bits)
    
    // Apply Montgomery reduction
    montgomery_reduce_avx2 %ymm4, %ymm4, %ymm0, %ymm1
    
    // Store result
    vmovdqa %ymm4, (%rdi)
    
    // Advance pointers
    add $32, %rsi
    add $32, %rdx
    add $32, %rdi
    
    // Decrement counter and loop
    dec %rbx
    jnz loop_start
    
    // Restore registers and return
    pop %r13
    pop %r12
    pop %rbx
    ret

#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT */
