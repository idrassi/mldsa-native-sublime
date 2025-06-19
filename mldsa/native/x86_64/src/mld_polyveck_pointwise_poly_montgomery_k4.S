/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_X86_64_DEFAULT)

.text
.global MLD_ASM_NAMESPACE(polyveck_pointwise_poly_montgomery_k4_asm)
.balign 4
MLD_ASM_FN_SYMBOL(polyveck_pointwise_poly_montgomery_k4_asm)
    // Save registers
    push %rbx
    push %r12
    push %r13
    push %r14
    
    // Load parameters
    // rdi: pointer to output vector r
    // rsi: pointer to input polynomial a
    // rdx: pointer to input vector v
    
    // Save parameters
    mov %rdi, %r12  // r
    mov %rsi, %r13  // a
    mov %rdx, %r14  // v
    
    // Call poly_pointwise_montgomery for each polynomial in the vector
    
    // First polynomial
    mov %r12, %rdi  // r[0]
    mov %r13, %rsi  // a
    mov %r14, %rdx  // v[0]
    call MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
    
    // Second polynomial
    lea 1024(%r12), %rdi  // r[1]
    mov %r13, %rsi        // a
    lea 1024(%r14), %rdx  // v[1]
    call MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
    
    // Third polynomial
    lea 2048(%r12), %rdi  // r[2]
    mov %r13, %rsi        // a
    lea 2048(%r14), %rdx  // v[2]
    call MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
    
    // Fourth polynomial
    lea 3072(%r12), %rdi  // r[3]
    mov %r13, %rsi        // a
    lea 3072(%r14), %rdx  // v[3]
    call MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
    
    // Restore registers and return
    pop %r14
    pop %r13
    pop %r12
    pop %rbx
    ret

#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT */
