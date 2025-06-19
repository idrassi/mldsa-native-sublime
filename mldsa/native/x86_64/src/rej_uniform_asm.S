/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED)

// We save the output on the stack first, and copy to the actual
// output buffer only in the end. This is because the main loop can overwrite
// by up to 60 bytes, which we account for here (we use 64 bytes for alignment).
#define STACK_SIZE (4*MLDSA_N + 64)

.text
.global MLD_ASM_NAMESPACE(rej_uniform_asm)
.align 32
MLD_ASM_FN_SYMBOL(rej_uniform_asm)
    // Function prologue
    push    %rbp
    mov     %rsp, %rbp
    sub     $STACK_SIZE, %rsp
    and     $-32, %rsp                  // Align stack to 32 bytes for AVX2
    
    // Save callee-saved registers
    push    %rbx
    push    %r12
    push    %r13
    push    %r14
    push    %r15
    
    // Parameters:
    // %rdi = output buffer
    // %rsi = input buffer
    // %rdx = input buffer length
    // %rcx = table pointer
    
    // Save parameters
    mov     %rdi, %r14                  // r14 = output buffer
    mov     %rsi, %r13                  // r13 = input buffer
    mov     %rdx, %r12                  // r12 = input buffer length
    mov     %rcx, %r15                  // r15 = table pointer
    
    // Initialize temporary buffer on stack
    mov     %rsp, %rbx                  // rbx = temporary buffer base
    
    // Zero out the temporary buffer
    xor     %rax, %rax                  // rax = 0
    vpxor   %ymm0, %ymm0, %ymm0         // ymm0 = 0
    mov     $MLDSA_N, %rcx              // rcx = MLDSA_N
    shr     $3, %rcx                    // rcx = MLDSA_N / 8 (number of 32-byte blocks)
    
.Lzero_loop:
    vmovdqa %ymm0, (%rbx)               // Zero 32 bytes
    add     $32, %rbx                   // Advance pointer
    dec     %rcx                        // Decrement counter
    jnz     .Lzero_loop                 // Loop until done
    
    // Reset temporary buffer pointer
    mov     %rsp, %rbx                  // rbx = temporary buffer base
    
    // Initialize counters
    xor     %r8, %r8                    // r8 = count (number of coefficients sampled)
    mov     $MLDSA_N, %r9               // r9 = len (target number of coefficients)
    
    // Load constants
    mov     $8380417, %eax              // eax = q = 8380417
    vmovd   %eax, %xmm15
    vpbroadcastd %xmm15, %ymm15         // ymm15 = [q, q, q, q, q, q, q, q]
    
    // Check if we have at least 32 bytes to process
    cmp     $32, %r12
    jb      .Lloop32_end
    
.Lloop32:
    // Check if we've generated enough coefficients
    cmp     %r9, %r8
    jae     .Lmemory_copy
    
    // Process 32 bytes (up to 8 coefficients)
    // First, unpack the byte stream into 32-bit integers
    
    // Load 24 bytes (8 potential coefficients, each 3 bytes)
    cmp     $24, %r12
    jb      .Lloop32_end
    sub     $24, %r12                   // Decrease remaining buffer length
    
    // Load and unpack bytes
    vmovdqu (%r13), %ymm0               // Load 32 bytes from input buffer
    add     $24, %r13                   // Advance input buffer pointer
    
    // Prepare the shuffle mask for byte reordering
    // This is equivalent to the AArch64 ld3 instruction
    // We need to rearrange bytes to form 3-byte sequences
    vpshufb .Lshuffle_mask(%rip), %ymm0, %ymm1
    
    // Mask out top bit of the third byte in each triplet
    vpand   .Lmask_23bits(%rip), %ymm1, %ymm1
    
    // Now ymm1 contains 8 integers, each 23 bits
    // Compare with q to find valid coefficients
    vpcmpgtd %ymm1, %ymm15, %ymm2       // ymm2[i] = 0xFFFFFFFF if q > ymm1[i], 0 otherwise
    
    // Create bitmap of valid coefficients
    vpmovmskb %ymm2, %eax               // Extract sign bits to eax
    and     $0x11111111, %eax           // Keep only one bit per integer (every 4th bit)
    mov     %eax, %ecx                  // Save bitmap
    
    // Count valid coefficients using popcnt
    popcnt  %ecx, %edx                  // edx = number of valid coefficients
    
    // Load permutation table entry based on bitmap
    shl     $3, %eax                    // Multiply by 8 (each table entry is 8 bytes)
    vmovq   (%r15,%rax), %xmm3          // Load table entry
    vpmovsxbd %xmm3, %ymm3              // Sign extend bytes to dwords
    
    // Permute valid coefficients to the front
    vpermd  %ymm1, %ymm3, %ymm4         // Permute based on table
    
    // Store valid coefficients to temporary buffer
    vmovdqu %ymm4, (%rbx)               // Store to temporary buffer
    lea     (%rbx,%rdx,4), %rbx         // Advance temporary buffer pointer
    
    // Update count
    add     %rdx, %r8                   // Increase count
    
    // Check if we have enough bytes for another iteration
    cmp     $24, %r12
    jae     .Lloop32
    
.Lloop32_end:
    // Process remaining bytes (3 at a time)
    cmp     %r9, %r8                    // Check if we've generated enough coefficients
    jae     .Lmemory_copy
    
    cmp     $3, %r12                    // Check if we have at least 3 bytes left
    jb      .Lmemory_copy
    
.Lloop3:
    // Process 3 bytes (1 coefficient)
    movzbl  (%r13), %eax                // Load first byte
    movzbl  1(%r13), %ecx               // Load second byte
    movzbl  2(%r13), %edx               // Load third byte
    
    // Combine bytes into a 24-bit integer
    shl     $8, %ecx
    shl     $16, %edx
    or      %ecx, %eax
    or      %edx, %eax
    and     $0x7FFFFF, %eax             // Mask to 23 bits
    
    // Check if value is less than q
    cmp     $8380417, %eax
    jae     .Lskip_coef
    
    // Store valid coefficient
    mov     %eax, (%rbx)
    add     $4, %rbx
    inc     %r8
    
.Lskip_coef:
    add     $3, %r13                    // Advance input buffer pointer
    sub     $3, %r12                    // Decrease remaining buffer length
    
    // Check if we've generated enough coefficients or have enough bytes left
    cmp     %r9, %r8
    jae     .Lmemory_copy
    cmp     $3, %r12
    jae     .Lloop3
    
.Lmemory_copy:
    // Return count directly, like the AArch64 version
    mov     %r8, %rax                   // rax = count
    
    // Copy coefficients from stack to output buffer
    mov     %rsp, %rsi                  // rsi = temporary buffer base
    mov     %r14, %rdi                  // rdi = output buffer
    mov     $MLDSA_N, %rcx              // rcx = MLDSA_N
    
    // Use AVX2 to copy in 32-byte chunks
    shr     $3, %rcx                    // rcx = MLDSA_N / 8 (number of 32-byte blocks)
    
.Lcopy_loop:
    vmovdqa (%rsi), %ymm0               // Load 32 bytes
    vmovdqa %ymm0, (%rdi)               // Store 32 bytes
    add     $32, %rsi                   // Advance source pointer
    add     $32, %rdi                   // Advance destination pointer
    dec     %rcx                        // Decrement counter
    jnz     .Lcopy_loop                 // Loop until done
    
    // Return count is in %rax
    
    // Function epilogue
    pop     %r15
    pop     %r14
    pop     %r13
    pop     %r12
    pop     %rbx
    mov     %rbp, %rsp
    pop     %rbp
    
    // Zero out AVX registers to avoid leaking data
    vzeroupper
    
    ret

.align 32
.Lshuffle_mask:
    .byte 0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11, -1, -1, -1, -1
    .byte 12, 15, 18, 21, 13, 16, 19, 22, 14, 17, 20, 23, -1, -1, -1, -1

.align 32
.Lmask_23bits:
    .long 0x7FFFFF, 0x7FFFFF, 0x7FFFFF, 0x7FFFFF
    .long 0x7FFFFF, 0x7FFFFF, 0x7FFFFF, 0x7FFFFF

#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT && !MLD_CONFIG_MULTILEVEL_NO_SHARED */
