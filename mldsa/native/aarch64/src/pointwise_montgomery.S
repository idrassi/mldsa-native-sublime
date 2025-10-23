/* Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_AARCH64)

.macro montgomery_reduce_long res, inl, inh
    uzp1   \res\().4s, \inl\().4s, \inh\().4s
    mul    \res\().4s, \res\().4s, modulus_twisted.4s
    smlal  \inl\().2d, \res\().2s, modulus.2s
    smlal2 \inh\().2d, \res\().4s, modulus.4s
    uzp2   \res\().4s, \inl\().4s, \inh\().4s
.endm

.macro pmull dl, dh, a, b
    smull  \dl\().2d, \a\().2s, \b\().2s
    smull2 \dh\().2d, \a\().4s, \b\().4s
.endm

out_ptr .req x0
a_ptr   .req x1
b_ptr   .req x2
count   .req x3
wtmp    .req w3

modulus         .req v0
modulus_twisted .req v1

.text
.global MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
.balign 4
MLD_ASM_FN_SYMBOL(poly_pointwise_montgomery_asm)
    // load q = 8380417
    movz wtmp, #57345
    movk wtmp, #127, lsl #16
    dup modulus.4s, wtmp

    // load -q^-1 = 4236238847
    movz wtmp, #57343
    movk wtmp, #64639, lsl #16
    dup modulus_twisted.4s, wtmp

    mov count, #(MLDSA_N / 4)

loop_start:
    ldr q17, [a_ptr, #1*16]
    ldr q18, [a_ptr, #2*16]
    ldr q19, [a_ptr, #3*16]
    ldr q16, [a_ptr], #4*16

    ldr q21, [b_ptr, #1*16]
    ldr q22, [b_ptr, #2*16]
    ldr q23, [b_ptr, #3*16]
    ldr q20, [b_ptr], #4*16

    pmull v24, v25, v16, v20
    pmull v26, v27, v17, v21
    pmull v28, v29, v18, v22
    pmull v30, v31, v19, v23

    montgomery_reduce_long v16, v24, v25
    montgomery_reduce_long v17, v26, v27
    montgomery_reduce_long v18, v28, v29
    montgomery_reduce_long v19, v30, v31

    str q17, [out_ptr, #1*16]
    str q18, [out_ptr, #2*16]
    str q19, [out_ptr, #3*16]
    str q16, [out_ptr], #4*16

    subs count, count, #4
    cbnz count, loop_start

    ret
#endif /* MLD_ARITH_BACKEND_AARCH64 */
