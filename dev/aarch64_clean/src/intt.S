/* Copyright (c) 2022 Arm Limited
 * Copyright (c) 2022 Hanno Becker
 * Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_AARCH64)

.macro mulmodq dst, src, const, idx0, idx1
        sqrdmulh t2.4s,      \src\().4s, \const\().s[\idx1\()]
        mul      \dst\().4s, \src\().4s, \const\().s[\idx0\()]
        mls      \dst\().4s, t2.4s,      modulus.s[0]
.endm

.macro mulmod dst, src, const, const_twisted
        sqrdmulh t2.4s,   \src\().4s, \const_twisted\().4s
        mul      \dst\().4s, \src\().4s, \const\().4s
        mls      \dst\().4s, t2.4s,   modulus.s[0]
.endm


.macro gs_butterfly a, b, root, idx0, idx1
        sub tmp.4s,   \a\().4s, \b\().4s
        add \a\().4s, \a\().4s, \b\().4s
        mulmodq  \b, tmp, \root, \idx0, \idx1
.endm

.macro gs_butterfly_v a, b, root, root_twisted
        sub tmp.4s,   \a\().4s, \b\().4s
        add \a\().4s, \a\().4s, \b\().4s
        mulmod  \b, tmp, \root, \root_twisted
.endm

.macro mul_ninv dst0, dst1, dst2, dst3, src0, src1, src2, src3
        mulmod \dst0, \src0, ninv, ninv_tw
        mulmod \dst1, \src1, ninv, ninv_tw
        mulmod \dst2, \src2, ninv, ninv_tw
        mulmod \dst3, \src3, ninv, ninv_tw
.endm

.macro load_roots_123
        ldr q_root0, [r123456_ptr], #64
        ldr q_root1, [r123456_ptr, #(-64 + 16)]
        ldr q_root2, [r123456_ptr, #(-64 + 32)]
        ldr q_root3, [r123456_ptr, #(-64 + 48)]
.endm

.macro load_roots_456
        ldr q_root0, [r123456_ptr], #64
        ldr q_root1, [r123456_ptr, #(-64 + 16)]
        ldr q_root2, [r123456_ptr, #(-64 + 32)]
        ldr q_root3, [r123456_ptr, #(-64 + 48)]
.endm

.macro load_roots_78_part1
        ldr q_root0,    [r78_ptr], #(12*16)
        ldr q_root0_tw, [r78_ptr, #(-12*16 + 1*16)]
        ldr q_root1,    [r78_ptr, #(-12*16 + 2*16)]
        ldr q_root1_tw, [r78_ptr, #(-12*16 + 3*16)]
        ldr q_root2,    [r78_ptr, #(-12*16 + 4*16)]
        ldr q_root2_tw, [r78_ptr, #(-12*16 + 5*16)]
.endm

.macro load_roots_78_part2
        ldr q_root0,    [r78_ptr, #(-12*16 +  6*16)]
        ldr q_root0_tw, [r78_ptr, #(-12*16 +  7*16)]
        ldr q_root1,    [r78_ptr, #(-12*16 +  8*16)]
        ldr q_root1_tw, [r78_ptr, #(-12*16 +  9*16)]
        ldr q_root2,    [r78_ptr, #(-12*16 + 10*16)]
        ldr q_root2_tw, [r78_ptr, #(-12*16 + 11*16)]
.endm

.macro transpose4 data0, data1, data2, data3
        trn1 t0.4s, \data0\().4s, \data1\().4s
        trn2 t1.4s, \data0\().4s, \data1\().4s
        trn1 t2.4s, \data2\().4s, \data3\().4s
        trn2 t3.4s, \data2\().4s, \data3\().4s

        trn2 \data2\().2d, t0.2d, t2.2d
        trn2 \data3\().2d, t1.2d, t3.2d
        trn1 \data0\().2d, t0.2d, t2.2d
        trn1 \data1\().2d, t1.2d, t3.2d
.endm

.macro save_vregs
        sub sp, sp, #(16*4)
        stp  d8,  d9, [sp, #16*0]
        stp d10, d11, [sp, #16*1]
        stp d12, d13, [sp, #16*2]
        stp d14, d15, [sp, #16*3]
.endm

.macro restore_vregs
        ldp  d8,  d9, [sp, #16*0]
        ldp d10, d11, [sp, #16*1]
        ldp d12, d13, [sp, #16*2]
        ldp d14, d15, [sp, #16*3]
        add sp, sp, #(16*4)
.endm

.macro push_stack
        save_vregs
.endm

.macro pop_stack
        restore_vregs
.endm

.text
.global MLD_ASM_NAMESPACE(intt_asm)
.balign 4
MLD_ASM_FN_SYMBOL(intt_asm)
        push_stack

        in          .req x0
        r78_ptr     .req x1
        r123456_ptr .req x2

        inp     .req x3
        inpp    .req x4
        count   .req x5
        xtmp    .req x6
        wtmp    .req w6

        data0  .req v9
        data1  .req v10
        data2  .req v11
        data3  .req v12
        data4  .req v13
        data5  .req v14
        data6  .req v15
        data7  .req v16

        q_data0  .req q9
        q_data1  .req q10
        q_data2  .req q11
        q_data3  .req q12
        q_data4  .req q13
        q_data5  .req q14
        q_data6  .req q15
        q_data7  .req q16

        root0 .req v0
        root1 .req v1
        root2 .req v2
        root3 .req v3

        q_root0 .req q0
        q_root1 .req q1
        q_root2 .req q2
        q_root3 .req q3

        tmp .req v24
        t0  .req v25
        t1  .req v26
        t2  .req v27
        t3  .req v28

        modulus .req v8
        q_modulus .req q8

        mov inp, in
        add inpp, inp, #64
        mov count, #8

        root0_tw .req v4
        root1_tw .req v5
        root2_tw .req v6
        root3_tw .req v7
        q_root0_tw .req q4
        q_root1_tw .req q5
        q_root2_tw .req q6
        q_root3_tw .req q7

        // load q = 8380417
        movz wtmp, #57345
        movk wtmp, #127, lsl #16
        dup modulus.4s, wtmp

        .p2align 2
layer45678_start:
        ld4 {data0.4S, data1.4S, data2.4S, data3.4S}, [inp]
        ld4 {data4.4S, data5.4S, data6.4S, data7.4S}, [inpp]

        load_roots_78_part1
        
        // Layer 8 Part 1
        gs_butterfly_v data0, data1, root1, root1_tw
        gs_butterfly_v data2, data3, root2, root2_tw
        // Layer 7 Part 1
        gs_butterfly_v data0, data2, root0, root0_tw
        gs_butterfly_v data1, data3, root0, root0_tw

        load_roots_78_part2

        // Layer 8 Part 2
        gs_butterfly_v data4, data5, root1, root1_tw
        gs_butterfly_v data6, data7, root2, root2_tw
        // Layer 7 Part 2
        gs_butterfly_v data4, data6, root0, root0_tw
        gs_butterfly_v data5, data7, root0, root0_tw

        transpose4 data0, data1, data2, data3
        transpose4 data4, data5, data6, data7

        load_roots_456

        // Layer 6
        gs_butterfly data0, data1, root1, 2, 3
        gs_butterfly data2, data3, root2, 0, 1
        gs_butterfly data4, data5, root2, 2, 3
        gs_butterfly data6, data7, root3, 0, 1

        // Layer 5
        gs_butterfly data0, data2, root0, 2, 3
        gs_butterfly data1, data3, root0, 2, 3
        gs_butterfly data4, data6, root1, 0, 1
        gs_butterfly data5, data7, root1, 0, 1

        // Layer 4
        gs_butterfly data0, data4, root0, 0, 1
        gs_butterfly data1, data5, root0, 0, 1
        gs_butterfly data2, data6, root0, 0, 1
        gs_butterfly data3, data7, root0, 0, 1

        // Standard way using vector instructions

        str  q_data0, [inp], #(16*4)
        str  q_data1, [inp, #(-16*4 +  1*16)]
        str  q_data2, [inp, #(-16*4 +  2*16)]
        str  q_data3, [inp, #(-16*4 +  3*16)]

        str  q_data4, [inpp], #(16*4)
        str  q_data5, [inpp, #(-16*4 +  1*16)]
        str  q_data6, [inpp, #(-16*4 +  2*16)]
        str  q_data7, [inpp, #(-16*4 +  3*16)]

        add inp, inp, #64
        add inpp, inpp, #64

        subs count, count, #1
        cbnz count, layer45678_start

        ninv             .req v25
        ninv_tw          .req v26


        mov count, #8
        

        // load ninv
        mov wtmp, #16382 // 2^(32 - 8) mod Q
        dup ninv.4s, wtmp

        // load ninv_tw = 4197891
        movz wtmp, #3587
        movk wtmp, #64, lsl #16
        dup ninv_tw.4s, wtmp

        load_roots_123

        .p2align 2
layer123_start:

        ldr q_data0, [in, #(0*(1024/8))]
        ldr q_data1, [in, #(1*(1024/8))]
        ldr q_data2, [in, #(2*(1024/8))]
        ldr q_data3, [in, #(3*(1024/8))]
        ldr q_data4, [in, #(4*(1024/8))]
        ldr q_data5, [in, #(5*(1024/8))]
        ldr q_data6, [in, #(6*(1024/8))]
        ldr q_data7, [in, #(7*(1024/8))]

        gs_butterfly data0, data1, root1, 2, 3
        gs_butterfly data2, data3, root2, 0, 1
        gs_butterfly data4, data5, root2, 2, 3
        gs_butterfly data6, data7, root3, 0, 1

        gs_butterfly data0, data2, root0, 2, 3
        gs_butterfly data1, data3, root0, 2, 3
        gs_butterfly data4, data6, root1, 0, 1
        gs_butterfly data5, data7, root1, 0, 1

        // root0[0] includes ninv, manually computed.
        gs_butterfly data0, data4, root0, 0, 1
        gs_butterfly data1, data5, root0, 0, 1
        gs_butterfly data2, data6, root0, 0, 1
        gs_butterfly data3, data7, root0, 0, 1

        str q_data4, [in, #(4*(1024/8))]
        str q_data5, [in, #(5*(1024/8))]
        str q_data6, [in, #(6*(1024/8))]
        str q_data7, [in, #(7*(1024/8))]

        // Scale half the coeffs by 1/n; for the other half, the scaling has
        // been merged into the multiplication with the twiddle factor on the
        // last layer.
        mul_ninv data0, data1, data2, data3, data0, data1, data2, data3

        str q_data0, [in], #(16)
        str q_data1, [in, #(-16 + 1*(1024/8))]
        str q_data2, [in, #(-16 + 2*(1024/8))]
        str q_data3, [in, #(-16 + 3*(1024/8))]

        subs count, count, #1
        cbnz count, layer123_start

       pop_stack
       ret
#endif
