/* Copyright (c) 2022 Arm Limited
   * Copyright (c) 2022 Hanno Becker
   * Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
   * Copyright (c) The mlkem-native project authors
   * Copyright (c) The mldsa-native project authors
   * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
    */

/* References
   * ==========
   *
   * - [NeonNTT]
   * Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
   * Becker, Hwang, Kannwischer, Yang, Yang
   * https: */ /* eprint.iacr.org/2021/986
   *
   * - [SLOTHY_Paper]
   * Fast and Clean: Auditable high-performance assembly via constraint solving
   * Abdulrahman, Becker, Kannwischer, Klein
   * https: */ /* eprint.iacr.org/2022/1303
    */

/* AArch64 ML-DSA forward NTT following @[NeonNTT] and @[SLOTHY_Paper] */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_AARCH64) &&  !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/aarch64_opt/src/ntt.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLD_ASM_NAMESPACE(ntt_asm)
MLD_ASM_FN_SYMBOL(ntt_asm)

        .cfi_startproc
        sub	sp, sp, #0x40
        .cfi_adjust_cfa_offset 0x40
        stp	d8, d9, [sp]
        .cfi_rel_offset d8, 0x0
        .cfi_rel_offset d9, 0x8
        stp	d10, d11, [sp, #0x10]
        .cfi_rel_offset d10, 0x10
        .cfi_rel_offset d11, 0x18
        stp	d12, d13, [sp, #0x20]
        .cfi_rel_offset d12, 0x20
        .cfi_rel_offset d13, 0x28
        stp	d14, d15, [sp, #0x30]
        .cfi_rel_offset d14, 0x30
        .cfi_rel_offset d15, 0x38
        mov	w5, #0xe001             // =57345
        movk	w5, #0x7f, lsl #16
        dup	v7.4s, w5
        mov	x3, x0
        mov	x4, #0x8                // =8
        ldr	q0, [x1], #0x40
        ldur	q1, [x1, #-0x30]
        ldur	q2, [x1, #-0x20]
        ldur	q3, [x1, #-0x10]
        ldr	x8, [x0, #0x380]
        ldr	x5, [x0, #0x280]
        ldr	x7, [x0, #0x388]
        ldr	x6, [x0, #0x288]
        mov	v5.d[0], x8
        ldr	x11, [x0, #0x200]
        ldr	x14, [x0, #0x300]
        mov	v24.d[0], x5
        mov	v5.d[1], x7
        ldr	x12, [x0, #0x208]
        ldr	x9, [x0, #0x180]
        mov	v24.d[1], x6
        sqrdmulh	v10.4s, v5.4s, v0.s[1]
        mov	v19.d[0], x11
        mul	v27.4s, v24.4s, v0.s[0]
        ldr	x10, [x0, #0x308]
        mul	v20.4s, v5.4s, v0.s[0]
        mov	v19.d[1], x12
        sqrdmulh	v13.4s, v24.4s, v0.s[1]
        mov	v30.d[0], x14
        mul	v22.4s, v19.4s, v0.s[0]
        ldr	x8, [x0, #0x188]
        sqrdmulh	v24.4s, v19.4s, v0.s[1]
        mov	v30.d[1], x10
        mls	v20.4s, v10.4s, v7.s[0]
        mov	v23.d[0], x9
        mul	v5.4s, v30.4s, v0.s[0]
        ldr	x11, [x0, #0x80]
        sqrdmulh	v15.4s, v30.4s, v0.s[1]
        mov	v23.d[1], x8
        mls	v27.4s, v13.4s, v7.s[0]
        ldr	x16, [x0, #0x88]
        sub	v13.4s, v23.4s, v20.4s
        ldr	x13, [x0, #0x100]
        add	v8.4s, v23.4s, v20.4s
        mov	v28.d[0], x11
        mls	v5.4s, v15.4s, v7.s[0]
        ldr	x9, [x0]
        mul	v23.4s, v13.4s, v1.s[0]
        ldr	x17, [x0, #0x108]
        sqrdmulh	v30.4s, v13.4s, v1.s[1]
        mov	v28.d[1], x16
        mul	v15.4s, v8.4s, v0.s[2]
        mov	v11.d[0], x13
        sqrdmulh	v10.4s, v8.4s, v0.s[3]
        ldr	x7, [x0, #0x298]
        add	v9.4s, v28.4s, v27.4s
        mov	v11.d[1], x17
        sub	v16.4s, v28.4s, v27.4s
        mov	v28.d[0], x9
        add	v29.4s, v11.4s, v5.4s
        ldr	x14, [x0, #0x8]
        mls	v23.4s, v30.4s, v7.s[0]
        ldr	x12, [x0, #0x210]
        mls	v15.4s, v10.4s, v7.s[0]
        ldr	x15, [x0, #0x290]
        sub	v12.4s, v11.4s, v5.4s
        ldr	x16, [x0, #0x218]
        mul	v11.4s, v29.4s, v0.s[2]
        ldr	x10, [x0, #0x190]
        add	v21.4s, v16.4s, v23.4s
        ldr	x13, [x0, #0x390]
        mul	v4.4s, v12.4s, v1.s[0]
        mov	v5.d[0], x12
        sqrdmulh	v13.4s, v29.4s, v0.s[3]
        ldr	x11, [x0, #0x198]
        sqrdmulh	v31.4s, v21.4s, v2.s[3]
        mov	v5.d[1], x16
        add	v30.4s, v9.4s, v15.4s
        mov	v28.d[1], x14
        sqrdmulh	v25.4s, v5.4s, v0.s[1]
        mov	v29.d[0], x10
        sqrdmulh	v10.4s, v12.4s, v1.s[1]
        mov	v14.d[0], x15
        mul	v18.4s, v5.4s, v0.s[0]
        ldr	x8, [x0, #0x110]
        mul	v17.4s, v30.4s, v1.s[2]
        mov	v29.d[1], x11
        mls	v22.4s, v24.4s, v7.s[0]
        ldr	x6, [x0, #0x90]
        mls	v11.4s, v13.4s, v7.s[0]
        ldr	x5, [x0, #0x310]
        mul	v24.4s, v21.4s, v2.s[2]
        mov	v14.d[1], x7
        sqrdmulh	v21.4s, v30.4s, v1.s[3]
        sub	v30.4s, v9.4s, v15.4s
        mls	v4.4s, v10.4s, v7.s[0]
        ldr	x7, [x0, #0x98]
        add	v6.4s, v28.4s, v22.4s
        mls	v24.4s, v31.4s, v7.s[0]
        mov	v8.d[0], x13
        mul	v27.4s, v30.4s, v2.s[0]
        sub	v22.4s, v28.4s, v22.4s
        sub	v19.4s, v6.4s, v11.4s
        mls	v17.4s, v21.4s, v7.s[0]
        add	v10.4s, v6.4s, v11.4s
        sub	v28.4s, v22.4s, v4.4s
        add	v9.4s, v22.4s, v4.4s
        sub	v16.4s, v16.4s, v23.4s
        sub	v13.4s, v10.4s, v17.4s
        sqrdmulh	v15.4s, v14.4s, v0.s[1]
        sqrdmulh	v30.4s, v30.4s, v2.s[1]
        sqrdmulh	v12.4s, v16.4s, v3.s[1]
        add	v31.4s, v9.4s, v24.4s
        add	v21.4s, v10.4s, v17.4s
        mul	v26.4s, v14.4s, v0.s[0]
        mls	v27.4s, v30.4s, v7.s[0]
        str	q13, [x0, #0x80]
        mul	v17.4s, v16.4s, v3.s[0]
        str	q31, [x0, #0x200]
        mls	v26.4s, v15.4s, v7.s[0]
        str	q21, [x0], #0x10
        add	v5.4s, v19.4s, v27.4s
        mls	v17.4s, v12.4s, v7.s[0]
        sub	x4, x4, #0x2

Lntt_layer123_start:
        add	v30.4s, v28.4s, v17.4s
        ldr	x13, [x0, #0x388]
        str	q5, [x0, #0xf0]
        mov	v23.d[0], x6
        sub	v21.4s, v28.4s, v17.4s
        ldr	x10, [x0, #0x290]
        sub	v5.4s, v19.4s, v27.4s
        ldr	x17, [x0, #0x308]
        str	q30, [x0, #0x2f0]
        mov	v27.d[0], x8
        mls	v18.4s, v25.4s, v7.s[0]
        mov	v8.d[1], x13
        str	q21, [x0, #0x370]
        mov	v28.d[0], x5
        sqrdmulh	v21.4s, v8.4s, v0.s[1]
        mov	v23.d[1], x7
        mul	v17.4s, v8.4s, v0.s[0]
        mov	v28.d[1], x17
        add	v12.4s, v23.4s, v26.4s
        ldr	x7, [x0, #0x98]
        mul	v22.4s, v28.4s, v0.s[0]
        ldr	x13, [x0, #0x298]
        sqrdmulh	v6.4s, v28.4s, v0.s[1]
        ldr	x5, [x0]
        mls	v17.4s, v21.4s, v7.s[0]
        mov	v19.d[0], x10
        sub	v28.4s, v23.4s, v26.4s
        ldr	x14, [x0, #0x8]
        sub	v21.4s, v9.4s, v24.4s
        mov	v19.d[1], x13
        mls	v22.4s, v6.4s, v7.s[0]
        mov	v23.d[0], x5
        sqrdmulh	v4.4s, v19.4s, v0.s[1]
        ldr	x15, [x0, #0x390]
        str	q21, [x0, #0x270]
        mov	v23.d[1], x14
        sub	v30.4s, v29.4s, v17.4s
        ldr	x8, [x0, #0x110]
        sub	v15.4s, v23.4s, v18.4s
        ldr	x5, [x0, #0x210]
        add	v8.4s, v29.4s, v17.4s
        ldr	x6, [x0, #0x90]
        str	q5, [x0, #0x170]
        ldr	x9, [x0, #0x218]
        add	v9.4s, v23.4s, v18.4s
        ldr	x10, [x0, #0x190]
        sqrdmulh	v13.4s, v8.4s, v0.s[3]
        mov	v18.d[0], x5
        mul	v16.4s, v30.4s, v1.s[0]
        ldr	x13, [x0, #0x108]
        sqrdmulh	v14.4s, v30.4s, v1.s[1]
        mov	v18.d[1], x9
        mul	v17.4s, v8.4s, v0.s[2]
        mov	v29.d[0], x10
        sqrdmulh	v25.4s, v18.4s, v0.s[1]
        ldr	x5, [x0, #0x198]
        mul	v18.4s, v18.4s, v0.s[0]
        mov	v8.d[0], x15
        mls	v16.4s, v14.4s, v7.s[0]
        mov	v27.d[1], x13
        mls	v17.4s, v13.4s, v7.s[0]
        add	v23.4s, v27.4s, v22.4s
        mov	v29.d[1], x5
        mul	v26.4s, v19.4s, v0.s[0]
        add	v30.4s, v28.4s, v16.4s
        sqrdmulh	v13.4s, v23.4s, v0.s[3]
        sub	v21.4s, v28.4s, v16.4s
        mul	v11.4s, v23.4s, v0.s[2]
        ldr	x5, [x0, #0x310]
        sub	v6.4s, v12.4s, v17.4s
        sub	v10.4s, v27.4s, v22.4s
        mul	v24.4s, v30.4s, v2.s[2]
        mls	v11.4s, v13.4s, v7.s[0]
        sqrdmulh	v14.4s, v6.4s, v2.s[1]
        mul	v23.4s, v10.4s, v1.s[0]
        add	v22.4s, v12.4s, v17.4s
        sub	v19.4s, v9.4s, v11.4s
        sqrdmulh	v5.4s, v10.4s, v1.s[1]
        mul	v20.4s, v22.4s, v1.s[2]
        sqrdmulh	v13.4s, v22.4s, v1.s[3]
        mul	v27.4s, v6.4s, v2.s[0]
        mls	v23.4s, v5.4s, v7.s[0]
        mul	v17.4s, v21.4s, v3.s[0]
        mls	v20.4s, v13.4s, v7.s[0]
        add	v12.4s, v9.4s, v11.4s
        sqrdmulh	v13.4s, v30.4s, v2.s[3]
        mls	v27.4s, v14.4s, v7.s[0]
        sub	v31.4s, v12.4s, v20.4s
        add	v9.4s, v15.4s, v23.4s
        mls	v24.4s, v13.4s, v7.s[0]
        add	v30.4s, v12.4s, v20.4s
        sqrdmulh	v21.4s, v21.4s, v3.s[1]
        str	q31, [x0, #0x80]
        add	v14.4s, v9.4s, v24.4s
        sub	v28.4s, v15.4s, v23.4s
        mls	v17.4s, v21.4s, v7.s[0]
        str	q14, [x0, #0x200]
        add	v5.4s, v19.4s, v27.4s
        str	q30, [x0], #0x10
        mls	v26.4s, v4.4s, v7.s[0]
        subs	x4, x4, #0x1
        cbnz	x4, Lntt_layer123_start
        add	v21.4s, v28.4s, v17.4s
        mov	v11.d[0], x8
        mls	v18.4s, v25.4s, v7.s[0]
        mov	v25.d[0], x6
        str	q5, [x0, #0xf0]
        ldr	x8, [x0, #0x308]
        sub	v30.4s, v28.4s, v17.4s
        mov	v25.d[1], x7
        sub	v5.4s, v9.4s, v24.4s
        mov	v17.d[0], x5
        add	v22.4s, v25.4s, v26.4s
        ldr	x9, [x0, #0x388]
        sub	v23.4s, v25.4s, v26.4s
        mov	v17.d[1], x8
        sub	v13.4s, v19.4s, v27.4s
        ldr	x13, [x0]
        mul	v28.4s, v17.4s, v0.s[0]
        ldr	x4, [x0, #0x8]
        sqrdmulh	v15.4s, v17.4s, v0.s[1]
        mov	v8.d[1], x9
        str	q5, [x0, #0x270]
        mul	v19.4s, v8.4s, v0.s[0]
        mov	v25.d[0], x13
        sqrdmulh	v12.4s, v8.4s, v0.s[1]
        ldr	x5, [x0, #0x108]
        mls	v28.4s, v15.4s, v7.s[0]
        mov	v25.d[1], x4
        str	q30, [x0, #0x370]
        sub	v31.4s, v25.4s, v18.4s
        mls	v19.4s, v12.4s, v7.s[0]
        mov	v11.d[1], x5
        add	v26.4s, v25.4s, v18.4s
        add	v25.4s, v11.4s, v28.4s
        sub	v28.4s, v11.4s, v28.4s
        add	v6.4s, v29.4s, v19.4s
        mul	v9.4s, v25.4s, v0.s[2]
        sub	v19.4s, v29.4s, v19.4s
        mul	v29.4s, v6.4s, v0.s[2]
        sqrdmulh	v27.4s, v6.4s, v0.s[3]
        sqrdmulh	v10.4s, v19.4s, v1.s[1]
        mul	v14.4s, v19.4s, v1.s[0]
        str	q21, [x0, #0x2f0]
        mls	v29.4s, v27.4s, v7.s[0]
        sqrdmulh	v21.4s, v25.4s, v0.s[3]
        mls	v14.4s, v10.4s, v7.s[0]
        str	q13, [x0, #0x170]
        add	v10.4s, v22.4s, v29.4s
        sub	v25.4s, v22.4s, v29.4s
        add	v15.4s, v23.4s, v14.4s
        mul	v18.4s, v10.4s, v1.s[2]
        sqrdmulh	v20.4s, v10.4s, v1.s[3]
        mul	v19.4s, v15.4s, v2.s[2]
        sub	v17.4s, v23.4s, v14.4s
        mul	v29.4s, v28.4s, v1.s[0]
        sqrdmulh	v28.4s, v28.4s, v1.s[1]
        mls	v9.4s, v21.4s, v7.s[0]
        sqrdmulh	v27.4s, v17.4s, v3.s[1]
        sqrdmulh	v13.4s, v25.4s, v2.s[1]
        mls	v29.4s, v28.4s, v7.s[0]
        mul	v16.4s, v17.4s, v3.s[0]
        mul	v22.4s, v25.4s, v2.s[0]
        add	v24.4s, v26.4s, v9.4s
        sqrdmulh	v25.4s, v15.4s, v2.s[3]
        mls	v16.4s, v27.4s, v7.s[0]
        sub	v10.4s, v31.4s, v29.4s
        mls	v18.4s, v20.4s, v7.s[0]
        mls	v22.4s, v13.4s, v7.s[0]
        sub	v13.4s, v10.4s, v16.4s
        mls	v19.4s, v25.4s, v7.s[0]
        sub	v9.4s, v26.4s, v9.4s
        str	q13, [x0, #0x380]
        sub	v21.4s, v24.4s, v18.4s
        add	v30.4s, v24.4s, v18.4s
        add	v13.4s, v9.4s, v22.4s
        str	q21, [x0, #0x80]
        add	v5.4s, v31.4s, v29.4s
        str	q13, [x0, #0x100]
        sub	v23.4s, v9.4s, v22.4s
        str	q30, [x0], #0x10
        add	v30.4s, v10.4s, v16.4s
        str	q23, [x0, #0x170]
        add	v13.4s, v5.4s, v19.4s
        str	q30, [x0, #0x2f0]
        sub	v12.4s, v5.4s, v19.4s
        str	q13, [x0, #0x1f0]
        str	q12, [x0, #0x270]
        mov	x0, x3
        add	x6, x0, #0x40
        mov	x4, #0x8                // =8
        ldr	q13, [x1], #0x40
        ldr	x5, [x6, #0x30]
        ldr	x16, [x6, #0x10]
        ldur	q19, [x1, #-0x30]
        ldr	x7, [x6, #0x38]
        ldr	x9, [x6, #0x18]
        ldr	q6, [x2, #0x40]
        mov	v3.d[0], x5
        mov	v4.d[0], x16
        ldr	x10, [x6, #0x20]
        ldr	q23, [x2, #0x10]
        mov	v3.d[1], x7
        ldr	x3, [x6, #0x28]
        mov	v4.d[1], x9
        sqrdmulh	v31.4s, v3.4s, v13.s[1]
        ldr	x9, [x0, #0x30]
        sqrdmulh	v11.4s, v4.4s, v13.s[1]
        mov	v12.d[0], x10
        mul	v5.4s, v4.4s, v13.s[0]
        ldr	x11, [x6]
        mul	v18.4s, v3.4s, v13.s[0]
        mov	v12.d[1], x3
        ldr	q24, [x2, #0x30]
        ldr	x7, [x6, #0x8]
        mov	v29.d[0], x9
        ldr	x15, [x0, #0x38]
        mul	v16.4s, v12.4s, v13.s[0]
        mov	v15.d[0], x11
        mls	v5.4s, v11.4s, v7.s[0]
        ldr	x13, [x0, #0x20]
        mls	v18.4s, v31.4s, v7.s[0]
        mov	v15.d[1], x7
        sqrdmulh	v12.4s, v12.4s, v13.s[1]
        ldr	x8, [x0, #0x28]
        sqrdmulh	v9.4s, v15.4s, v13.s[1]
        mov	v29.d[1], x15
        mul	v27.4s, v15.4s, v13.s[0]
        ldr	x10, [x0, #0x10]
        add	v10.4s, v29.4s, v18.4s
        mov	v8.d[0], x13
        mls	v16.4s, v12.4s, v7.s[0]
        ldr	x14, [x0, #0x18]
        sub	v28.4s, v29.4s, v18.4s
        mov	v8.d[1], x8
        sqrdmulh	v17.4s, v10.4s, v13.s[3]
        ldr	x7, [x0]
        mul	v1.4s, v10.4s, v13.s[2]
        mov	v14.d[0], x10
        add	v30.4s, v8.4s, v16.4s
        ldr	x8, [x0, #0x8]
        sub	v11.4s, v8.4s, v16.4s
        mov	v14.d[1], x14
        mls	v27.4s, v9.4s, v7.s[0]
        mov	v21.d[0], x7
        add	v16.4s, v14.4s, v5.4s
        sqrdmulh	v22.4s, v30.4s, v13.s[3]
        mul	v0.4s, v11.4s, v19.s[0]
        mov	v21.d[1], x8
        sqrdmulh	v2.4s, v28.4s, v19.s[1]
        mul	v8.4s, v28.4s, v19.s[0]
        ldur	q25, [x1, #-0x20]
        sub	v5.4s, v14.4s, v5.4s
        sqrdmulh	v18.4s, v11.4s, v19.s[1]
        mls	v8.4s, v2.4s, v7.s[0]
        ldr	q26, [x2, #0x70]
        mls	v0.4s, v18.4s, v7.s[0]
        add	v11.4s, v5.4s, v8.4s
        sub	v9.4s, v5.4s, v8.4s
        sub	v4.4s, v21.4s, v27.4s
        sqrdmulh	v10.4s, v11.4s, v25.s[3]
        mul	v14.4s, v11.4s, v25.s[2]
        add	v2.4s, v4.4s, v0.4s
        ldur	q15, [x1, #-0x10]
        mls	v14.4s, v10.4s, v7.s[0]
        sub	v28.4s, v4.4s, v0.4s
        mul	v31.4s, v9.4s, v15.s[0]
        sqrdmulh	v0.4s, v9.4s, v15.s[1]
        add	v11.4s, v2.4s, v14.4s
        sub	v14.4s, v2.4s, v14.4s
        ldr	q10, [x2, #0xa0]
        trn1	v20.4s, v11.4s, v14.4s
        mls	v31.4s, v0.4s, v7.s[0]
        ldr	q4, [x2, #0xb0]
        trn2	v3.4s, v11.4s, v14.4s
        sub	x4, x4, #0x1

Lntt_layer45678_start:
        mls	v1.4s, v17.4s, v7.s[0]
        add	v5.4s, v21.4s, v27.4s
        sub	v29.4s, v28.4s, v31.4s
        add	v31.4s, v28.4s, v31.4s
        add	v9.4s, v16.4s, v1.4s
        sub	v15.4s, v16.4s, v1.4s
        trn2	v8.4s, v31.4s, v29.4s
        sqrdmulh	v27.4s, v9.4s, v19.s[3]
        mul	v12.4s, v9.4s, v19.s[2]
        ldr	q28, [x2, #0x60]
        trn2	v0.2d, v3.2d, v8.2d
        sqrdmulh	v19.4s, v15.4s, v25.s[1]
        mul	v14.4s, v0.4s, v28.4s
        sqrdmulh	v21.4s, v0.4s, v26.4s
        mul	v13.4s, v30.4s, v13.s[2]
        trn1	v11.2d, v3.2d, v8.2d
        trn1	v18.4s, v31.4s, v29.4s
        mls	v14.4s, v21.4s, v7.s[0]
        mls	v13.4s, v22.4s, v7.s[0]
        ldr	q17, [x2, #0x80]
        sub	v30.4s, v11.4s, v14.4s
        sub	v8.4s, v5.4s, v13.4s
        add	v3.4s, v5.4s, v13.4s
        mul	v13.4s, v30.4s, v10.4s
        trn2	v9.2d, v20.2d, v18.2d
        add	v29.4s, v11.4s, v14.4s
        mul	v5.4s, v9.4s, v28.4s
        sqrdmulh	v16.4s, v9.4s, v26.4s
        ldr	q21, [x2, #0x90]
        mul	v9.4s, v29.4s, v17.4s
        mls	v5.4s, v16.4s, v7.s[0]
        sqrdmulh	v28.4s, v29.4s, v21.4s
        mul	v21.4s, v15.4s, v25.s[0]
        trn1	v14.2d, v20.2d, v18.2d
        mls	v12.4s, v27.4s, v7.s[0]
        mls	v9.4s, v28.4s, v7.s[0]
        add	v26.4s, v14.4s, v5.4s
        mls	v21.4s, v19.4s, v7.s[0]
        add	v18.4s, v3.4s, v12.4s
        add	v10.4s, v26.4s, v9.4s
        sub	v16.4s, v3.4s, v12.4s
        add	v11.4s, v8.4s, v21.4s
        sub	v0.4s, v8.4s, v21.4s
        trn1	v27.4s, v18.4s, v16.4s
        trn2	v1.4s, v18.4s, v16.4s
        trn2	v16.4s, v11.4s, v0.4s
        trn1	v29.4s, v11.4s, v0.4s
        sqrdmulh	v2.4s, v30.4s, v4.4s
        trn2	v0.2d, v1.2d, v16.2d
        trn2	v18.2d, v27.2d, v29.2d
        sqrdmulh	v19.4s, v0.4s, v23.4s
        sqrdmulh	v4.4s, v18.4s, v23.4s
        ldr	q21, [x2], #0xc0
        ldur	q25, [x2, #-0x70]
        mul	v15.4s, v0.4s, v21.4s
        mul	v31.4s, v18.4s, v21.4s
        mls	v13.4s, v2.4s, v7.s[0]
        sub	v0.4s, v14.4s, v5.4s
        trn1	v3.2d, v1.2d, v16.2d
        mls	v15.4s, v19.4s, v7.s[0]
        mls	v31.4s, v4.4s, v7.s[0]
        sub	v11.4s, v26.4s, v9.4s
        trn1	v30.2d, v27.2d, v29.2d
        add	v27.4s, v3.4s, v15.4s
        sub	v29.4s, v3.4s, v15.4s
        add	v12.4s, v0.4s, v13.4s
        sqrdmulh	v3.4s, v27.4s, v24.4s
        mul	v16.4s, v29.4s, v6.4s
        sqrdmulh	v8.4s, v29.4s, v25.4s
        sub	v13.4s, v0.4s, v13.4s
        ldur	q15, [x2, #-0xa0]
        st4	{ v10.4s, v11.4s, v12.4s, v13.4s }, [x6], #64
        mul	v24.4s, v27.4s, v15.4s
        add	x6, x6, #0x40
        mls	v16.4s, v8.4s, v7.s[0]
        ldr	x9, [x6, #0x30]
        sub	v20.4s, v30.4s, v31.4s
        ldr	x8, [x6, #0x38]
        add	v31.4s, v30.4s, v31.4s
        ldr	x15, [x6, #0x20]
        mls	v24.4s, v3.4s, v7.s[0]
        ldr	x5, [x6, #0x10]
        add	v17.4s, v20.4s, v16.4s
        mov	v4.d[0], x9
        sub	v18.4s, v20.4s, v16.4s
        ldr	x13, [x6, #0x28]
        ldr	q13, [x1], #0x40
        mov	v4.d[1], x8
        mov	v30.d[0], x5
        ldr	x17, [x6, #0x18]
        sub	v16.4s, v31.4s, v24.4s
        mov	v14.d[0], x15
        add	v15.4s, v31.4s, v24.4s
        ldr	x7, [x6]
        ldur	q19, [x1, #-0x30]
        mov	v14.d[1], x13
        mov	v30.d[1], x17
        ldr	x3, [x6, #0x8]
        st4	{ v15.4s, v16.4s, v17.4s, v18.4s }, [x0], #64
        sqrdmulh	v2.4s, v30.4s, v13.s[1]
        mov	v18.d[0], x7
        mul	v1.4s, v4.4s, v13.s[0]
        add	x0, x0, #0x40
        sqrdmulh	v9.4s, v4.4s, v13.s[1]
        mov	v18.d[1], x3
        ldur	q25, [x1, #-0x20]
        ldr	x5, [x0, #0x30]
        ldr	x9, [x0, #0x38]
        mul	v27.4s, v18.4s, v13.s[0]
        ldr	x7, [x0, #0x10]
        mls	v1.4s, v9.4s, v7.s[0]
        ldr	x15, [x0, #0x20]
        mul	v10.4s, v14.4s, v13.s[0]
        mov	v28.d[0], x5
        sqrdmulh	v23.4s, v14.4s, v13.s[1]
        ldr	x3, [x0, #0x18]
        mul	v14.4s, v30.4s, v13.s[0]
        mov	v28.d[1], x9
        sqrdmulh	v22.4s, v18.4s, v13.s[1]
        ldr	x17, [x0, #0x28]
        sub	v6.4s, v28.4s, v1.4s
        mov	v26.d[0], x15
        mls	v10.4s, v23.4s, v7.s[0]
        ldr	x9, [x0, #0x8]
        mls	v14.4s, v2.4s, v7.s[0]
        mov	v4.d[0], x7
        mul	v24.4s, v6.4s, v19.s[0]
        ldr	x8, [x0]
        sqrdmulh	v0.4s, v6.4s, v19.s[1]
        mov	v26.d[1], x17
        mls	v27.4s, v22.4s, v7.s[0]
        mov	v4.d[1], x3
        sub	v30.4s, v26.4s, v10.4s
        sub	v11.4s, v4.4s, v14.4s
        mov	v21.d[0], x8
        mls	v24.4s, v0.4s, v7.s[0]
        mul	v18.4s, v30.4s, v19.s[0]
        mov	v21.d[1], x9
        sqrdmulh	v6.4s, v30.4s, v19.s[1]
        sub	v5.4s, v21.4s, v27.4s
        add	v3.4s, v11.4s, v24.4s
        ldur	q15, [x1, #-0x10]
        mul	v9.4s, v3.4s, v25.s[2]
        sqrdmulh	v3.4s, v3.4s, v25.s[3]
        mls	v18.4s, v6.4s, v7.s[0]
        sub	v30.4s, v11.4s, v24.4s
        add	v16.4s, v4.4s, v14.4s
        mls	v9.4s, v3.4s, v7.s[0]
        add	v0.4s, v5.4s, v18.4s
        mul	v31.4s, v30.4s, v15.s[0]
        add	v6.4s, v28.4s, v1.4s
        sub	v17.4s, v0.4s, v9.4s
        sqrdmulh	v8.4s, v30.4s, v15.s[1]
        add	v20.4s, v0.4s, v9.4s
        add	v30.4s, v26.4s, v10.4s
        ldr	q10, [x2, #0xa0]
        mul	v1.4s, v6.4s, v13.s[2]
        trn2	v3.4s, v20.4s, v17.4s
        sub	v28.4s, v5.4s, v18.4s
        sqrdmulh	v22.4s, v30.4s, v13.s[3]
        mls	v31.4s, v8.4s, v7.s[0]
        trn1	v20.4s, v20.4s, v17.4s
        sqrdmulh	v17.4s, v6.4s, v13.s[3]
        ldr	q4, [x2, #0xb0]
        ldr	q26, [x2, #0x70]
        ldr	q23, [x2, #0x10]
        ldr	q24, [x2, #0x30]
        ldr	q6, [x2, #0x40]
        subs	x4, x4, #0x1
        cbnz	x4, Lntt_layer45678_start
        sub	v2.4s, v28.4s, v31.4s
        add	v8.4s, v28.4s, v31.4s
        ldr	q0, [x2, #0x60]
        trn2	v18.4s, v8.4s, v2.4s
        ldr	q14, [x2, #0x80]
        trn2	v9.2d, v3.2d, v18.2d
        trn1	v29.4s, v8.4s, v2.4s
        mul	v11.4s, v9.4s, v0.4s
        sqrdmulh	v28.4s, v9.4s, v26.4s
        trn2	v9.2d, v20.2d, v29.2d
        trn1	v2.2d, v3.2d, v18.2d
        mul	v12.4s, v9.4s, v0.4s
        mls	v11.4s, v28.4s, v7.s[0]
        sqrdmulh	v0.4s, v9.4s, v26.4s
        ldr	q5, [x2, #0x90]
        add	v15.4s, v2.4s, v11.4s
        sub	v18.4s, v2.4s, v11.4s
        mls	v12.4s, v0.4s, v7.s[0]
        sqrdmulh	v3.4s, v15.4s, v5.4s
        mul	v31.4s, v15.4s, v14.4s
        mul	v11.4s, v18.4s, v10.4s
        sqrdmulh	v14.4s, v18.4s, v4.4s
        trn1	v8.2d, v20.2d, v29.2d
        mls	v31.4s, v3.4s, v7.s[0]
        add	v15.4s, v8.4s, v12.4s
        mls	v11.4s, v14.4s, v7.s[0]
        sub	v0.4s, v8.4s, v12.4s
        mls	v1.4s, v17.4s, v7.s[0]
        add	v20.4s, v21.4s, v27.4s
        mul	v13.4s, v30.4s, v13.s[2]
        sub	v18.4s, v0.4s, v11.4s
        add	v14.4s, v16.4s, v1.4s
        sub	v10.4s, v16.4s, v1.4s
        mls	v13.4s, v22.4s, v7.s[0]
        sqrdmulh	v8.4s, v14.4s, v19.s[3]
        mul	v9.4s, v14.4s, v19.s[2]
        sqrdmulh	v3.4s, v10.4s, v25.s[1]
        mul	v10.4s, v10.4s, v25.s[0]
        add	v12.4s, v20.4s, v13.4s
        mls	v9.4s, v8.4s, v7.s[0]
        sub	v26.4s, v20.4s, v13.4s
        mls	v10.4s, v3.4s, v7.s[0]
        sub	v16.4s, v15.4s, v31.4s
        sub	v8.4s, v12.4s, v9.4s
        add	v12.4s, v12.4s, v9.4s
        sub	v2.4s, v26.4s, v10.4s
        add	v9.4s, v26.4s, v10.4s
        trn2	v26.4s, v12.4s, v8.4s
        trn1	v20.4s, v12.4s, v8.4s
        trn2	v25.4s, v9.4s, v2.4s
        ldr	q4, [x2], #0xc0
        trn2	v1.2d, v26.2d, v25.2d
        trn1	v8.2d, v26.2d, v25.2d
        mul	v13.4s, v1.4s, v4.4s
        sqrdmulh	v10.4s, v1.4s, v23.4s
        add	v15.4s, v15.4s, v31.4s
        ldur	q29, [x2, #-0xa0]
        mls	v13.4s, v10.4s, v7.s[0]
        trn1	v12.4s, v9.4s, v2.4s
        ldur	q3, [x2, #-0x70]
        add	v17.4s, v8.4s, v13.4s
        trn1	v21.2d, v20.2d, v12.2d
        trn2	v10.2d, v20.2d, v12.2d
        sub	v14.4s, v8.4s, v13.4s
        mul	v28.4s, v10.4s, v4.4s
        sqrdmulh	v13.4s, v10.4s, v23.4s
        sqrdmulh	v12.4s, v17.4s, v24.4s
        mul	v10.4s, v14.4s, v6.4s
        sqrdmulh	v27.4s, v14.4s, v3.4s
        mls	v28.4s, v13.4s, v7.s[0]
        mul	v13.4s, v17.4s, v29.4s
        add	v17.4s, v0.4s, v11.4s
        mls	v10.4s, v27.4s, v7.s[0]
        sub	v20.4s, v21.4s, v28.4s
        mls	v13.4s, v12.4s, v7.s[0]
        add	v23.4s, v21.4s, v28.4s
        sub	v12.4s, v20.4s, v10.4s
        add	v11.4s, v20.4s, v10.4s
        sub	v10.4s, v23.4s, v13.4s
        add	v9.4s, v23.4s, v13.4s
        st4	{ v15.4s, v16.4s, v17.4s, v18.4s }, [x6], #64
        st4	{ v9.4s, v10.4s, v11.4s, v12.4s }, [x0], #64
        add	x0, x0, #0x40
        add	x6, x6, #0x40
        ldp	d8, d9, [sp]
        .cfi_restore d8
        .cfi_restore d9
        ldp	d10, d11, [sp, #0x10]
        .cfi_restore d10
        .cfi_restore d11
        ldp	d12, d13, [sp, #0x20]
        .cfi_restore d12
        .cfi_restore d13
        ldp	d14, d15, [sp, #0x30]
        .cfi_restore d14
        .cfi_restore d15
        add	sp, sp, #0x40
        .cfi_adjust_cfa_offset -0x40
        ret
        .cfi_endproc

#endif /* MLD_ARITH_BACKEND_AARCH64 && !MLD_CONFIG_MULTILEVEL_NO_SHARED */
