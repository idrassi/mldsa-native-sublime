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
 *   Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
 *   Becker, Hwang, Kannwischer, Yang, Yang
 *   https://eprint.iacr.org/2021/986
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
        ldr	q20, [x0, #0x390]
        ldr	q21, [x0, #0x380]
        mul	v30.4s, v20.4s, v0.s[0]
        sqrdmulh	v18.4s, v20.4s, v0.s[1]
        sqrdmulh	v14.4s, v21.4s, v0.s[1]
        mul	v4.4s, v21.4s, v0.s[0]
        ldr	q29, [x0, #0x280]
        ldr	q6, [x0, #0x180]
        mls	v4.4s, v14.4s, v7.s[0]
        ldr	q12, [x0, #0x300]
        sqrdmulh	v25.4s, v29.4s, v0.s[1]
        mul	v21.4s, v29.4s, v0.s[0]
        sqrdmulh	v11.4s, v12.4s, v0.s[1]
        add	v8.4s, v6.4s, v4.4s
        sub	v27.4s, v6.4s, v4.4s
        mls	v21.4s, v25.4s, v7.s[0]
        ldr	q15, [x0, #0x80]
        mul	v17.4s, v12.4s, v0.s[0]
        mls	v30.4s, v18.4s, v7.s[0]
        add	v19.4s, v15.4s, v21.4s
        sub	v20.4s, v15.4s, v21.4s
        mls	v17.4s, v11.4s, v7.s[0]
        ldr	q13, [x0, #0x100]
        ldr	q22, [x0, #0x200]
        ldr	q26, [x0, #0x290]
        mul	v18.4s, v8.4s, v0.s[2]
        ldr	q24, [x0, #0x310]
        sqrdmulh	v11.4s, v8.4s, v0.s[3]
        mul	v12.4s, v26.4s, v0.s[0]
        mul	v5.4s, v27.4s, v1.s[0]
        sqrdmulh	v21.4s, v27.4s, v1.s[1]
        ldr	q28, [x0, #0x190]
        mul	v6.4s, v22.4s, v0.s[0]
        sqrdmulh	v23.4s, v22.4s, v0.s[1]
        add	v22.4s, v28.4s, v30.4s
        sub	v30.4s, v28.4s, v30.4s
        sqrdmulh	v9.4s, v26.4s, v0.s[1]
        sqrdmulh	v29.4s, v24.4s, v0.s[1]
        mul	v27.4s, v24.4s, v0.s[0]
        mls	v18.4s, v11.4s, v7.s[0]
        sqrdmulh	v24.4s, v22.4s, v0.s[3]
        mls	v5.4s, v21.4s, v7.s[0]
        mls	v6.4s, v23.4s, v7.s[0]
        mls	v12.4s, v9.4s, v7.s[0]
        sub	v10.4s, v19.4s, v18.4s
        add	v21.4s, v20.4s, v5.4s
        sub	v28.4s, v20.4s, v5.4s
        sub	v16.4s, v13.4s, v17.4s
        add	v20.4s, v13.4s, v17.4s
        add	v19.4s, v19.4s, v18.4s
        mul	v11.4s, v22.4s, v0.s[2]
        ldr	q31, [x0, #0x90]
        mul	v13.4s, v30.4s, v1.s[0]
        mls	v11.4s, v24.4s, v7.s[0]
        add	v8.4s, v31.4s, v12.4s
        ldr	q23, [x0, #0x210]
        mls	v27.4s, v29.4s, v7.s[0]
        ldr	q24, [x0, #0x110]
        add	v29.4s, v8.4s, v11.4s
        sqrdmulh	v9.4s, v30.4s, v1.s[1]
        add	v15.4s, v24.4s, v27.4s
        mul	v17.4s, v20.4s, v0.s[2]
        sqrdmulh	v22.4s, v20.4s, v0.s[3]
        sub	v5.4s, v24.4s, v27.4s
        mul	v20.4s, v23.4s, v0.s[0]
        sqrdmulh	v24.4s, v29.4s, v1.s[3]
        sqrdmulh	v26.4s, v23.4s, v0.s[1]
        mls	v13.4s, v9.4s, v7.s[0]
        sqrdmulh	v14.4s, v16.4s, v1.s[1]
        mul	v27.4s, v29.4s, v1.s[2]
        mul	v16.4s, v16.4s, v1.s[0]
        ldr	q25, [x0]
        mls	v27.4s, v24.4s, v7.s[0]
        sqrdmulh	v29.4s, v15.4s, v0.s[3]
        mul	v4.4s, v15.4s, v0.s[2]
        sqrdmulh	v30.4s, v19.4s, v1.s[3]
        mls	v17.4s, v22.4s, v7.s[0]
        mls	v20.4s, v26.4s, v7.s[0]
        ldr	q26, [x0, #0x10]
        mls	v4.4s, v29.4s, v7.s[0]
        add	v24.4s, v25.4s, v6.4s
        mul	v23.4s, v5.4s, v1.s[0]
        mls	v16.4s, v14.4s, v7.s[0]
        sqrdmulh	v29.4s, v21.4s, v2.s[3]
        mul	v15.4s, v21.4s, v2.s[2]
        mul	v9.4s, v19.4s, v1.s[2]
        mul	v19.4s, v10.4s, v2.s[0]
        sub	v31.4s, v31.4s, v12.4s
        sqrdmulh	v10.4s, v10.4s, v2.s[1]
        sqrdmulh	v12.4s, v28.4s, v3.s[1]
        sub	v6.4s, v25.4s, v6.4s
        mul	v14.4s, v28.4s, v3.s[0]
        add	v18.4s, v31.4s, v13.4s
        mls	v9.4s, v30.4s, v7.s[0]
        sqrdmulh	v22.4s, v5.4s, v1.s[1]
        add	v25.4s, v24.4s, v17.4s
        mul	v30.4s, v18.4s, v2.s[2]
        add	v5.4s, v26.4s, v20.4s
        sqrdmulh	v18.4s, v18.4s, v2.s[3]
        mls	v23.4s, v22.4s, v7.s[0]
        sub	v28.4s, v26.4s, v20.4s
        mls	v19.4s, v10.4s, v7.s[0]
        mls	v14.4s, v12.4s, v7.s[0]
        sub	v12.4s, v25.4s, v9.4s
        add	v26.4s, v28.4s, v23.4s
        add	v10.4s, v6.4s, v16.4s
        sub	v21.4s, v24.4s, v17.4s
        mls	v15.4s, v29.4s, v7.s[0]
        sub	v29.4s, v6.4s, v16.4s
        mls	v30.4s, v18.4s, v7.s[0]
        add	v20.4s, v25.4s, v9.4s
        add	v24.4s, v5.4s, v4.4s
        sub	v6.4s, v10.4s, v15.4s
        str	q20, [x0], #0x10
        sub	v20.4s, v5.4s, v4.4s
        sub	v4.4s, v31.4s, v13.4s
        sub	v17.4s, v8.4s, v11.4s
        add	v31.4s, v21.4s, v19.4s
        add	v9.4s, v24.4s, v27.4s
        add	v22.4s, v10.4s, v15.4s
        sub	v13.4s, v26.4s, v30.4s
        str	q9, [x0], #0x10
        sub	v11.4s, v29.4s, v14.4s
        str	q31, [x0, #0xe0]
        sub	v15.4s, v24.4s, v27.4s
        str	q6, [x0, #0x260]
        sqrdmulh	v6.4s, v17.4s, v2.s[1]
        sub	v27.4s, v21.4s, v19.4s
        str	q11, [x0, #0x360]
        sqrdmulh	v10.4s, v4.4s, v3.s[1]
        str	q12, [x0, #0x60]
        add	v5.4s, v26.4s, v30.4s
        str	q22, [x0, #0x1e0]
        sub	x4, x4, #0x2

Lntt_layer123_start:
        str	q27, [x0, #0x160]
        add	v21.4s, v29.4s, v14.4s
        sub	v29.4s, v28.4s, v23.4s
        ldr	q18, [x0, #0x100]
        ldr	q28, [x0, #0x300]
        ldr	q27, [x0, #0x200]
        sqrdmulh	v8.4s, v28.4s, v0.s[1]
        mul	v23.4s, v28.4s, v0.s[0]
        mul	v26.4s, v27.4s, v0.s[0]
        sqrdmulh	v22.4s, v27.4s, v0.s[1]
        mul	v14.4s, v4.4s, v3.s[0]
        mls	v23.4s, v8.4s, v7.s[0]
        ldr	q27, [x0, #0x380]
        mls	v26.4s, v22.4s, v7.s[0]
        add	v19.4s, v18.4s, v23.4s
        sub	v12.4s, v18.4s, v23.4s
        sqrdmulh	v30.4s, v27.4s, v0.s[1]
        mul	v8.4s, v27.4s, v0.s[0]
        ldr	q11, [x0, #0x280]
        ldr	q31, [x0, #0x180]
        mls	v14.4s, v10.4s, v7.s[0]
        mls	v8.4s, v30.4s, v7.s[0]
        mul	v18.4s, v11.4s, v0.s[0]
        sqrdmulh	v25.4s, v11.4s, v0.s[1]
        ldr	q22, [x0, #0x80]
        sub	v24.4s, v31.4s, v8.4s
        mls	v18.4s, v25.4s, v7.s[0]
        ldr	q4, [x0]
        sqrdmulh	v10.4s, v19.4s, v0.s[3]
        mul	v11.4s, v19.4s, v0.s[2]
        add	v9.4s, v4.4s, v26.4s
        sub	v28.4s, v4.4s, v26.4s
        sqrdmulh	v16.4s, v12.4s, v1.s[1]
        mul	v23.4s, v12.4s, v1.s[0]
        sqrdmulh	v27.4s, v24.4s, v1.s[1]
        add	v4.4s, v31.4s, v8.4s
        mul	v8.4s, v24.4s, v1.s[0]
        sub	v12.4s, v22.4s, v18.4s
        mls	v23.4s, v16.4s, v7.s[0]
        str	q21, [x0, #0x2e0]
        mul	v26.4s, v17.4s, v2.s[0]
        sqrdmulh	v17.4s, v4.4s, v0.s[3]
        mul	v16.4s, v4.4s, v0.s[2]
        mls	v8.4s, v27.4s, v7.s[0]
        mls	v26.4s, v6.4s, v7.s[0]
        add	v24.4s, v22.4s, v18.4s
        mls	v16.4s, v17.4s, v7.s[0]
        mls	v11.4s, v10.4s, v7.s[0]
        sub	v27.4s, v20.4s, v26.4s
        sub	v4.4s, v12.4s, v8.4s
        sub	v17.4s, v24.4s, v16.4s
        sub	v30.4s, v29.4s, v14.4s
        sqrdmulh	v10.4s, v4.4s, v3.s[1]
        add	v22.4s, v20.4s, v26.4s
        sqrdmulh	v6.4s, v17.4s, v2.s[1]
        add	v26.4s, v28.4s, v23.4s
        add	v19.4s, v12.4s, v8.4s
        sub	v20.4s, v9.4s, v11.4s
        str	q15, [x0, #0x70]
        add	v25.4s, v24.4s, v16.4s
        add	v15.4s, v9.4s, v11.4s
        mul	v16.4s, v19.4s, v2.s[2]
        mul	v18.4s, v25.4s, v1.s[2]
        sqrdmulh	v31.4s, v25.4s, v1.s[3]
        str	q5, [x0, #0x1f0]
        sqrdmulh	v8.4s, v19.4s, v2.s[3]
        str	q22, [x0, #0xf0]
        mls	v18.4s, v31.4s, v7.s[0]
        str	q13, [x0, #0x270]
        mls	v16.4s, v8.4s, v7.s[0]
        str	q30, [x0, #0x370]
        add	v5.4s, v15.4s, v18.4s
        sub	v15.4s, v15.4s, v18.4s
        sub	v13.4s, v26.4s, v16.4s
        str	q5, [x0], #0x10
        add	v5.4s, v26.4s, v16.4s
        subs	x4, x4, #0x1
        cbnz	x4, Lntt_layer123_start
        mul	v8.4s, v17.4s, v2.s[0]
        str	q13, [x0, #0x270]
        mul	v4.4s, v4.4s, v3.s[0]
        str	q5, [x0, #0x1f0]
        mls	v8.4s, v6.4s, v7.s[0]
        str	q27, [x0, #0x160]
        sub	v13.4s, v28.4s, v23.4s
        str	q15, [x0, #0x70]
        add	v18.4s, v29.4s, v14.4s
        mls	v4.4s, v10.4s, v7.s[0]
        add	v5.4s, v20.4s, v8.4s
        str	q18, [x0, #0x2e0]
        sub	v8.4s, v20.4s, v8.4s
        str	q5, [x0, #0xf0]
        sub	v17.4s, v13.4s, v4.4s
        str	q8, [x0, #0x170]
        add	v18.4s, v13.4s, v4.4s
        str	q17, [x0, #0x370]
        str	q18, [x0, #0x2f0]
        mov	x0, x3
        mov	x4, #0x8                // =8
        ldr	q4, [x0, #0x70]
        ldr	q26, [x1], #0x40
        ldr	q21, [x0, #0x60]
        mul	v13.4s, v4.4s, v26.s[0]
        sqrdmulh	v31.4s, v4.4s, v26.s[1]
        mul	v2.4s, v21.4s, v26.s[0]
        sqrdmulh	v24.4s, v21.4s, v26.s[1]
        ldr	q1, [x0, #0x30]
        mls	v13.4s, v31.4s, v7.s[0]
        mls	v2.4s, v24.4s, v7.s[0]
        ldr	q12, [x0, #0x20]
        ldr	q21, [x0, #0x50]
        ldr	q23, [x0, #0x40]
        add	v15.4s, v1.4s, v13.4s
        add	v5.4s, v12.4s, v2.4s
        sqrdmulh	v28.4s, v23.4s, v26.s[1]
        mul	v16.4s, v15.4s, v26.s[2]
        sqrdmulh	v6.4s, v5.4s, v26.s[3]
        mul	v3.4s, v5.4s, v26.s[2]
        sqrdmulh	v31.4s, v15.4s, v26.s[3]
        mul	v29.4s, v21.4s, v26.s[0]
        sqrdmulh	v14.4s, v21.4s, v26.s[1]
        mul	v23.4s, v23.4s, v26.s[0]
        sub	v24.4s, v1.4s, v13.4s
        sub	v13.4s, v12.4s, v2.4s
        mls	v29.4s, v14.4s, v7.s[0]
        ldr	q9, [x0, #0x10]
        ldur	q18, [x1, #-0x30]
        mls	v23.4s, v28.4s, v7.s[0]
        ldr	q15, [x0]
        mls	v16.4s, v31.4s, v7.s[0]
        ldur	q31, [x1, #-0x20]
        add	v11.4s, v9.4s, v29.4s
        sqrdmulh	v22.4s, v24.4s, v18.s[1]
        mul	v4.4s, v24.4s, v18.s[0]
        add	v1.4s, v11.4s, v16.4s
        sub	v2.4s, v11.4s, v16.4s
        mls	v3.4s, v6.4s, v7.s[0]
        mls	v4.4s, v22.4s, v7.s[0]
        sub	v17.4s, v9.4s, v29.4s
        mul	v20.4s, v1.4s, v18.s[2]
        sqrdmulh	v6.4s, v1.4s, v18.s[3]
        mul	v22.4s, v2.4s, v31.s[0]
        sqrdmulh	v30.4s, v2.4s, v31.s[1]
        add	v0.4s, v15.4s, v23.4s
        mul	v16.4s, v13.4s, v18.s[0]
        sqrdmulh	v13.4s, v13.4s, v18.s[1]
        ldur	q24, [x1, #-0x10]
        sub	v10.4s, v17.4s, v4.4s
        add	v18.4s, v17.4s, v4.4s
        mls	v22.4s, v30.4s, v7.s[0]
        mls	v20.4s, v6.4s, v7.s[0]
        sub	v30.4s, v0.4s, v3.4s
        add	v26.4s, v0.4s, v3.4s
        mls	v16.4s, v13.4s, v7.s[0]
        add	v12.4s, v30.4s, v22.4s
        sub	v5.4s, v30.4s, v22.4s
        mul	v8.4s, v18.4s, v31.s[2]
        sqrdmulh	v22.4s, v18.4s, v31.s[3]
        sqrdmulh	v28.4s, v10.4s, v24.s[1]
        mul	v24.4s, v10.4s, v24.s[0]
        sub	v31.4s, v15.4s, v23.4s
        add	v29.4s, v26.4s, v20.4s
        sub	v4.4s, v26.4s, v20.4s
        add	v23.4s, v31.4s, v16.4s
        sub	v15.4s, v31.4s, v16.4s
        trn1	v13.4s, v12.4s, v5.4s
        trn2	v1.4s, v12.4s, v5.4s
        mls	v8.4s, v22.4s, v7.s[0]
        mls	v24.4s, v28.4s, v7.s[0]
        trn1	v5.4s, v29.4s, v4.4s
        trn2	v6.4s, v29.4s, v4.4s
        add	v25.4s, v23.4s, v8.4s
        sub	v19.4s, v23.4s, v8.4s
        add	v20.4s, v15.4s, v24.4s
        sub	v4.4s, v15.4s, v24.4s
        trn2	v10.4s, v25.4s, v19.4s
        trn1	v29.2d, v5.2d, v13.2d
        trn2	v22.2d, v5.2d, v13.2d
        trn1	v17.2d, v6.2d, v1.2d
        trn2	v23.2d, v6.2d, v1.2d
        trn2	v24.4s, v20.4s, v4.4s
        sub	x4, x4, #0x1

Lntt_layer45678_start:
        trn1	v26.4s, v20.4s, v4.4s
        trn1	v13.2d, v10.2d, v24.2d
        trn2	v8.2d, v10.2d, v24.2d
        trn1	v1.4s, v25.4s, v19.4s
        ldr	q21, [x2], #0xc0
        ldur	q18, [x2, #-0xb0]
        mul	v24.4s, v22.4s, v21.4s
        mul	v20.4s, v23.4s, v21.4s
        sqrdmulh	v0.4s, v23.4s, v18.4s
        sqrdmulh	v27.4s, v22.4s, v18.4s
        trn2	v10.2d, v1.2d, v26.2d
        trn1	v19.2d, v1.2d, v26.2d
        mls	v20.4s, v0.4s, v7.s[0]
        mls	v24.4s, v27.4s, v7.s[0]
        ldur	q4, [x2, #-0x60]
        sub	v18.4s, v17.4s, v20.4s
        add	v0.4s, v17.4s, v20.4s
        add	v14.4s, v29.4s, v24.4s
        sub	v17.4s, v29.4s, v24.4s
        ldur	q2, [x2, #-0x50]
        mul	v31.4s, v8.4s, v4.4s
        mul	v1.4s, v10.4s, v4.4s
        sqrdmulh	v4.4s, v8.4s, v2.4s
        sqrdmulh	v22.4s, v10.4s, v2.4s
        ldr	q3, [x1], #0x40
        mls	v31.4s, v4.4s, v7.s[0]
        mls	v1.4s, v22.4s, v7.s[0]
        ldr	q16, [x0, #0xf0]
        sub	v9.4s, v13.4s, v31.4s
        add	v30.4s, v13.4s, v31.4s
        sub	v10.4s, v19.4s, v1.4s
        add	v6.4s, v19.4s, v1.4s
        ldur	q24, [x2, #-0x80]
        ldur	q13, [x2, #-0x70]
        mul	v2.4s, v18.4s, v24.4s
        sqrdmulh	v23.4s, v16.4s, v3.s[1]
        sqrdmulh	v12.4s, v18.4s, v13.4s
        ldur	q20, [x2, #-0xa0]
        ldur	q1, [x2, #-0x90]
        mls	v2.4s, v12.4s, v7.s[0]
        mul	v15.4s, v0.4s, v20.4s
        sqrdmulh	v31.4s, v0.4s, v1.4s
        mul	v25.4s, v16.4s, v3.s[0]
        add	v0.4s, v17.4s, v2.4s
        sub	v17.4s, v17.4s, v2.4s
        mls	v15.4s, v31.4s, v7.s[0]
        ldr	q16, [x0, #0xe0]
        mls	v25.4s, v23.4s, v7.s[0]
        add	v23.4s, v14.4s, v15.4s
        sub	v27.4s, v14.4s, v15.4s
        mul	v12.4s, v16.4s, v3.s[0]
        sqrdmulh	v15.4s, v16.4s, v3.s[1]
        ldr	q29, [x0, #0xa0]
        ldr	q21, [x0, #0xb0]
        mls	v12.4s, v15.4s, v7.s[0]
        trn1	v8.4s, v0.4s, v17.4s
        trn2	v16.4s, v0.4s, v17.4s
        trn1	v24.4s, v23.4s, v27.4s
        trn2	v14.4s, v23.4s, v27.4s
        sub	v15.4s, v21.4s, v25.4s
        add	v25.4s, v21.4s, v25.4s
        add	v0.4s, v29.4s, v12.4s
        sub	v4.4s, v29.4s, v12.4s
        ldur	q28, [x2, #-0x30]
        ldur	q18, [x2, #-0x40]
        sqrdmulh	v31.4s, v30.4s, v28.4s
        mul	v21.4s, v25.4s, v3.s[2]
        mul	v27.4s, v30.4s, v18.4s
        sqrdmulh	v2.4s, v25.4s, v3.s[3]
        ldur	q26, [x2, #-0x20]
        mls	v27.4s, v31.4s, v7.s[0]
        ldur	q5, [x2, #-0x10]
        mul	v12.4s, v9.4s, v26.4s
        sub	v29.4s, v6.4s, v27.4s
        add	v27.4s, v6.4s, v27.4s
        sqrdmulh	v20.4s, v9.4s, v5.4s
        mul	v26.4s, v0.4s, v3.s[2]
        sqrdmulh	v23.4s, v0.4s, v3.s[3]
        ldr	q18, [x0, #0xd0]
        ldr	q13, [x0, #0xc0]
        mul	v17.4s, v18.4s, v3.s[0]
        sqrdmulh	v19.4s, v18.4s, v3.s[1]
        sqrdmulh	v6.4s, v13.4s, v3.s[1]
        mul	v18.4s, v13.4s, v3.s[0]
        mls	v12.4s, v20.4s, v7.s[0]
        trn1	v3.2d, v24.2d, v8.2d
        trn2	v13.2d, v24.2d, v8.2d
        trn2	v9.2d, v14.2d, v16.2d
        add	v31.4s, v10.4s, v12.4s
        sub	v11.4s, v10.4s, v12.4s
        trn1	v28.2d, v14.2d, v16.2d
        ldur	q20, [x1, #-0x30]
        mls	v21.4s, v2.4s, v7.s[0]
        trn1	v25.4s, v27.4s, v29.4s
        sqrdmulh	v2.4s, v15.4s, v20.s[1]
        mul	v14.4s, v15.4s, v20.s[0]
        mul	v8.4s, v4.4s, v20.s[0]
        sqrdmulh	v0.4s, v4.4s, v20.s[1]
        trn2	v15.4s, v27.4s, v29.4s
        mls	v26.4s, v23.4s, v7.s[0]
        mls	v17.4s, v19.4s, v7.s[0]
        ldr	q30, [x0, #0x90]
        mls	v18.4s, v6.4s, v7.s[0]
        ldr	q22, [x0, #0x80]
        add	v29.4s, v30.4s, v17.4s
        ldur	q10, [x1, #-0x20]
        add	v1.4s, v29.4s, v21.4s
        mls	v14.4s, v2.4s, v7.s[0]
        sub	v19.4s, v29.4s, v21.4s
        sub	v30.4s, v30.4s, v17.4s
        sqrdmulh	v21.4s, v1.4s, v20.s[3]
        add	v6.4s, v22.4s, v18.4s
        mul	v23.4s, v1.4s, v20.s[2]
        sqrdmulh	v20.4s, v19.4s, v10.s[1]
        mul	v24.4s, v19.4s, v10.s[0]
        ldur	q29, [x1, #-0x10]
        str	q3, [x0], #0x80
        sub	v4.4s, v30.4s, v14.4s
        stur	q13, [x0, #-0x60]
        add	v5.4s, v30.4s, v14.4s
        stur	q9, [x0, #-0x50]
        mls	v23.4s, v21.4s, v7.s[0]
        trn2	v30.4s, v31.4s, v11.4s
        trn1	v19.4s, v31.4s, v11.4s
        mls	v24.4s, v20.4s, v7.s[0]
        sub	v3.4s, v6.4s, v26.4s
        stur	q28, [x0, #-0x70]
        add	v2.4s, v6.4s, v26.4s
        mls	v8.4s, v0.4s, v7.s[0]
        sqrdmulh	v1.4s, v4.4s, v29.s[1]
        mul	v29.4s, v4.4s, v29.s[0]
        sub	v27.4s, v22.4s, v18.4s
        sqrdmulh	v26.4s, v5.4s, v10.s[3]
        mul	v9.4s, v5.4s, v10.s[2]
        trn2	v31.2d, v25.2d, v19.2d
        trn1	v21.2d, v25.2d, v19.2d
        add	v18.4s, v2.4s, v23.4s
        sub	v6.4s, v2.4s, v23.4s
        add	v0.4s, v3.4s, v24.4s
        sub	v24.4s, v3.4s, v24.4s
        mls	v29.4s, v1.4s, v7.s[0]
        mls	v9.4s, v26.4s, v7.s[0]
        sub	v14.4s, v27.4s, v8.4s
        add	v11.4s, v27.4s, v8.4s
        trn2	v2.2d, v15.2d, v30.2d
        trn1	v16.2d, v15.2d, v30.2d
        trn1	v12.4s, v0.4s, v24.4s
        trn1	v28.4s, v18.4s, v6.4s
        trn2	v8.4s, v0.4s, v24.4s
        trn2	v13.4s, v18.4s, v6.4s
        add	v20.4s, v14.4s, v29.4s
        sub	v19.4s, v11.4s, v9.4s
        add	v25.4s, v11.4s, v9.4s
        sub	v4.4s, v14.4s, v29.4s
        trn2	v22.2d, v28.2d, v12.2d
        trn2	v10.4s, v25.4s, v19.4s
        stur	q16, [x0, #-0x30]
        trn2	v23.2d, v13.2d, v8.2d
        stur	q21, [x0, #-0x40]
        trn2	v24.4s, v20.4s, v4.4s
        stur	q2, [x0, #-0x10]
        trn1	v29.2d, v28.2d, v12.2d
        stur	q31, [x0, #-0x20]
        trn1	v17.2d, v13.2d, v8.2d
        subs	x4, x4, #0x1
        cbnz	x4, Lntt_layer45678_start
        ldr	q3, [x2, #0x60]
        ldr	q13, [x2, #0x10]
        ldr	q8, [x2], #0xc0
        ldur	q27, [x2, #-0x50]
        trn1	v26.4s, v25.4s, v19.4s
        trn2	v16.2d, v10.2d, v24.2d
        mul	v15.4s, v23.4s, v8.4s
        trn1	v9.4s, v20.4s, v4.4s
        mul	v11.4s, v16.4s, v3.4s
        sqrdmulh	v31.4s, v23.4s, v13.4s
        sqrdmulh	v21.4s, v16.4s, v27.4s
        trn1	v28.2d, v10.2d, v24.2d
        trn2	v4.2d, v26.2d, v9.2d
        mul	v20.4s, v22.4s, v8.4s
        sqrdmulh	v13.4s, v22.4s, v13.4s
        mls	v15.4s, v31.4s, v7.s[0]
        mls	v11.4s, v21.4s, v7.s[0]
        sqrdmulh	v24.4s, v4.4s, v27.4s
        mls	v20.4s, v13.4s, v7.s[0]
        add	v1.4s, v17.4s, v15.4s
        sub	v21.4s, v17.4s, v15.4s
        mul	v10.4s, v4.4s, v3.4s
        add	v6.4s, v29.4s, v20.4s
        sub	v19.4s, v29.4s, v20.4s
        add	v0.4s, v28.4s, v11.4s
        sub	v8.4s, v28.4s, v11.4s
        ldur	q4, [x2, #-0xa0]
        ldur	q16, [x2, #-0x10]
        ldur	q12, [x2, #-0x40]
        ldur	q3, [x2, #-0x90]
        ldur	q11, [x2, #-0x80]
        ldur	q28, [x2, #-0x70]
        ldur	q25, [x2, #-0x30]
        trn1	v20.2d, v26.2d, v9.2d
        ldur	q18, [x2, #-0x20]
        mls	v10.4s, v24.4s, v7.s[0]
        mul	v26.4s, v0.4s, v12.4s
        sqrdmulh	v30.4s, v0.4s, v25.4s
        sqrdmulh	v14.4s, v1.4s, v3.4s
        mul	v17.4s, v21.4s, v11.4s
        sqrdmulh	v3.4s, v21.4s, v28.4s
        mul	v31.4s, v1.4s, v4.4s
        mul	v22.4s, v8.4s, v18.4s
        sqrdmulh	v24.4s, v8.4s, v16.4s
        mls	v26.4s, v30.4s, v7.s[0]
        mls	v31.4s, v14.4s, v7.s[0]
        mls	v17.4s, v3.4s, v7.s[0]
        mls	v22.4s, v24.4s, v7.s[0]
        sub	v14.4s, v20.4s, v10.4s
        add	v23.4s, v20.4s, v10.4s
        add	v18.4s, v6.4s, v31.4s
        sub	v0.4s, v19.4s, v17.4s
        add	v29.4s, v19.4s, v17.4s
        add	v5.4s, v14.4s, v22.4s
        sub	v15.4s, v23.4s, v26.4s
        sub	v27.4s, v6.4s, v31.4s
        add	v12.4s, v23.4s, v26.4s
        sub	v1.4s, v14.4s, v22.4s
        trn1	v4.4s, v18.4s, v27.4s
        trn1	v24.4s, v12.4s, v15.4s
        trn2	v8.4s, v12.4s, v15.4s
        trn2	v28.4s, v5.4s, v1.4s
        trn1	v25.4s, v5.4s, v1.4s
        trn2	v13.4s, v29.4s, v0.4s
        trn2	v2.4s, v18.4s, v27.4s
        trn1	v15.2d, v8.2d, v28.2d
        trn1	v26.2d, v24.2d, v25.2d
        str	q15, [x0, #0x50]
        trn1	v10.2d, v2.2d, v13.2d
        trn1	v6.4s, v29.4s, v0.4s
        str	q10, [x0, #0x10]
        trn2	v27.2d, v24.2d, v25.2d
        str	q26, [x0, #0x40]
        trn2	v3.2d, v4.2d, v6.2d
        str	q27, [x0, #0x60]
        trn2	v30.2d, v2.2d, v13.2d
        str	q3, [x0, #0x20]
        trn2	v12.2d, v8.2d, v28.2d
        str	q30, [x0, #0x30]
        trn1	v20.2d, v4.2d, v6.2d
        str	q12, [x0, #0x70]
        str	q20, [x0], #0x80
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
