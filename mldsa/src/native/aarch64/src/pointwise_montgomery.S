/* Copyright (c) The mldsa-native project authors
   * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
    */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_AARCH64) && !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/aarch64_opt/src/pointwise_montgomery.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
.global MLD_ASM_NAMESPACE(poly_pointwise_montgomery_asm)
MLD_ASM_FN_SYMBOL(poly_pointwise_montgomery_asm)

        .cfi_startproc
        mov	w3, #0xe001             // =57345
        movk	w3, #0x7f, lsl #16
        dup	v0.4s, w3
        mov	w3, #0x2001             // =8193
        movk	w3, #0x380, lsl #16
        dup	v1.4s, w3
        mov	x3, #0x40               // =64
        ldr	q3, [x2, #0x30]
        ldr	q28, [x1, #0x30]
        ldr	q5, [x1], #0x40
        ldr	q23, [x2, #0x10]
        ldr	q2, [x2], #0x40
        ldur	q19, [x1, #-0x30]
        ldur	q31, [x1, #-0x20]
        ldur	q7, [x2, #-0x20]
        smull	v26.2d, v28.2s, v3.2s
        ldr	q25, [x2, #0x20]
        smull2	v24.2d, v28.4s, v3.4s
        ldr	q28, [x2], #0x40
        smull	v29.2d, v5.2s, v2.2s
        ldr	q6, [x1, #0x30]
        smull2	v5.2d, v5.4s, v2.4s
        ldr	q22, [x1, #0x10]
        smull	v16.2d, v19.2s, v23.2s
        smull2	v18.2d, v19.4s, v23.4s
        uzp1	v27.4s, v26.4s, v24.4s
        smull2	v17.2d, v31.4s, v7.4s
        mul	v19.4s, v27.4s, v1.4s
        uzp1	v21.4s, v29.4s, v5.4s
        smull	v4.2d, v31.2s, v7.2s
        uzp1	v20.4s, v16.4s, v18.4s
        mul	v23.4s, v21.4s, v1.4s
        smlsl	v26.2d, v19.2s, v0.2s
        smlsl2	v24.2d, v19.4s, v0.4s
        uzp1	v19.4s, v4.4s, v17.4s
        mul	v31.4s, v20.4s, v1.4s
        smlsl	v29.2d, v23.2s, v0.2s
        uzp2	v2.4s, v26.4s, v24.4s
        mul	v24.4s, v19.4s, v1.4s
        smlsl	v16.2d, v31.2s, v0.2s
        str	q2, [x0, #0x30]
        sub	x3, x3, #0x8

Lloop_start:
        smlsl2	v5.2d, v23.4s, v0.4s
        ldur	q2, [x2, #-0x10]
        smlsl2	v18.2d, v31.4s, v0.4s
        ldr	q20, [x1], #0x40
        smlsl	v4.2d, v24.2s, v0.2s
        ldur	q23, [x2, #-0x30]
        smlsl2	v17.2d, v24.4s, v0.4s
        ldur	q24, [x1, #-0x20]
        uzp2	v27.4s, v29.4s, v5.4s
        smull2	v26.2d, v6.4s, v2.4s
        smull	v2.2d, v6.2s, v2.2s
        uzp2	v19.4s, v16.4s, v18.4s
        smull2	v18.2d, v22.4s, v23.4s
        str	q27, [x0], #0x40
        smull	v16.2d, v22.2s, v23.2s
        stur	q19, [x0, #-0x30]
        smull	v29.2d, v20.2s, v28.2s
        uzp2	v3.4s, v4.4s, v17.4s
        smull2	v5.2d, v20.4s, v28.4s
        uzp1	v27.4s, v2.4s, v26.4s
        stur	q3, [x0, #-0x20]
        smull	v4.2d, v24.2s, v25.2s
        mul	v23.4s, v27.4s, v1.4s
        uzp1	v30.4s, v16.4s, v18.4s
        ldr	q6, [x1, #0x30]
        ldr	q28, [x2], #0x40
        mul	v31.4s, v30.4s, v1.4s
        uzp1	v7.4s, v29.4s, v5.4s
        ldr	q22, [x1, #0x10]
        smull2	v17.2d, v24.4s, v25.4s
        ldur	q25, [x2, #-0x20]
        smlsl	v2.2d, v23.2s, v0.2s
        smlsl2	v26.2d, v23.4s, v0.4s
        mul	v23.4s, v7.4s, v1.4s
        uzp1	v20.4s, v4.4s, v17.4s
        smlsl	v16.2d, v31.2s, v0.2s
        uzp2	v19.4s, v2.4s, v26.4s
        mul	v24.4s, v20.4s, v1.4s
        str	q19, [x0, #0x30]
        smlsl	v29.2d, v23.2s, v0.2s
        subs	x3, x3, #0x4
        cbnz	x3, Lloop_start
        smlsl2	v18.2d, v31.4s, v0.4s
        ldur	q19, [x2, #-0x10]
        smlsl	v4.2d, v24.2s, v0.2s
        ldr	q30, [x1, #0x20]
        smlsl2	v17.2d, v24.4s, v0.4s
        ldur	q20, [x2, #-0x30]
        smlsl2	v5.2d, v23.4s, v0.4s
        ldr	q2, [x1], #0x40
        uzp2	v16.4s, v16.4s, v18.4s
        smull2	v26.2d, v6.4s, v19.4s
        smull	v31.2d, v6.2s, v19.2s
        uzp2	v18.4s, v4.4s, v17.4s
        smull	v24.2d, v30.2s, v25.2s
        smull2	v6.2d, v30.4s, v25.4s
        uzp2	v3.4s, v29.4s, v5.4s
        str	q18, [x0, #0x20]
        smull2	v19.2d, v22.4s, v20.4s
        smull	v23.2d, v22.2s, v20.2s
        uzp1	v27.4s, v31.4s, v26.4s
        str	q16, [x0, #0x10]
        smull	v7.2d, v2.2s, v28.2s
        smull2	v5.2d, v2.4s, v28.4s
        uzp1	v22.4s, v24.4s, v6.4s
        str	q3, [x0], #0x40
        mul	v17.4s, v27.4s, v1.4s
        uzp1	v30.4s, v23.4s, v19.4s
        mul	v21.4s, v22.4s, v1.4s
        uzp1	v18.4s, v7.4s, v5.4s
        mul	v22.4s, v30.4s, v1.4s
        smlsl2	v26.2d, v17.4s, v0.4s
        mul	v3.4s, v18.4s, v1.4s
        smlsl	v31.2d, v17.2s, v0.2s
        smlsl	v24.2d, v21.2s, v0.2s
        smlsl2	v19.2d, v22.4s, v0.4s
        smlsl2	v5.2d, v3.4s, v0.4s
        smlsl	v7.2d, v3.2s, v0.2s
        uzp2	v25.4s, v31.4s, v26.4s
        smlsl	v23.2d, v22.2s, v0.2s
        smlsl2	v6.2d, v21.4s, v0.4s
        str	q25, [x0, #0x30]
        uzp2	v26.4s, v7.4s, v5.4s
        uzp2	v19.4s, v23.4s, v19.4s
        uzp2	v21.4s, v24.4s, v6.4s
        str	q26, [x0], #0x40
        stur	q19, [x0, #-0x30]
        stur	q21, [x0, #-0x20]
        ret
        .cfi_endproc

#endif /* MLD_ARITH_BACKEND_AARCH64 && !MLD_CONFIG_MULTILEVEL_NO_SHARED */
