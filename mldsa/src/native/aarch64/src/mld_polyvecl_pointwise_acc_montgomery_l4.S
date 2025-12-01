/* Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_AARCH64)

/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/aarch64_opt/src/mld_polyvecl_pointwise_acc_montgomery_l4.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLD_ASM_NAMESPACE(polyvecl_pointwise_acc_montgomery_l4_asm)
MLD_ASM_FN_SYMBOL(polyvecl_pointwise_acc_montgomery_l4_asm)

        .cfi_startproc
        mov	w3, #0xe001             // =57345
        movk	w3, #0x7f, lsl #16
        dup	v0.4s, w3
        mov	w3, #0x2001             // =8193
        movk	w3, #0x380, lsl #16
        dup	v1.4s, w3
        mov	x3, #0x40               // =64
        ldr	q24, [x1, #0x30]
        ldr	q7, [x2, #0x30]
        ldr	q22, [x2, #0x400]
        ldr	q21, [x2, #0x800]
        ldr	q30, [x1, #0x430]
        ldr	q26, [x2, #0x430]
        ldr	q16, [x2], #0x40
        ldr	q23, [x1, #0x810]
        smull	v6.2d, v24.2s, v7.2s
        ldr	q20, [x1], #0x40
        smull2	v3.2d, v24.4s, v7.4s
        ldr	q31, [x1, #0x3c0]
        smlal	v6.2d, v30.2s, v26.2s
        ldr	q19, [x2, #0xbd0]
        smlal2	v3.2d, v30.4s, v26.4s
        ldr	q4, [x2, #0xbc0]
        smull	v30.2d, v20.2s, v16.2s
        ldr	q25, [x1, #0x7c0]
        smlal	v30.2d, v31.2s, v22.2s
        ldur	q2, [x2, #-0x20]
        smull2	v18.2d, v20.4s, v16.4s
        ldr	q16, [x1, #0xbc0]
        ldr	q28, [x2, #0x7f0]
        smlal2	v18.2d, v31.4s, v22.4s
        smlal	v30.2d, v25.2s, v21.2s
        ldur	q26, [x1, #-0x20]
        smlal2	v18.2d, v25.4s, v21.4s
        ldr	q21, [x1, #0x7f0]
        ldr	q17, [x1, #0xbf0]
        smlal2	v18.2d, v16.4s, v4.4s
        ldr	q7, [x2, #0xbf0]
        smlal	v30.2d, v16.2s, v4.2s
        ldr	q31, [x1, #0x3d0]
        smull2	v5.2d, v26.4s, v2.4s
        smlal	v6.2d, v21.2s, v28.2s
        ldr	q24, [x1, #0x3e0]
        smlal2	v3.2d, v21.4s, v28.4s
        ldr	q29, [x2, #0x3e0]
        smlal	v6.2d, v17.2s, v7.2s
        ldr	q28, [x2, #0x7e0]
        smlal2	v3.2d, v17.4s, v7.4s
        ldr	q21, [x1, #0x7e0]
        ldur	q22, [x1, #-0x30]
        smull	v4.2d, v26.2s, v2.2s
        ldr	q27, [x2, #0x3d0]
        smlal2	v5.2d, v24.4s, v29.4s
        smlal	v4.2d, v24.2s, v29.2s
        uzp1	v24.4s, v30.4s, v18.4s
        ldur	q16, [x2, #-0x30]
        smlal	v4.2d, v21.2s, v28.2s
        uzp1	v17.4s, v6.4s, v3.4s
        mul	v26.4s, v24.4s, v1.4s
        ldr	q20, [x2, #0xbe0]
        mul	v25.4s, v17.4s, v1.4s
        ldr	q24, [x2, #0x7d0]
        ldr	q7, [x2, #0x30]
        smull	v29.2d, v22.2s, v16.2s
        smlsl	v30.2d, v26.2s, v0.2s
        smlsl2	v18.2d, v26.4s, v0.4s
        ldr	q26, [x1, #0xbe0]
        smlal2	v5.2d, v21.4s, v28.4s
        ldr	q28, [x2], #0x40
        smlsl2	v3.2d, v25.4s, v0.4s
        smlsl	v6.2d, v25.2s, v0.2s
        ldr	q25, [x1, #0xbd0]
        uzp2	v2.4s, v30.4s, v18.4s
        smlal2	v5.2d, v26.4s, v20.4s
        smlal	v29.2d, v31.2s, v27.2s
        ldr	q21, [x1, #0x20]
        smlal	v4.2d, v26.2s, v20.2s
        ldr	q30, [x1], #0x40
        smlal	v29.2d, v23.2s, v24.2s
        uzp2	v17.4s, v6.4s, v3.4s
        smull2	v18.2d, v22.4s, v16.4s
        str	q2, [x0], #0x40
        ldr	q3, [x1, #0x7c0]
        smlal	v29.2d, v25.2s, v19.2s
        smull2	v26.2d, v30.4s, v28.4s
        uzp1	v22.4s, v4.4s, v5.4s
        sub	x3, x3, #0x8

Ll4_loop_start:
        mul	v16.4s, v22.4s, v1.4s
        ldr	q22, [x2, #0x3c0]
        ldr	q20, [x1, #0x3c0]
        ldr	q2, [x2, #0xbc0]
        smlal2	v18.2d, v31.4s, v27.4s
        ldr	q27, [x2, #0x7c0]
        smlal2	v18.2d, v23.4s, v24.4s
        ldr	q23, [x1, #0xbc0]
        stur	q17, [x0, #-0x10]
        smull	v17.2d, v30.2s, v28.2s
        ldr	q24, [x2, #0xbe0]
        smlal2	v26.2d, v20.4s, v22.4s
        smlal2	v26.2d, v3.4s, v27.4s
        ldur	q30, [x2, #-0x20]
        smlal2	v26.2d, v23.4s, v2.4s
        ldr	q31, [x2, #0x3e0]
        smlsl	v4.2d, v16.2s, v0.2s
        ldur	q6, [x1, #-0x10]
        smlsl2	v5.2d, v16.4s, v0.4s
        smlal	v17.2d, v20.2s, v22.2s
        ldr	q20, [x1, #0x3e0]
        smlal	v17.2d, v3.2s, v27.2s
        ldr	q27, [x2, #0x3f0]
        smlal	v17.2d, v23.2s, v2.2s
        ldr	q23, [x1, #0x3f0]
        uzp2	v4.4s, v4.4s, v5.4s
        smull2	v5.2d, v21.4s, v30.4s
        smlal2	v5.2d, v20.4s, v31.4s
        ldr	q28, [x2, #0x7f0]
        smlal2	v18.2d, v25.4s, v19.4s
        ldr	q25, [x1, #0x7f0]
        smull	v2.2d, v6.2s, v7.2s
        uzp1	v19.4s, v17.4s, v26.4s
        smlal	v2.2d, v23.2s, v27.2s
        stur	q4, [x0, #-0x20]
        mul	v16.4s, v19.4s, v1.4s
        ldr	q4, [x1, #0xbf0]
        uzp1	v22.4s, v29.4s, v18.4s
        ldr	q19, [x2, #0xbf0]
        smlal	v2.2d, v25.2s, v28.2s
        ldr	q3, [x1, #0x7e0]
        mul	v22.4s, v22.4s, v1.4s
        smlsl	v17.2d, v16.2s, v0.2s
        smlsl2	v26.2d, v16.4s, v0.4s
        smlal	v2.2d, v4.2s, v19.2s
        smlsl2	v18.2d, v22.4s, v0.4s
        smlsl	v29.2d, v22.2s, v0.2s
        ldr	q16, [x2, #0x7e0]
        uzp2	v17.4s, v17.4s, v26.4s
        smull2	v26.2d, v6.4s, v7.4s
        smlal2	v26.2d, v23.4s, v27.4s
        ldr	q27, [x1, #0xbe0]
        smlal2	v26.2d, v25.4s, v28.4s
        str	q17, [x0], #0x40
        smlal2	v26.2d, v4.4s, v19.4s
        uzp2	v7.4s, v29.4s, v18.4s
        smull	v4.2d, v21.2s, v30.2s
        ldr	q21, [x1, #0x20]
        smlal	v4.2d, v20.2s, v31.2s
        stur	q7, [x0, #-0x70]
        smlal	v4.2d, v3.2s, v16.2s
        ldur	q18, [x1, #-0x30]
        smlal	v4.2d, v27.2s, v24.2s
        uzp1	v31.4s, v2.4s, v26.4s
        smlal2	v5.2d, v3.4s, v16.4s
        ldur	q7, [x2, #-0x30]
        mul	v22.4s, v31.4s, v1.4s
        ldr	q31, [x1, #0x3d0]
        ldr	q28, [x2], #0x40
        ldr	q19, [x2, #0xb90]
        smlal2	v5.2d, v27.4s, v24.4s
        ldr	q27, [x2, #0x390]
        smull	v29.2d, v18.2s, v7.2s
        ldr	q24, [x2, #0x790]
        smull2	v18.2d, v18.4s, v7.4s
        ldr	q23, [x1, #0x7d0]
        smlsl2	v26.2d, v22.4s, v0.4s
        ldr	q25, [x1, #0xbd0]
        smlsl	v2.2d, v22.2s, v0.2s
        ldr	q30, [x1], #0x40
        smlal	v29.2d, v31.2s, v27.2s
        uzp1	v22.4s, v4.4s, v5.4s
        smlal	v29.2d, v23.2s, v24.2s
        ldur	q7, [x2, #-0x10]
        smlal	v29.2d, v25.2s, v19.2s
        ldr	q3, [x1, #0x7c0]
        uzp2	v17.4s, v2.4s, v26.4s
        smull2	v26.2d, v30.4s, v28.4s
        subs	x3, x3, #0x4
        cbnz	x3, Ll4_loop_start
        mul	v22.4s, v22.4s, v1.4s
        ldr	q20, [x1, #0x7d0]
        ldr	q6, [x1, #0xbd0]
        ldur	q2, [x2, #-0x30]
        smlal2	v18.2d, v31.4s, v27.4s
        ldur	q27, [x1, #-0x30]
        smlal2	v18.2d, v23.4s, v24.4s
        ldur	q16, [x2, #-0x20]
        smlal2	v18.2d, v25.4s, v19.4s
        smlsl2	v5.2d, v22.4s, v0.4s
        stur	q17, [x0, #-0x10]
        smlsl	v4.2d, v22.2s, v0.2s
        ldr	q24, [x2, #0x3d0]
        smull	v25.2d, v27.2s, v2.2s
        smull2	v22.2d, v21.4s, v16.4s
        uzp1	v19.4s, v29.4s, v18.4s
        smull	v16.2d, v21.2s, v16.2s
        ldr	q21, [x1, #0x3d0]
        uzp2	v5.4s, v4.4s, v5.4s
        smull	v4.2d, v30.2s, v28.2s
        mul	v17.4s, v19.4s, v1.4s
        ldr	q31, [x2, #0x7d0]
        ldr	q19, [x1, #0x3c0]
        stur	q5, [x0, #-0x20]
        smull2	v30.2d, v27.4s, v2.4s
        smlal	v25.2d, v21.2s, v24.2s
        ldur	q28, [x1, #-0x10]
        ldr	q5, [x2, #0x3c0]
        smlal2	v30.2d, v21.4s, v24.4s
        smlsl	v29.2d, v17.2s, v0.2s
        ldr	q24, [x1, #0x7e0]
        smlal	v25.2d, v20.2s, v31.2s
        ldr	q27, [x2, #0xbd0]
        smlal2	v30.2d, v20.4s, v31.4s
        smull2	v31.2d, v28.4s, v7.4s
        smlal2	v26.2d, v19.4s, v5.4s
        ldr	q2, [x2, #0x7c0]
        smlal2	v30.2d, v6.4s, v27.4s
        ldr	q20, [x1, #0xbc0]
        smlal	v25.2d, v6.2s, v27.2s
        ldr	q6, [x2, #0xbc0]
        smlal	v4.2d, v19.2s, v5.2s
        ldr	q23, [x2, #0xbe0]
        smlal	v4.2d, v3.2s, v2.2s
        ldr	q27, [x2, #0x3e0]
        ldr	q19, [x1, #0x3f0]
        smlal2	v26.2d, v3.4s, v2.4s
        smlal	v4.2d, v20.2s, v6.2s
        uzp1	v3.4s, v25.4s, v30.4s
        smlal2	v26.2d, v20.4s, v6.4s
        ldr	q20, [x1, #0x3e0]
        mul	v5.4s, v3.4s, v1.4s
        ldr	q6, [x2, #0x7e0]
        ldr	q2, [x2, #0x3f0]
        smull	v28.2d, v28.2s, v7.2s
        ldr	q7, [x1, #0x7f0]
        ldr	q21, [x1, #0xbe0]
        smlal2	v22.2d, v20.4s, v27.4s
        smlal	v16.2d, v20.2s, v27.2s
        ldr	q3, [x2, #0x7f0]
        smlal2	v22.2d, v24.4s, v6.4s
        ldr	q27, [x2, #0xbf0]
        ldr	q20, [x1, #0xbf0]
        smlal	v28.2d, v19.2s, v2.2s
        smlal	v16.2d, v24.2s, v6.2s
        smlal	v28.2d, v7.2s, v3.2s
        smlal2	v31.2d, v19.4s, v2.4s
        smlal	v28.2d, v20.2s, v27.2s
        smlal2	v31.2d, v7.4s, v3.4s
        smlal2	v31.2d, v20.4s, v27.4s
        smlal2	v22.2d, v21.4s, v23.4s
        smlal	v16.2d, v21.2s, v23.2s
        uzp1	v21.4s, v4.4s, v26.4s
        smlsl	v25.2d, v5.2s, v0.2s
        uzp1	v6.4s, v28.4s, v31.4s
        mul	v7.4s, v21.4s, v1.4s
        mul	v6.4s, v6.4s, v1.4s
        uzp1	v3.4s, v16.4s, v22.4s
        mul	v3.4s, v3.4s, v1.4s
        smlsl2	v30.2d, v5.4s, v0.4s
        smlsl2	v18.2d, v17.4s, v0.4s
        smlsl	v28.2d, v6.2s, v0.2s
        smlsl	v4.2d, v7.2s, v0.2s
        uzp2	v21.4s, v25.4s, v30.4s
        smlsl	v16.2d, v3.2s, v0.2s
        smlsl2	v22.2d, v3.4s, v0.4s
        str	q21, [x0, #0x10]
        smlsl2	v26.2d, v7.4s, v0.4s
        smlsl2	v31.2d, v6.4s, v0.4s
        uzp2	v6.4s, v29.4s, v18.4s
        uzp2	v3.4s, v16.4s, v22.4s
        uzp2	v30.4s, v4.4s, v26.4s
        str	q3, [x0, #0x20]
        uzp2	v3.4s, v28.4s, v31.4s
        stur	q6, [x0, #-0x30]
        str	q30, [x0], #0x40
        stur	q3, [x0, #-0x10]
        ret
        .cfi_endproc

#endif /* MLD_ARITH_BACKEND_AARCH64 */
