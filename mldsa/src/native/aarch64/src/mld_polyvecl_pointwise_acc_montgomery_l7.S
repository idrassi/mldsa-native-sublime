/* Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_AARCH64)

/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/aarch64_opt/src/mld_polyvecl_pointwise_acc_montgomery_l7.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLD_ASM_NAMESPACE(polyvecl_pointwise_acc_montgomery_l7_asm)
MLD_ASM_FN_SYMBOL(polyvecl_pointwise_acc_montgomery_l7_asm)

        .cfi_startproc
        mov	w3, #0xe001             // =57345
        movk	w3, #0x7f, lsl #16
        dup	v0.4s, w3
        mov	w3, #0x2001             // =8193
        movk	w3, #0x380, lsl #16
        dup	v1.4s, w3
        mov	x3, #0x40               // =64
        ldr	q17, [x1], #0x40
        ldr	q4, [x2], #0x40
        ldur	q5, [x1, #-0x30]
        ldur	q31, [x2, #-0x30]
        ldur	q26, [x2, #-0x20]
        ldur	q20, [x1, #-0x10]
        ldur	q16, [x1, #-0x20]
        smull	v24.2d, v17.2s, v4.2s
        ldur	q18, [x2, #-0x10]
        smull2	v27.2d, v5.4s, v31.4s
        ldr	q7, [x1, #0x3d0]
        smull2	v25.2d, v17.4s, v4.4s
        ldr	q23, [x1, #0x3c0]
        smull	v28.2d, v16.2s, v26.2s
        ldr	q21, [x2, #0x3d0]
        smull2	v29.2d, v16.4s, v26.4s
        ldr	q19, [x1, #0x7e0]
        ldr	q22, [x2, #0x3c0]
        smull	v30.2d, v20.2s, v18.2s
        smull	v26.2d, v5.2s, v31.2s
        ldr	q4, [x1, #0x3f0]
        smlal	v26.2d, v7.2s, v21.2s
        ldr	q16, [x2, #0x3e0]
        smull2	v31.2d, v20.4s, v18.4s
        ldr	q5, [x1, #0x3e0]
        smlal2	v25.2d, v23.4s, v22.4s
        smlal	v24.2d, v23.2s, v22.2s
        ldr	q18, [x2, #0x3f0]
        smlal2	v27.2d, v7.4s, v21.4s
        ldr	q22, [x1, #0x7c0]
        smlal	v28.2d, v5.2s, v16.2s
        ldr	q17, [x2, #0x7c0]
        smlal2	v29.2d, v5.4s, v16.4s
        ldr	q16, [x2, #0x7d0]
        smlal	v30.2d, v4.2s, v18.2s
        ldr	q5, [x1, #0x7d0]
        smlal2	v31.2d, v4.4s, v18.4s
        ldr	q4, [x2, #0x7e0]
        smlal	v24.2d, v22.2s, v17.2s
        ldr	q2, [x1, #0x7f0]
        smlal2	v25.2d, v22.4s, v17.4s
        ldr	q22, [x1, #0xbd0]
        ldr	q18, [x2, #0x7f0]
        smlal	v26.2d, v5.2s, v16.2s
        smlal2	v27.2d, v5.4s, v16.4s
        smlal2	v31.2d, v2.4s, v18.4s
        ldr	q5, [x2, #0xbd0]
        smlal2	v29.2d, v19.4s, v4.4s
        ldr	q3, [x1, #0xbc0]
        ldr	q23, [x2, #0xbc0]
        smlal	v30.2d, v2.2s, v18.2s
        smlal	v28.2d, v19.2s, v4.2s
        ldr	q16, [x2, #0xbe0]
        ldr	q17, [x1, #0xbe0]
        smlal	v26.2d, v22.2s, v5.2s
        smlal2	v27.2d, v22.4s, v5.4s
        ldr	q22, [x2, #0xbf0]
        ldr	q21, [x1, #0xbf0]
        smlal2	v25.2d, v3.4s, v23.4s
        smlal	v24.2d, v3.2s, v23.2s
        ldr	q20, [x1, #0xff0]
        ldr	q23, [x2, #0xff0]
        smlal2	v29.2d, v17.4s, v16.4s
        smlal	v28.2d, v17.2s, v16.2s
        ldr	q7, [x2, #0xfc0]
        smlal	v30.2d, v21.2s, v22.2s
        ldr	q19, [x1, #0xfc0]
        ldr	q6, [x1, #0xfd0]
        sub	x3, x3, #0x4

Ll7_loop_start:
        smlal	v30.2d, v20.2s, v23.2s
        ldr	q3, [x2, #0xfd0]
        smlal2	v31.2d, v21.4s, v22.4s
        ldr	q18, [x2, #0x13f0]
        ldr	q2, [x1, #0x13f0]
        smlal2	v31.2d, v20.4s, v23.4s
        ldr	q16, [x2, #0x13d0]
        smlal	v24.2d, v19.2s, v7.2s
        smlal	v26.2d, v6.2s, v3.2s
        ldr	q17, [x2, #0x13c0]
        ldr	q20, [x1, #0x13c0]
        smlal2	v27.2d, v6.4s, v3.4s
        ldr	q5, [x1, #0x17c0]
        smlal2	v25.2d, v19.4s, v7.4s
        smlal	v30.2d, v2.2s, v18.2s
        ldr	q21, [x2, #0x17c0]
        ldr	q22, [x2, #0xfe0]
        smlal2	v31.2d, v2.4s, v18.4s
        smlal	v24.2d, v20.2s, v17.2s
        ldr	q23, [x1, #0x13d0]
        ldr	q3, [x1, #0xfe0]
        smlal2	v25.2d, v20.4s, v17.4s
        smlal	v24.2d, v5.2s, v21.2s
        ldr	q2, [x1, #0x17f0]
        ldr	q17, [x2, #0x17f0]
        smlal2	v25.2d, v5.4s, v21.4s
        smlal	v26.2d, v23.2s, v16.2s
        ldr	q5, [x2, #0x17d0]
        smlal2	v29.2d, v3.4s, v22.4s
        ldr	q4, [x2, #0x13e0]
        smlal	v28.2d, v3.2s, v22.2s
        ldr	q22, [x2, #0x17e0]
        smlal	v30.2d, v2.2s, v17.2s
        uzp1	v21.4s, v24.4s, v25.4s
        ldr	q20, [x1, #0x17d0]
        smlal2	v27.2d, v23.4s, v16.4s
        mul	v18.4s, v21.4s, v1.4s
        ldr	q23, [x1, #0x13e0]
        ldr	q3, [x1, #0x17e0]
        ldr	q6, [x2], #0x40
        smlal2	v31.2d, v2.4s, v17.4s
        smlal	v26.2d, v20.2s, v5.2s
        ldr	q2, [x1, #0x400]
        ldr	q16, [x1], #0x40
        smlal2	v29.2d, v23.4s, v4.4s
        smlsl	v24.2d, v18.2s, v0.2s
        ldr	q21, [x1, #0x7c0]
        smlsl2	v25.2d, v18.4s, v0.4s
        ldr	q18, [x2, #0x3c0]
        smlal	v28.2d, v23.2s, v4.2s
        smlal2	v27.2d, v20.4s, v5.4s
        ldr	q17, [x1, #0xbc0]
        smlal	v28.2d, v3.2s, v22.2s
        ldr	q5, [x2, #0xbc0]
        smlal2	v29.2d, v3.4s, v22.4s
        uzp2	v19.4s, v24.4s, v25.4s
        ldr	q4, [x2, #0x7c0]
        smull	v24.2d, v16.2s, v6.2s
        smull2	v25.2d, v16.4s, v6.4s
        uzp1	v23.4s, v30.4s, v31.4s
        smlal2	v25.2d, v2.4s, v18.4s
        mul	v6.4s, v23.4s, v1.4s
        smlal	v24.2d, v2.2s, v18.2s
        smlal	v24.2d, v21.2s, v4.2s
        smlal	v24.2d, v17.2s, v5.2s
        uzp1	v23.4s, v28.4s, v29.4s
        uzp1	v2.4s, v26.4s, v27.4s
        smlsl2	v31.2d, v6.4s, v0.4s
        ldur	q20, [x2, #-0x20]
        smlsl	v30.2d, v6.2s, v0.2s
        mul	v2.4s, v2.4s, v1.4s
        ldur	q18, [x1, #-0x10]
        ldr	q6, [x2, #0x7f0]
        ldr	q22, [x2, #0x3f0]
        mul	v23.4s, v23.4s, v1.4s
        ldur	q3, [x1, #-0x30]
        uzp2	v31.4s, v30.4s, v31.4s
        ldur	q30, [x2, #-0x10]
        str	q19, [x0], #0x40
        smlal2	v25.2d, v21.4s, v4.4s
        ldr	q7, [x1, #0x7f0]
        smlsl2	v27.2d, v2.4s, v0.4s
        smlsl	v26.2d, v2.2s, v0.2s
        ldur	q19, [x2, #-0x30]
        smlsl2	v29.2d, v23.4s, v0.4s
        ldr	q4, [x1, #0x3d0]
        stur	q31, [x0, #-0x10]
        smull2	v31.2d, v18.4s, v30.4s
        ldur	q2, [x1, #-0x20]
        smlsl	v28.2d, v23.2s, v0.2s
        uzp2	v16.4s, v26.4s, v27.4s
        smull2	v27.2d, v3.4s, v19.4s
        smlal2	v25.2d, v17.4s, v5.4s
        ldr	q5, [x1, #0x3f0]
        ldr	q23, [x1, #0x7d0]
        smull	v30.2d, v18.2s, v30.2s
        uzp2	v17.4s, v28.4s, v29.4s
        smull2	v29.2d, v2.4s, v20.4s
        ldr	q21, [x2, #0x3e0]
        smull	v28.2d, v2.2s, v20.2s
        ldr	q2, [x2, #0x3d0]
        smlal	v30.2d, v5.2s, v22.2s
        ldr	q18, [x1, #0xbd0]
        smlal	v30.2d, v7.2s, v6.2s
        smull	v26.2d, v3.2s, v19.2s
        ldr	q20, [x1, #0x3e0]
        smlal2	v31.2d, v5.4s, v22.4s
        ldr	q22, [x2, #0x7d0]
        ldr	q3, [x2, #0x7e0]
        smlal2	v27.2d, v4.4s, v2.4s
        stur	q17, [x0, #-0x20]
        smlal2	v31.2d, v7.4s, v6.4s
        smlal2	v29.2d, v20.4s, v21.4s
        ldr	q17, [x2, #0xbd0]
        smlal	v28.2d, v20.2s, v21.2s
        ldr	q20, [x1, #0x7e0]
        smlal	v26.2d, v4.2s, v2.2s
        ldr	q2, [x2, #0xbe0]
        smlal2	v27.2d, v23.4s, v22.4s
        ldr	q21, [x1, #0xbf0]
        smlal	v26.2d, v23.2s, v22.2s
        ldr	q5, [x1, #0xbe0]
        smlal	v26.2d, v18.2s, v17.2s
        ldr	q22, [x2, #0xbf0]
        ldr	q7, [x2, #0xfc0]
        smlal	v28.2d, v20.2s, v3.2s
        smlal2	v27.2d, v18.4s, v17.4s
        stur	q16, [x0, #-0x30]
        ldr	q6, [x1, #0xfd0]
        smlal	v28.2d, v5.2s, v2.2s
        smlal	v30.2d, v21.2s, v22.2s
        ldr	q19, [x1, #0xfc0]
        smlal2	v29.2d, v20.4s, v3.4s
        ldr	q23, [x2, #0xff0]
        smlal2	v29.2d, v5.4s, v2.4s
        ldr	q20, [x1, #0xff0]
        subs	x3, x3, #0x4
        cbnz	x3, Ll7_loop_start
        smlal2	v31.2d, v21.4s, v22.4s
        ldr	q21, [x2, #0xfd0]
        smlal2	v31.2d, v20.4s, v23.4s
        ldr	q3, [x2, #0xfe0]
        smlal	v30.2d, v20.2s, v23.2s
        ldr	q22, [x1, #0xfe0]
        smlal2	v25.2d, v19.4s, v7.4s
        smlal	v24.2d, v19.2s, v7.2s
        ldr	q7, [x2, #0x13d0]
        smlal	v26.2d, v6.2s, v21.2s
        ldr	q18, [x1, #0x13d0]
        ldr	q23, [x1, #0x13c0]
        smlal2	v27.2d, v6.4s, v21.4s
        smlal	v28.2d, v22.2s, v3.2s
        ldr	q19, [x2, #0x13c0]
        smlal2	v29.2d, v22.4s, v3.4s
        ldr	q17, [x1, #0x13e0]
        ldr	q3, [x2, #0x13e0]
        smlal2	v27.2d, v18.4s, v7.4s
        smlal	v26.2d, v18.2s, v7.2s
        ldr	q7, [x2, #0x13f0]
        smlal2	v25.2d, v23.4s, v19.4s
        ldr	q21, [x1, #0x13f0]
        smlal	v24.2d, v23.2s, v19.2s
        ldr	q19, [x1, #0x17c0]
        ldr	q20, [x2, #0x17c0]
        smlal	v28.2d, v17.2s, v3.2s
        ldr	q23, [x1, #0x17d0]
        smlal2	v29.2d, v17.4s, v3.4s
        ldr	q6, [x2, #0x17d0]
        smlal2	v31.2d, v21.4s, v7.4s
        smlal	v30.2d, v21.2s, v7.2s
        ldr	q21, [x1, #0x17e0]
        smlal	v24.2d, v19.2s, v20.2s
        ldr	q3, [x2, #0x17e0]
        smlal2	v25.2d, v19.4s, v20.4s
        ldr	q7, [x1, #0x17f0]
        smlal	v26.2d, v23.2s, v6.2s
        ldr	q20, [x2, #0x17f0]
        smlal2	v27.2d, v23.4s, v6.4s
        smlal2	v29.2d, v21.4s, v3.4s
        smlal	v28.2d, v21.2s, v3.2s
        uzp1	v21.4s, v24.4s, v25.4s
        smlal2	v31.2d, v7.4s, v20.4s
        uzp1	v22.4s, v26.4s, v27.4s
        mul	v6.4s, v21.4s, v1.4s
        mul	v3.4s, v22.4s, v1.4s
        smlal	v30.2d, v7.2s, v20.2s
        smlsl	v24.2d, v6.2s, v0.2s
        smlsl2	v25.2d, v6.4s, v0.4s
        uzp1	v7.4s, v28.4s, v29.4s
        smlsl	v26.2d, v3.2s, v0.2s
        uzp1	v21.4s, v30.4s, v31.4s
        mul	v23.4s, v7.4s, v1.4s
        mul	v16.4s, v21.4s, v1.4s
        smlsl2	v27.2d, v3.4s, v0.4s
        smlsl	v28.2d, v23.2s, v0.2s
        smlsl2	v29.2d, v23.4s, v0.4s
        smlsl2	v31.2d, v16.4s, v0.4s
        smlsl	v30.2d, v16.2s, v0.2s
        uzp2	v21.4s, v24.4s, v25.4s
        uzp2	v6.4s, v28.4s, v29.4s
        uzp2	v24.4s, v30.4s, v31.4s
        uzp2	v30.4s, v26.4s, v27.4s
        str	q6, [x0, #0x20]
        str	q21, [x0], #0x40
        stur	q24, [x0, #-0x10]
        stur	q30, [x0, #-0x30]
        ret
        .cfi_endproc

#endif /* MLD_ARITH_BACKEND_AARCH64 */
