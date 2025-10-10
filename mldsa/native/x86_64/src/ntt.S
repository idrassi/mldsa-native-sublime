/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Dilithium optimized AVX2 implementation
 *   Bai, Ducas, Kiltz, Lepoint, Lyubashevsky, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/dilithium/tree/master/avx2
 */

 /*
  * This file is derived from the public domain
  * AVX2 Dilithium implementation @[REF_AVX2].
  */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED)

#include "consts.h"

        .intel_syntax noprefix

.macro shuffle8 r0,r1,r2,r3
vperm2i128	ymm\r2,ymm\r0,ymm\r1,0x20
vperm2i128	ymm\r3,ymm\r0,ymm\r1,0x31
.endm

.macro shuffle4 r0,r1,r2,r3
vpunpcklqdq	ymm\r2,ymm\r0,ymm\r1
vpunpckhqdq	ymm\r3,ymm\r0,ymm\r1
.endm

.macro shuffle2 r0,r1,r2,r3
vmovsldup	ymm\r2,ymm\r1
vpblendd	ymm\r2,ymm\r0,ymm\r2,0xAA
vpsrlq		ymm\r0,ymm\r0,32
vpblendd	ymm\r3,ymm\r0,ymm\r1,0xAA
.endm

.macro butterfly l,h,zl0=1,zl1=1,zh0=2,zh1=2
vpmuldq		ymm13,ymm\h,ymm\zl0
vmovshdup	ymm12,ymm\h
vpmuldq		ymm14,ymm12,ymm\zl1

vpmuldq		ymm\h,ymm\h,ymm\zh0
vpmuldq		ymm12,ymm12,ymm\zh1

vpmuldq		ymm13,ymm13,ymm0
vpmuldq		ymm14,ymm14,ymm0

vmovshdup	ymm\h,ymm\h
vpblendd	ymm\h,ymm\h,ymm12,0xAA

vpsubd		ymm12,ymm\l,ymm\h
vpaddd		ymm\l,ymm\l,ymm\h

vmovshdup	ymm13,ymm13
vpblendd	ymm13,ymm13,ymm14,0xAA

vpaddd		ymm\h,ymm12,ymm13
vpsubd		ymm\l,ymm\l,ymm13
.endm

.macro levels0t1 off
/* level 0 */
vpbroadcastd	ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+1)*4]
vpbroadcastd	ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+1)*4]

vmovdqa		ymm4,[rdi+0+32*\off]
vmovdqa		ymm5,[rdi+128+32*\off]
vmovdqa		ymm6,[rdi+256+32*\off]
vmovdqa	 	ymm7,[rdi+384+32*\off]
vmovdqa		ymm8,[rdi+512+32*\off]
vmovdqa		ymm9,[rdi+640+32*\off]
vmovdqa		ymm10,[rdi+768+32*\off]
vmovdqa	 	ymm11,[rdi+896+32*\off]

butterfly	4,8
butterfly	5,9
butterfly	6,10
butterfly	7,11

/* level 1 */
vpbroadcastd	ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+2)*4]
vpbroadcastd	ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+2)*4]
butterfly	4,6
butterfly	5,7

vpbroadcastd	ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+3)*4]
vpbroadcastd	ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+3)*4]
butterfly	8,10
butterfly	9,11

vmovdqa		[rdi+0+32*\off],ymm4
vmovdqa		[rdi+128+32*\off],ymm5
vmovdqa		[rdi+256+32*\off],ymm6
vmovdqa		[rdi+384+32*\off],ymm7
vmovdqa		[rdi+512+32*\off],ymm8
vmovdqa		[rdi+640+32*\off],ymm9
vmovdqa		[rdi+768+32*\off],ymm10
vmovdqa		[rdi+896+32*\off],ymm11
.endm

.macro levels2t7 off
/* level 2 */
vmovdqa		ymm4,[rdi+0+256*\off]
vmovdqa		ymm5,[rdi+32+256*\off]
vmovdqa		ymm6,[rdi+64+256*\off]
vmovdqa	 	ymm7,[rdi+96+256*\off]
vmovdqa		ymm8,[rdi+128+256*\off]
vmovdqa		ymm9,[rdi+160+256*\off]
vmovdqa		ymm10,[rdi+192+256*\off]
vmovdqa	 	ymm11,[rdi+224+256*\off]

vpbroadcastd	ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+4+\off)*4]
vpbroadcastd	ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+4+\off)*4]

butterfly	4,8
butterfly	5,9
butterfly	6,10
butterfly	7,11

shuffle8	4,8,3,8
shuffle8	5,9,4,9
shuffle8	6,10,5,10
shuffle8	7,11,6,11

/* level 3 */
vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+8+8*\off)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+8+8*\off)*4]

butterfly	3,5
butterfly	8,10
butterfly	4,6
butterfly	9,11

shuffle4	3,5,7,5
shuffle4	8,10,3,10
shuffle4	4,6,8,6
shuffle4	9,11,4,11

/* level 4 */
vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+40+8*\off)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+40+8*\off)*4]

butterfly	7,8
butterfly	5,6
butterfly	3,4
butterfly	10,11

shuffle2	7,8,9,8
shuffle2	5,6,7,6
shuffle2	3,4,5,4
shuffle2	10,11,3,11

/* level 5 */
vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+72+8*\off)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+72+8*\off)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2

butterfly	9,5,1,10,2,15
butterfly	8,4,1,10,2,15
butterfly	7,3,1,10,2,15
butterfly	6,11,1,10,2,15

/* level 6 */
vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104+8*\off)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104+8*\off)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2
butterfly	9,7,1,10,2,15
butterfly	8,6,1,10,2,15

vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+104+8*\off+32)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+104+8*\off+32)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2
butterfly	5,3,1,10,2,15
butterfly	4,11,1,10,2,15

/* level 7 */
vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2
butterfly	9,8,1,10,2,15

vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+32)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+32)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2
butterfly	7,6,1,10,2,15

vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+64)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+64)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2
butterfly	5,4,1,10,2,15

vmovdqa		ymm1,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS_QINV+168+8*\off+96)*4]
vmovdqa		ymm2,[rsi+(MLD_AVX2_BACKEND_DATA_OFFSET_ZETAS+168+8*\off+96)*4]
vpsrlq		ymm10,ymm1,32
vmovshdup	ymm15,ymm2
butterfly	3,11,1,10,2,15

vmovdqa		[rdi+0+256*\off],ymm9
vmovdqa		[rdi+32+256*\off],ymm8
vmovdqa		[rdi+64+256*\off],ymm7
vmovdqa		[rdi+96+256*\off],ymm6
vmovdqa		[rdi+128+256*\off],ymm5
vmovdqa		[rdi+160+256*\off],ymm4
vmovdqa		[rdi+192+256*\off],ymm3
vmovdqa		[rdi+224+256*\off],ymm11
.endm

.text
.balign 4
.global MLD_ASM_NAMESPACE(ntt_avx2)
MLD_ASM_FN_SYMBOL(ntt_avx2)
vmovdqa ymm0,[rsi+MLD_AVX2_BACKEND_DATA_OFFSET_8XQ*4]

levels0t1 0
levels0t1 1
levels0t1 2
levels0t1 3

levels2t7 0
levels2t7 1
levels2t7 2
levels2t7 3

ret
#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT && !MLD_CONFIG_MULTILEVEL_NO_SHARED \
        */
