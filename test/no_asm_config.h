/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLD_CONFIG_H
#define MLD_CONFIG_H

#define MLD_RANDOMIZED_SIGNING

/******************************************************************************
 * Name:        MLD_CONFIG_PARAMETER_SET
 *
 * Description: Parameter set to use for ML-DSA.
 *
 *              This must be one of:
 *              - MLD_PARAMETER_SET_44 (ML-DSA-44)
 *              - MLD_PARAMETER_SET_65 (ML-DSA-65)
 *              - MLD_PARAMETER_SET_87 (ML-DSA-87)
 *
 *****************************************************************************/
#ifndef MLD_CONFIG_PARAMETER_SET
#define MLD_CONFIG_PARAMETER_SET MLD_PARAMETER_SET_44
#endif

/******************************************************************************
 * Name:        MLD_CONFIG_NAMESPACE
 *
 * Description: Namespace to use for ML-DSA symbols.
 *
 *              If this is undefined, a default namespace based on the
 *              parameter set will be used.
 *
 *****************************************************************************/
#ifndef MLD_CONFIG_NAMESPACE
#if MLD_CONFIG_PARAMETER_SET == MLD_PARAMETER_SET_44
#define MLD_CONFIG_NAMESPACE MLD_44_ref
#elif MLD_CONFIG_PARAMETER_SET == MLD_PARAMETER_SET_65
#define MLD_CONFIG_NAMESPACE MLD_65_ref
#elif MLD_CONFIG_PARAMETER_SET == MLD_PARAMETER_SET_87
#define MLD_CONFIG_NAMESPACE MLD_87_ref
#endif
#endif


/******************************************************************************
 * Name:        MLD_CONFIG_ARITH_BACKEND_FILE
 *
 * Description: The arithmetic backend to use.
 *
 *              If MLD_CONFIG_USE_NATIVE_BACKEND_ARITH is unset, this option
 *              is ignored.
 *
 *              If MLD_CONFIG_USE_NATIVE_BACKEND_ARITH is set, this option must
 *              either be undefined or the filename of an arithmetic backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLD_CONFIG_USE_NATIVE_BACKEND_ARITH) && \
    !defined(MLD_CONFIG_ARITH_BACKEND_FILE)
#define MLD_CONFIG_ARITH_BACKEND_FILE "native/meta.h"
#endif

/******************************************************************************
 * Name:        MLD_CONFIG_FIPS202_BACKEND_FILE
 *
 * Description: The FIPS-202 backend to use.
 *
 *              If MLD_CONFIG_USE_NATIVE_BACKEND_FIPS202 is set, this option
 *              must either be undefined or the filename of a FIPS202 backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLD_CONFIG_USE_NATIVE_BACKEND_FIPS202) && \
    !defined(MLD_CONFIG_FIPS202_BACKEND_FILE)
#define MLD_CONFIG_FIPS202_BACKEND_FILE "fips202/native/auto.h"
#endif

/******************************************************************************
 * Name:        MLD_CONFIG_CUSTOM_ZEROIZE
 *
 * Description: In compliance with FIPS 204 Section 3.6.3, mldsa-native zeroizes
 *              intermediate stack buffers before returning from function calls.
 *
 *              Set this option and define `mld_zeroize_native` if you want to
 *              use a custom method to zeroize intermediate stack buffers.
 *              The default implementation uses SecureZeroMemory on Windows
 *              and a memset + compiler barrier otherwise. If neither of those
 *              is available on the target platform, compilation will fail,
 *              and you will need to use MLD_CONFIG_CUSTOM_ZEROIZE to provide
 *              a custom implementation of `mld_zeroize_native()`.
 *
 *              WARNING:
 *              The explicit stack zeroization conducted by mldsa-native
 *              reduces the likelihood of data leaking on the stack, but
 *              does not eliminate it! The C standard makes no guarantee about
 *              where a compiler allocates structures and whether/where it makes
 *              copies of them. Also, in addition to entire structures, there
 *              may also be potentially exploitable leakage of individual values
 *              on the stack.
 *
 *              If you need bullet-proof zeroization of the stack, you need to
 *              consider additional measures instead of what this feature
 *              provides. In this case, you can set mld_zeroize_native to a
 *              no-op.
 *
 *****************************************************************************/
#define MLD_CONFIG_CUSTOM_ZEROIZE
#if !defined(__ASSEMBLER__)
#include <stdint.h>
#include <string.h>
#include "../mldsa/sys.h"
static MLD_INLINE void mld_zeroize_native(void *ptr, size_t len)
{
  explicit_bzero(ptr, len);
}
#endif


/******************************************************************************
 * Name:        MLD_CONFIG_KEYGEN_PCT
 *
 * Description: Compliance with @[FIPS140_3_IG, p.87] requires a
 *              Pairwise Consistency Test (PCT) to be carried out on a freshly
 *              generated keypair before it can be exported.
 *
 *              Set this option if such a check should be implemented.
 *              In this case, crypto_sign_keypair_internal and
 *              crypto_sign_keypair will return a non-zero error code if the
 *              PCT failed.
 *
 *              NOTE: This feature will drastically lower the performance of
 *              key generation.
 *
 *****************************************************************************/
/* #define MLD_CONFIG_KEYGEN_PCT */

/******************************************************************************
 * Name:        MLD_CONFIG_KEYGEN_PCT_BREAKAGE_TEST
 *
 * Description: If this option is set, the user must provide a runtime
 *              function `static inline int mld_break_pct() { ... }` to
 *              indicate whether the PCT should be made fail.
 *
 *              This option only has an effect if MLD_CONFIG_KEYGEN_PCT is set.
 *
 *****************************************************************************/
/* #define MLD_CONFIG_KEYGEN_PCT_BREAKAGE_TEST
   #if !defined(__ASSEMBLER__)
   #include "sys.h"
   static MLD_INLINE int mld_break_pct(void)
   {
       ... return 0/1 depending on whether PCT should be broken ...
   }
   #endif
*/

/******************************************************************************
 * Name:        MLD_CONFIG_NO_ASM
 *
 * Description: If this option is set, mldsa-native will be built without
 *              use of native code or inline assembly.
 *
 *              By default, inline assembly is used to implement value barriers.
 *              Without inline assembly, mldsa-native will use a global volatile
 *              'opt blocker' instead; see ct.h.
 *
 *              Inline assembly is also used to implement a secure zeroization
 *              function on non-Windows platforms. If this option is set and
 *              the target platform is not Windows, you MUST set
 *              MLK_CONFIG_CUSTOM_ZEROIZE and provide a custom zeroization
 *              function.
 *
 *              If this option is set, MLD_CONFIG_USE_NATIVE_BACKEND_FIPS202 and
 *              and MLD_CONFIG_USE_NATIVE_BACKEND_ARITH will be ignored, and no
 *              native backends will be used.
 *
 *****************************************************************************/
#define MLD_CONFIG_NO_ASM


#endif /* !MLD_CONFIG_H */
