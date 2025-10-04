/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS140_3_IG]
 *   Implementation Guidance for FIPS 140-3 and the Cryptographic Module
 *   Validation Program National Institute of Standards and Technology
 *   https://csrc.nist.gov/projects/cryptographic-module-validation-program/fips-140-3-ig-announcements
 *
 * - [FIPS204]
 *   FIPS 204 Module-Lattice-Based Digital Signature Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/204/final
 */

#ifndef MLD_CONFIG_H
#define MLD_CONFIG_H

#define MLD_RANDOMIZED_SIGNING

/******************************************************************************
 * Name:        MLD_CONFIG_PARAMETER_SET
 *
 * Description: Specifies the parameter set for ML-DSA
 *              - MLD_CONFIG_PARAMETER_SET=44 corresponds to ML-DSA-44
 *              - MLD_CONFIG_PARAMETER_SET=65 corresponds to ML-DSA-65
 *              - MLD_CONFIG_PARAMETER_SET=87 corresponds to ML-DSA-87
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#ifndef MLD_CONFIG_PARAMETER_SET
#define MLD_CONFIG_PARAMETER_SET \
  44 /* Change this for different security strengths */
#endif

/******************************************************************************
 * Name:        MLD_CONFIG_NAMESPACE_PREFIX
 *
 * Description: The prefix to use to namespace global symbols from mldsa/.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLD_CONFIG_NAMESPACE_PREFIX)
#define MLD_CONFIG_NAMESPACE_PREFIX MLD_DEFAULT_NAMESPACE_PREFIX
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
 * Name:        MLD_CONFIG_FIPS202_CUSTOM_HEADER
 *
 * Description: Custom header to use for FIPS-202
 *
 *              This should only be set if you intend to use a custom
 *              FIPS-202 implementation, different from the one shipped
 *              with mldsa-native.
 *
 *              If set, it must be the name of a file serving as the
 *              replacement for mldsa/fips202/fips202.h, and exposing
 *              the same API (see FIPS202.md).
 *
 *****************************************************************************/
/* #define MLD_CONFIG_FIPS202_CUSTOM_HEADER "SOME_FILE.h" */

/******************************************************************************
 * Name:        MLD_CONFIG_FIPS202X4_CUSTOM_HEADER
 *
 * Description: Custom header to use for FIPS-202-X4
 *
 *              This should only be set if you intend to use a custom
 *              FIPS-202 implementation, different from the one shipped
 *              with mldsa-native.
 *
 *              If set, it must be the name of a file serving as the
 *              replacement for mldsa/fips202/fips202x4.h, and exposing
 *              the same API (see FIPS202.md).
 *
 *****************************************************************************/
/* #define MLD_CONFIG_FIPS202X4_CUSTOM_HEADER "SOME_FILE.h" */

/******************************************************************************
 * Name:        MLD_CONFIG_CUSTOM_ZEROIZE
 *
 * Description: In compliance with @[FIPS204, Section 3.6.3], mldsa-native
 *              zeroizes intermediate stack buffers before returning from
 *              function calls.
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



/*************************  Config internals  ********************************/

/* Default namespace
 *
 * Don't change this. If you need a different namespace, re-define
 * MLD_CONFIG_NAMESPACE_PREFIX above instead, and remove the following.
 *
 * The default MLDSA namespace is
 *
 *   PQCP_MLDSA_NATIVE_MLDSA<LEVEL>_
 *
 * e.g., PQCP_MLDSA_NATIVE_MLDSA65_
 */

#if MLD_CONFIG_PARAMETER_SET == 44
#define MLD_DEFAULT_NAMESPACE_PREFIX PQCP_MLDSA_NATIVE_MLDSA44
#elif MLD_CONFIG_PARAMETER_SET == 65
#define MLD_DEFAULT_NAMESPACE_PREFIX PQCP_MLDSA_NATIVE_MLDSA65
#elif MLD_CONFIG_PARAMETER_SET == 87
#define MLD_DEFAULT_NAMESPACE_PREFIX PQCP_MLDSA_NATIVE_MLDSA87
#endif
#endif /* !MLD_CONFIG_H */
