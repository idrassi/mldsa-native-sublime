/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLD_CONFIG_H
#define MLD_CONFIG_H

#define MLD_RANDOMIZED_SIGNING

#ifndef MLDSA_MODE
#define MLDSA_MODE 2
#endif

#if MLDSA_MODE == 2
#define MLD_NAMESPACETOP MLD_44_ref
#define MLD_NAMESPACE(s) MLD_44_ref_##s
#elif MLDSA_MODE == 3
#define MLD_NAMESPACETOP MLD_65_ref
#define MLD_NAMESPACE(s) MLD_65_ref_##s
#elif MLDSA_MODE == 5
#define MLD_NAMESPACETOP MLD_87_ref
#define MLD_NAMESPACE(s) MLD_87_ref_##s
#endif


/******************************************************************************
 * Name:        MLD_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of this default configuration file mldsa/config.h.
 *
 *              When you need to build mldsa-native in multiple configurations,
 *              using varying MLD_CONFIG_FILE can be more convenient
 *              then configuring everything through CFLAGS.
 *
 *              To use, MLD_CONFIG_FILE _must_ be defined prior
 *              to the inclusion of any mldsa-native headers. For example,
 *              it can be set by passing `-DMLD_CONFIG_FILE="..."`
 *              on the command line.
 *
 *****************************************************************************/
/* #define MLD_CONFIG_FILE "config.h" */

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
/* #define MLD_CONFIG_CUSTOM_ZEROIZE
   #if !defined(__ASSEMBLER__)
   #include <stdint.h>
   #include "sys.h"
   static MLD_INLINE void mld_zeroize_native(void *ptr, size_t len)
   {
       ... your implementation ...
   }
   #endif
*/

/******************************************************************************
 * Name:        MLD_CONFIG_CUSTOM_MEMCPY
 *
 * Description: Set this option and define `mld_memcpy` if you want to
 *              use a custom method to copy memory instead of the standard
 *              library memcpy function.
 *
 *              The custom implementation must have the same signature and
 *              behavior as the standard memcpy function:
 *              void *mld_memcpy(void *dest, const void *src, size_t n)
 *
 *****************************************************************************/
#define MLD_CONFIG_CUSTOM_MEMCPY
#if !defined(__ASSEMBLER__)
#include <stddef.h>
#include <stdint.h>
#include "../mldsa/sys.h"
static MLD_INLINE void *mld_memcpy(void *dest, const void *src, size_t n)
{
  /* Simple byte-by-byte copy implementation for testing */
  unsigned char *d = (unsigned char *)dest;
  const unsigned char *s = (const unsigned char *)src;
  for (size_t i = 0; i < n; i++)
  {
    d[i] = s[i];
  }
  return dest;
}
#endif /* !__ASSEMBLER__ */


/******************************************************************************
 * Name:        MLD_CONFIG_CUSTOM_MEMSET
 *
 * Description: Set this option and define `mld_memset` if you want to
 *              use a custom method to set memory instead of the standard
 *              library memset function.
 *
 *              The custom implementation must have the same signature and
 *              behavior as the standard memset function:
 *              void *mld_memset(void *s, int c, size_t n)
 *
 *****************************************************************************/
/* #define MLD_CONFIG_CUSTOM_MEMSET
   #if !defined(__ASSEMBLER__)
   #include <stdint.h>
   #include "sys.h"
   static MLD_INLINE void *mld_memset(void *s, int c, size_t n)
   {
       ... your implementation ...
   }
   #endif
*/

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
 * Name:        MLD_CONFIG_CT_TESTING_ENABLED
 *
 * Description: If set, mldsa-native annotates data as secret / public using
 *              valgrind's annotations VALGRIND_MAKE_MEM_UNDEFINED and
 *              VALGRIND_MAKE_MEM_DEFINED, enabling various checks for secret-
 *              dependent control flow of variable time execution (depending
 *              on the exact version of valgrind installed).
 *
 *****************************************************************************/
/* #define MLD_CONFIG_CT_TESTING_ENABLED */

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
 *              MLD_CONFIG_CUSTOM_ZEROIZE and provide a custom zeroization
 *              function.
 *
 *              If this option is set, MLD_CONFIG_USE_NATIVE_BACKEND_FIPS202 and
 *              and MLD_CONFIG_USE_NATIVE_BACKEND_ARITH will be ignored, and no
 *              native backends will be used.
 *
 *****************************************************************************/
/* #define MLD_CONFIG_NO_ASM */

/******************************************************************************
 * Name:        MLD_CONFIG_NO_ASM_VALUE_BARRIER
 *
 * Description: If this option is set, mldsa-native will be built without
 *              use of native code or inline assembly for value barriers.
 *
 *              By default, inline assembly (if available) is used to implement
 *              value barriers.
 *              Without inline assembly, mldsa-native will use a global volatile
 *              'opt blocker' instead; see ct.h.
 *
 *****************************************************************************/
/* #define MLD_CONFIG_NO_ASM_VALUE_BARRIER */



#endif /* !MLD_CONFIG_H */
