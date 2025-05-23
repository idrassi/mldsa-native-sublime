/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_NATIVE_API_H
#define MLD_NATIVE_API_H
/*
 * Native arithmetic interface
 *
 * This header is primarily for documentation purposes.
 * It should not be included by backend implementations.
 *
 * To ensure consistency with backends, the header will be
 * included automatically after inclusion of the active
 * backend, to ensure consistency of function signatures,
 * and run sanity checks.
 */

#include <stdint.h>
#include "../cbmc.h"
#include "../common.h"

/*
 * This is the C<->native interface allowing for the drop-in of
 * native code for performance critical arithmetic components of ML-DSA.
 *
 * A _backend_ is a specific implementation of (part of) this interface.
 *
 * To add a function to a backend, define MLD_USE_NATIVE_XXX and
 * implement `static inline xxx(...)` in the profile header.
 *
 */

/*
 * Those functions are meant to be trivial wrappers around the chosen native
 * implementation. The are static inline to avoid unnecessary calls.
 * The macro before each declaration controls whether a native
 * implementation is present.
 */

#if defined(MLD_USE_NATIVE_NTT)
/*************************************************
 * Name:        mld_ntt_native
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place.
 *
 *              The input polynomial is assumed to be in normal order.
 *              The output polynomial is in bitreversed order.
 *
 * Arguments:   - int32_t p[MLDSA_N]: pointer to in/output polynomial
 **************************************************/
static MLD_INLINE void mld_ntt_native(int32_t p[MLDSA_N]);
#endif /* MLD_USE_NATIVE_NTT */


#if defined(MLD_USE_NATIVE_INTT)
/*************************************************
 * Name:        mld_intt_native
 *
 * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
 *              of a polynomial in place.
 *
 *              The input polynomial is in bitreversed order.
 *              The output polynomial is assumed to be in normal order.
 *
 * Arguments:   - uint32_t p[MLDSA_N]: pointer to in/output polynomial
 **************************************************/
static MLD_INLINE void mld_intt_native(int16_t p[MLKEM_N])
#endif /* MLD_USE_NATIVE_INTT */

#if defined(MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY)

#if MLDSA_L == 4
    /*************************************************
     * Name:        mld_polyvecl_pointwise_acc_montgomery_l4_native
     *
     * Description: Pointwise multiply vectors of polynomials of length MLDSA_L,
     *              multiply resulting vector by 2^{-32} and add (accumulate)
     *              polynomials in it.
     *              Input/output vectors are in NTT domain representation.
     *              The second input is assumed to be output of an NTT, and
     *              hence must have coefficients bounded by (-9q, +9q).
     *
     *
     * Arguments:   - int32_t *w: output polynomial
     *              - const int32_t *u: pointer to first input vector
     *              - const int32_t *v: pointer to second input vector
     **************************************************/
    static MLD_INLINE void mld_polyvecl_pointwise_acc_montgomery_l4_native(
        int32_t w[MLDSA_N], const int32_t u[4 * MLDSA_N],
        const int32_t v[4 * MLDSA_N]);
#endif /* MLDSA_L == 4 */

#if MLDSA_L == 5
/*************************************************
 * Name:        mld_polyvecl_pointwise_acc_montgomery_l5_native
 *
 * Description: Pointwise multiply vectors of polynomials of length MLDSA_L,
 *              multiply resulting vector by 2^{-32} and add (accumulate)
 *              polynomials in it.
 *              Input/output vectors are in NTT domain representation.
 *              The second input is assumed to be output of an NTT, and
 *              hence must have coefficients bounded by (-9q, +9q).
 *
 *
 * Arguments:   - int32_t *w: output polynomial
 *              - const int32_t *u: pointer to first input vector
 *              - const int32_t *v: pointer to second input vector
 **************************************************/
static MLD_INLINE void mld_polyvecl_pointwise_acc_montgomery_l5_native(
    int32_t w[MLDSA_N], const int32_t u[5 * MLDSA_N],
    const int32_t v[5 * MLDSA_N]);
#endif /* MLDSA_L == 5 */

#if MLDSA_L == 7
/*************************************************
 * Name:        mld_polyvecl_pointwise_acc_montgomery_l7_native
 *
 * Description: Pointwise multiply vectors of polynomials of length MLDSA_L,
 *              multiply resulting vector by 2^{-32} and add (accumulate)
 *              polynomials in it.
 *              Input/output vectors are in NTT domain representation.
 *              The second input is assumed to be output of an NTT, and
 *              hence must have coefficients bounded by (-9q, +9q).
 *
 *
 * Arguments:   - int32_t *w: output polynomial
 *              - const int32_t *u: pointer to first input vector
 *              - const int32_t *v: pointer to second input vector
 **************************************************/
static MLD_INLINE void mld_polyvecl_pointwise_acc_montgomery_l7_native(
    int32_t w[MLDSA_N], const int32_t u[7 * MLDSA_N],
    const int32_t v[7 * MLDSA_N]);
#endif /* MLDSA_L == 7 */

#endif /* MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY */

#endif /* !MLD_NATIVE_API_H */
