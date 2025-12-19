/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdint.h>
#include <string.h>

#include "cbmc.h"

#define MLDSA_K 8
#define MLDSA_L 7
#define MLDSA_N 256
#define MLDSA_GAMMA1  (1 << 19)
#define MLDSA_Q 8380417

#define MLDSA_CRHBYTES 64
#define MLD_NTT_BOUND (9 * MLDSA_Q)
typedef struct
{
  int32_t coeffs[MLDSA_N];
} mld_poly;

typedef struct
{
  mld_poly vec[MLDSA_K];
} mld_polyveck;


typedef struct
{
  mld_poly vec[MLDSA_L];
} mld_polyvecl;

/*************************************************
 * Name:        mld_polyvecl_uniform_gamma1
 *
 * Description: Sample vector of polynomials with uniformly random coefficients
 *              in [-(MLDSA_GAMMA1 - 1), MLDSA_GAMMA1] by unpacking output
 *              stream of SHAKE256(seed|nonce)
 *
 * Arguments:   - mld_polyvecl *v: pointer to output vector
 *              - const uint8_t seed[]: byte array with seed of length
 *                MLDSA_CRHBYTES
 *              - uint16_t nonce: 16-bit nonce
 *************************************************/
void mld_polyvecl_uniform_gamma1(mld_polyvecl *v,
                                 const uint8_t seed[MLDSA_CRHBYTES],
                                 uint16_t nonce)
__contract__(
  requires(memory_no_alias(v, sizeof(mld_polyvecl)))
  requires(memory_no_alias(seed, MLDSA_CRHBYTES))
  requires(nonce <= (UINT16_MAX - MLDSA_L) / MLDSA_L)
  assigns(memory_slice(v, sizeof(mld_polyvecl)))
  ensures(forall(k0, 0, MLDSA_L,
    array_bound(v->vec[k0].coeffs, 0, MLDSA_N, -(MLDSA_GAMMA1 - 1), MLDSA_GAMMA1 + 1)))
);


/*************************************************
 * Name:        mld_polyveck_pointwise_poly_montgomery
 *
 * Description: Pointwise multiplication of a polynomial vector of length
 *              MLDSA_K by a single polynomial in NTT domain and multiplication
 *              of the resulting polynomial vector by 2^{-32}.
 *
 * Arguments:   - mld_polyveck *r: pointer to output vector
 *              - mld_poly *a: pointer to input polynomial
 *              - mld_polyveck *v: pointer to input vector
 **************************************************/
void mld_polyveck_pointwise_poly_montgomery(mld_polyveck *r, const mld_poly *a,
                                            const mld_polyveck *v)
__contract__(
  requires(memory_no_alias(r, sizeof(mld_polyveck)))
  requires(memory_no_alias(a, sizeof(mld_poly)))
  requires(memory_no_alias(v, sizeof(mld_polyveck)))
  requires(array_abs_bound(a->coeffs, 0, MLDSA_N, MLD_NTT_BOUND))
  requires(forall(k0, 0, MLDSA_K, array_abs_bound(v->vec[k0].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  assigns(memory_slice(r, sizeof(mld_polyveck)))
  ensures(forall(k1, 0, MLDSA_K, array_abs_bound(r->vec[k1].coeffs, 0, MLDSA_N, MLDSA_Q)))
);

#define MLD_NONCE_UB ((UINT16_MAX - MLDSA_L) / MLDSA_L)

static int mld_attempt_signature_generation(
    const uint8_t rhoprime[MLDSA_CRHBYTES], uint16_t nonce,
    const mld_polyveck *s2,
    const mld_poly *cp)
__contract__(
  requires(memory_no_alias(rhoprime, MLDSA_CRHBYTES))
  requires(memory_no_alias(s2, sizeof(mld_polyveck)))
  requires(memory_no_alias(cp, sizeof(mld_poly)))
  requires(nonce <= MLD_NONCE_UB)
  requires(forall(k4, 0, MLDSA_K, array_abs_bound(s2->vec[k4].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  requires(array_abs_bound(cp->coeffs, 0, MLDSA_N, MLD_NTT_BOUND))
)
{
  #if 0
  union
  {
    mld_polyvecl y;
    mld_polyveck h;
  } yh;
  #else
  struct
  {
    mld_polyvecl y;
    mld_polyveck h;
  } yh;
  #endif
  mld_polyvecl *y = &yh.y;
  mld_polyveck *h = &yh.h;


  mld_polyvecl_uniform_gamma1(y, rhoprime, nonce);
  mld_polyveck_pointwise_poly_montgomery(h, cp, s2);

  return 0;
}

