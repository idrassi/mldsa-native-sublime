/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * goto-cc -DCBMC sign.c --function harness -o a.out
 * goto-instrument --dfcc harness --enforce-contract mld_attempt_signature_generation --replace-call-with-contract mld_polyvecl_uniform_gamma1 --replace-call-with-contract mld_polyveck_pointwise_poly_montgomery a.out b.out
 * cbmc b.out --smt2 --slice-formula
 */

#include <stdint.h>
#include <string.h>

/***************************************************
 * CBMC contract macros (inlined from cbmc.h)
 ***************************************************/
#ifdef CBMC

#define __contract__(x) x
#define assigns(...) __CPROVER_assigns(__VA_ARGS__)
#define requires(...) __CPROVER_requires(__VA_ARGS__)
#define ensures(...) __CPROVER_ensures(__VA_ARGS__)
#define memory_slice(...) __CPROVER_object_upto(__VA_ARGS__)
#define memory_no_alias(...) __CPROVER_is_fresh(__VA_ARGS__)

/* clang-format off */
#define forall(qvar, qvar_lb, qvar_ub, predicate)                 \
  __CPROVER_forall                                                \
  {                                                               \
    unsigned qvar;                                                \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==> (predicate)   \
  }

#define CBMC_CONCAT_(left, right) left##right
#define CBMC_CONCAT(left, right) CBMC_CONCAT_(left, right)

#define array_bound_core(qvar, qvar_lb, qvar_ub, array_var,            \
                         value_lb, value_ub)                           \
  __CPROVER_forall                                                     \
  {                                                                    \
    unsigned qvar;                                                     \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==>                    \
        (((int)(value_lb) <= ((array_var)[(qvar)])) &&		       \
         (((array_var)[(qvar)]) < (int)(value_ub)))		       \
  }

#define array_bound(array_var, qvar_lb, qvar_ub, value_lb, value_ub) \
  array_bound_core(CBMC_CONCAT(_cbmc_idx, __COUNTER__), (qvar_lb),      \
      (qvar_ub), (array_var), (value_lb), (value_ub))

#define array_abs_bound(arr, lb, ub, k) \
  array_bound((arr), (lb), (ub), -((int)(k)) + 1, (k))
/* clang-format on */

#else /* !CBMC */
#define __contract__(x)
#endif /* CBMC */

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
)
{
  #if 1
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

void harness(void)
{
  uint8_t *rhoprime;
  uint16_t nonce;
  mld_polyveck *s2;
  mld_poly *cp;

  mld_attempt_signature_generation(rhoprime, nonce, s2, cp);
}
