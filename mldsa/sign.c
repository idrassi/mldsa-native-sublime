/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdint.h>
#include <string.h>

#include "cbmc.h"
#include "fips202/fips202.h"
#include "packing.h"
#include "poly.h"
#include "polyvec.h"
#include "randombytes.h"
#include "sign.h"
#include "symmetric.h"

static void mld_sample_s1_s2(mld_polyvecl *s1, mld_polyveck *s2,
                             const uint8_t seed[MLDSA_CRHBYTES])
__contract__(
  requires(memory_no_alias(s1, sizeof(mld_polyvecl)))
  requires(memory_no_alias(s2, sizeof(mld_polyveck)))
  requires(memory_no_alias(seed, MLDSA_CRHBYTES))
  assigns(object_whole(s1), object_whole(s2))
  ensures(forall(l0, 0, MLDSA_L, array_abs_bound(s1->vec[l0].coeffs, 0, MLDSA_N, MLDSA_ETA + 1)))
  ensures(forall(k0, 0, MLDSA_K, array_abs_bound(s2->vec[k0].coeffs, 0, MLDSA_N, MLDSA_ETA + 1)))
)
{
/* Sample short vectors s1 and s2 */
#if MLDSA_MODE == 2
  poly_uniform_eta_4x(&s1->vec[0], &s1->vec[1], &s1->vec[2], &s1->vec[3], seed,
                      0, 1, 2, 3);
  poly_uniform_eta_4x(&s2->vec[0], &s2->vec[1], &s2->vec[2], &s2->vec[3], seed,
                      4, 5, 6, 7);
#elif MLDSA_MODE == 3
  poly_uniform_eta_4x(&s1->vec[0], &s1->vec[1], &s1->vec[2], &s1->vec[3], seed,
                      0, 1, 2, 3);
  poly_uniform_eta_4x(&s1->vec[4], &s2->vec[0], &s2->vec[1],
                      &s2->vec[2] /* irrelevant */, seed, 4, 5, 6,
                      0xFF /* irrelevant */);
  poly_uniform_eta_4x(&s2->vec[2], &s2->vec[3], &s2->vec[4], &s2->vec[5], seed,
                      7, 8, 9, 10);
#elif MLDSA_MODE == 5
  poly_uniform_eta_4x(&s1->vec[0], &s1->vec[1], &s1->vec[2], &s1->vec[3], seed,
                      0, 1, 2, 3);
  poly_uniform_eta_4x(&s1->vec[4], &s1->vec[5], &s1->vec[6],
                      &s2->vec[0] /* irrelevant */, seed, 4, 5, 6,
                      0xFF /* irrelevant */);
  poly_uniform_eta_4x(&s2->vec[0], &s2->vec[1], &s2->vec[2], &s2->vec[3], seed,
                      7, 8, 9, 10);
  poly_uniform_eta_4x(&s2->vec[4], &s2->vec[5], &s2->vec[6], &s2->vec[7], seed,
                      11, 12, 13, 14);
#endif /* MLDSA_MODE == 5 */
}

int crypto_sign_keypair_internal(uint8_t *pk, uint8_t *sk,
                                 const uint8_t seed[MLDSA_SEEDBYTES])
{
  uint8_t seedbuf[2 * MLDSA_SEEDBYTES + MLDSA_CRHBYTES];
  uint8_t inbuf[MLDSA_SEEDBYTES + 2];
  uint8_t tr[MLDSA_TRBYTES];
  const uint8_t *rho, *rhoprime, *key;
  mld_polyvecl mat[MLDSA_K];
  mld_polyvecl s1, s1hat;
  mld_polyveck s2, t2, t1, t0;

  /* Get randomness for rho, rhoprime and key */
  memcpy(inbuf, seed, MLDSA_SEEDBYTES);
  inbuf[MLDSA_SEEDBYTES + 0] = MLDSA_K;
  inbuf[MLDSA_SEEDBYTES + 1] = MLDSA_L;
  shake256(seedbuf, 2 * MLDSA_SEEDBYTES + MLDSA_CRHBYTES, inbuf,
           MLDSA_SEEDBYTES + 2);
  rho = seedbuf;
  rhoprime = rho + MLDSA_SEEDBYTES;
  key = rhoprime + MLDSA_CRHBYTES;

  /* Expand matrix */
  polyvec_matrix_expand(mat, rho);

  mld_sample_s1_s2(&s1, &s2, rhoprime);

  /* Matrix-vector multiplication */
  s1hat = s1;
  polyvecl_ntt(&s1hat);
  polyvec_matrix_pointwise_montgomery(&t1, mat, &s1hat);
  polyveck_reduce(&t1);
  polyveck_invntt_tomont(&t1);

  /* Add error vector s2 */
  polyveck_add(&t1, &s2);

  /* Extract t1 and write public key */
  polyveck_caddq(&t1);
  polyveck_power2round(&t2, &t0, &t1);
  pack_pk(pk, rho, &t2);

  /* Compute H(rho, t1) and write secret key */
  shake256(tr, MLDSA_TRBYTES, pk, CRYPTO_PUBLICKEYBYTES);
  pack_sk(sk, rho, tr, key, &t0, &s1, &s2);
  return 0;
}

int crypto_sign_keypair(uint8_t *pk, uint8_t *sk)
{
  uint8_t seed[MLDSA_SEEDBYTES];
  randombytes(seed, MLDSA_SEEDBYTES);
  return crypto_sign_keypair_internal(pk, sk, seed);
}

/*************************************************
 * Name:        mld_H
 *
 * Description: Abstracts application of SHAKE256 to
 *              one, two or three blocks of data,
 *              yielding a user-requested size of
 *              output.
 *
 * Arguments:   - uint8_t *out: pointer to output
 *              - size_t outlen: requested output length in bytes
 *              - const uint8_t *in1: pointer to input block 1
 *                                    Must NOT be NULL
 *              - size_t in1len: length of input in1 bytes
 *              - const uint8_t *in2: pointer to input block 2
 *                                    May be NULL, in which case
 *                                    this block is ignored
 *              - size_t in2len: length of input in2 bytes
 *              - const uint8_t *in3: pointer to input block 3
 *                                    May be NULL, in which case
 *                                    this block is ignored
 *              - size_t in3len: length of input in3 bytes
 **************************************************/
static void mld_H(uint8_t *out, size_t outlen, const uint8_t *in1,
                  size_t in1len, const uint8_t *in2, size_t in2len,
                  const uint8_t *in3, size_t in3len)
__contract__(
  requires(outlen <= 8 * SHAKE256_RATE /* somewhat arbitrary bound */)
  requires(memory_no_alias(in1, in1len))
  requires(in2 == NULL || memory_no_alias(in2, in2len))
  requires(in3 == NULL || memory_no_alias(in3, in3len))
  requires(memory_no_alias(out, outlen))
  assigns(memory_slice(out, outlen))
)
{
  keccak_state state;
  shake256_init(&state);
  shake256_absorb(&state, in1, in1len);
  if (in2 != NULL)
  {
    shake256_absorb(&state, in2, in2len);
  }
  if (in3 != NULL)
  {
    shake256_absorb(&state, in3, in3len);
  }
  shake256_finalize(&state);
  shake256_squeeze(out, outlen, &state);
}

#define NONCE_UB ((UINT16_MAX - MLDSA_L) / MLDSA_L)

/*************************************************
 * Name:        attempt_signature_generation
 *
 * Description: Attempts to generate a single signature.
 *              This function encapsulates one iteration of the
 *              rejection sampling process to help CBMC analysis.
 *
 * Arguments:   - uint8_t *sig: pointer to output signature
 *              - const uint8_t *mu: pointer to message hash
 *              - const uint8_t *rhoprime: pointer to randomness seed
 *              - uint16_t nonce: current nonce value
 *              - const polyvecl mat[MLDSA_K]: expanded matrix
 *              - const polyvecl *s1: secret vector s1
 *              - const polyveck *s2: secret vector s2
 *              - const polyveck *t0: secret vector t0
 *
 * Returns 0 if signature generation succeeds, -1 if rejected
 **************************************************/
static int mld_attempt_signature_generation(
    uint8_t *sig, const uint8_t *mu, const uint8_t rhoprime[MLDSA_CRHBYTES],
    uint16_t nonce, const polyvecl mat[MLDSA_K], const polyvecl *s1,
    const polyveck *s2, const polyveck *t0)
__contract__(
  requires(memory_no_alias(sig, CRYPTO_BYTES))
  requires(memory_no_alias(mu, MLDSA_CRHBYTES))
  requires(memory_no_alias(rhoprime, MLDSA_CRHBYTES))
  requires(memory_no_alias(mat, MLDSA_K * sizeof(polyvecl)))
  requires(memory_no_alias(s1, sizeof(polyvecl)))
  requires(memory_no_alias(s2, sizeof(polyveck)))
  requires(memory_no_alias(t0, sizeof(polyveck)))
  requires(nonce <= NONCE_UB)
  requires(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
                                         array_bound(mat[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
  requires(forall(k2, 0, MLDSA_K, array_abs_bound(t0->vec[k2].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  requires(forall(k3, 0, MLDSA_L, array_abs_bound(s1->vec[k3].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  requires(forall(k4, 0, MLDSA_K, array_abs_bound(s2->vec[k4].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  assigns(memory_slice(sig, CRYPTO_BYTES))
  ensures(return_value == 0 || return_value == -1)
)
{
  uint8_t challenge_bytes[MLDSA_CTILDEBYTES];
  unsigned int n;
  polyvecl y, z;
  polyveck w2, w1, w0, h;
  poly cp;
  int z_invalid, w0_invalid, h_invalid;

  /* Sample intermediate vector y */
  polyvecl_uniform_gamma1(&y, rhoprime, nonce);

  /* Matrix-vector multiplication */
  z = y;
  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);

  /* Decompose w and call the random oracle */
  polyveck_caddq(&w1);
  polyveck_decompose(&w2, &w0, &w1);
  polyveck_pack_w1(sig, &w2);

  mld_H(challenge_bytes, MLDSA_CTILDEBYTES, mu, MLDSA_CRHBYTES, sig,
        MLDSA_K * MLDSA_POLYW1_PACKEDBYTES, NULL, 0);
  poly_challenge(&cp, challenge_bytes);
  poly_ntt(&cp);

  /* Compute z, reject if it reveals secret */
  polyvecl_pointwise_poly_montgomery(&z, &cp, s1);
  polyvecl_invntt_tomont(&z);
  polyvecl_add(&z, &y);
  polyvecl_reduce(&z);

  z_invalid = polyvecl_chknorm(&z, MLDSA_GAMMA1 - MLDSA_BETA);
  if (z_invalid)
  {
    return -1; /* reject */
  }

  /* If z is valid, then its coefficients are bounded by  */
  /* MLDSA_GAMMA1 - MLDSA_BETA. This will be needed below */
  /* to prove the pre-condition of pack_sig()             */
  cassert(forall(k1, 0, MLDSA_L,
                 array_abs_bound(z.vec[k1].coeffs, 0, MLDSA_N,
                                 (MLDSA_GAMMA1 - MLDSA_BETA))));

  /* Check that subtracting cs2 does not change high bits of w and low bits
   * do not reveal secret information */
  polyveck_pointwise_poly_montgomery(&h, &cp, s2);
  polyveck_invntt_tomont(&h);
  polyveck_sub(&w0, &h);
  polyveck_reduce(&w0);
  w0_invalid = polyveck_chknorm(&w0, MLDSA_GAMMA2 - MLDSA_BETA);
  if (w0_invalid)
  {
    return -1; /* reject */
  }

  /* Compute hints for w1 */
  polyveck_pointwise_poly_montgomery(&h, &cp, t0);
  polyveck_invntt_tomont(&h);
  polyveck_reduce(&h);
  h_invalid = polyveck_chknorm(&h, MLDSA_GAMMA2);
  if (h_invalid)
  {
    return -1; /* reject */
  }

  polyveck_add(&w0, &h);
  n = polyveck_make_hint(&h, &w0, &w2);
  if (n > MLDSA_OMEGA)
  {
    return -1; /* reject */
  }

  /* All is well - write signature */
  pack_sig(sig, challenge_bytes, &z, &h, n);
  return 0; /* success */
}



int crypto_sign_signature_internal(uint8_t *sig, size_t *siglen,
                                   const uint8_t *m, size_t mlen,
                                   const uint8_t *pre, size_t prelen,
                                   const uint8_t rnd[MLDSA_RNDBYTES],
                                   const uint8_t *sk, int externalmu)
{
  uint8_t seedbuf[2 * MLDSA_SEEDBYTES + MLDSA_TRBYTES + 2 * MLDSA_CRHBYTES];
  uint8_t *rho, *tr, *key, *mu, *rhoprime;
  polyvecl mat[MLDSA_K], s1;
  polyveck t0, s2;

  uint16_t nonce = 0;

  rho = seedbuf;
  tr = rho + MLDSA_SEEDBYTES;
  key = tr + MLDSA_TRBYTES;
  mu = key + MLDSA_SEEDBYTES;
  rhoprime = mu + MLDSA_CRHBYTES;
  unpack_sk(rho, tr, key, &t0, &s1, &s2, sk);

  if (!externalmu)
  {
    /* Compute mu = CRH(tr, pre, msg) */
    mld_H(mu, MLDSA_CRHBYTES, tr, MLDSA_TRBYTES, pre, prelen, m, mlen);
  }
  else
  {
    /* mu has been provided directly */
    memcpy(mu, m, MLDSA_CRHBYTES);
  }

  /* Compute rhoprime = CRH(key, rnd, mu) */
  mld_H(rhoprime, MLDSA_CRHBYTES, key, MLDSA_SEEDBYTES, rnd, MLDSA_RNDBYTES, mu,
        MLDSA_CRHBYTES);

  /* Expand matrix and transform vectors */
  polyvec_matrix_expand(mat, rho);
  polyvecl_ntt(&s1);
  polyveck_ntt(&s2);
  polyveck_ntt(&t0);

  /* Reference: This code is re-structured using a while(1),  */
  /* with explicit "continue" statements (rather than "goto") */
  /* to implement rejection of invalid signatures.            */
  /* The loop statement also supplies a syntactic location to */
  /* place loop invariants for CBMC.                          */
  while (1)
  __loop__(
    assigns(nonce, object_whole(siglen), memory_slice(sig, CRYPTO_BYTES))
    invariant(nonce <= NONCE_UB)

    /* t0, s1, s2, and mat are initialized above and are NOT changed by this */
    /* loop. We can therefore re-assert their bounds here as part of the     */
    /* loop invariant. This makes proof noticeably faster with CBMC          */
    invariant(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
              array_bound(mat[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    invariant(forall(k2, 0, MLDSA_K, array_abs_bound(t0.vec[k2].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
    invariant(forall(k3, 0, MLDSA_L, array_abs_bound(s1.vec[k3].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
    invariant(forall(k4, 0, MLDSA_K, array_abs_bound(s2.vec[k4].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  )
  {
    int result;

    if (nonce == NONCE_UB)
    {
      *siglen = 0;
      memset(sig, 0, CRYPTO_BYTES);
      return -1;
    }

    result = mld_attempt_signature_generation(sig, mu, rhoprime, nonce, mat,
                                              &s1, &s2, &t0);
    nonce++;
    if (result == 0)
    {
      *siglen = CRYPTO_BYTES;
      return 0;
    }
  }
}

int crypto_sign_signature(uint8_t *sig, size_t *siglen, const uint8_t *m,
                          size_t mlen, const uint8_t *ctx, size_t ctxlen,
                          const uint8_t *sk)
{
  size_t i;
  uint8_t pre[257];
  uint8_t rnd[MLDSA_RNDBYTES];

  if (ctxlen > 255)
  {
    return -1;
  }

  /* Prepare pre = (0, ctxlen, ctx) */
  pre[0] = 0;
  pre[1] = ctxlen;
  for (i = 0; i < ctxlen; i++)
  {
    pre[2 + i] = ctx[i];
  }

#ifdef MLD_RANDOMIZED_SIGNING
  randombytes(rnd, MLDSA_RNDBYTES);
#else
  for (i = 0; i < MLDSA_RNDBYTES; i++)
  {
    rnd[i] = 0;
  }
#endif /* !MLD_RANDOMIZED_SIGNING */

  crypto_sign_signature_internal(sig, siglen, m, mlen, pre, 2 + ctxlen, rnd, sk,
                                 0);
  return 0;
}

int crypto_sign_signature_extmu(uint8_t *sig, size_t *siglen,
                                const uint8_t mu[MLDSA_CRHBYTES],
                                const uint8_t *sk)
{
  uint8_t rnd[MLDSA_RNDBYTES];

#ifdef MLD_RANDOMIZED_SIGNING
  randombytes(rnd, MLDSA_RNDBYTES);
#else
  size_t i;
  for (i = 0; i < MLDSA_RNDBYTES; i++)
  {
    rnd[i] = 0;
  }
#endif /* !MLD_RANDOMIZED_SIGNING */

  crypto_sign_signature_internal(sig, siglen, mu, 0, NULL, 0, rnd, sk, 1);
  return 0;
}

int crypto_sign(uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen,
                const uint8_t *ctx, size_t ctxlen, const uint8_t *sk)
{
  int ret;
  size_t i;

  for (i = 0; i < mlen; ++i)
  {
    sm[CRYPTO_BYTES + mlen - 1 - i] = m[mlen - 1 - i];
  }
  ret = crypto_sign_signature(sm, smlen, sm + CRYPTO_BYTES, mlen, ctx, ctxlen,
                              sk);
  *smlen += mlen;
  return ret;
}

int crypto_sign_verify_internal(const uint8_t *sig, size_t siglen,
                                const uint8_t *m, size_t mlen,
                                const uint8_t *pre, size_t prelen,
                                const uint8_t *pk, int externalmu)
{
  unsigned int i;
  uint8_t buf[MLDSA_K * MLDSA_POLYW1_PACKEDBYTES];
  uint8_t rho[MLDSA_SEEDBYTES];
  uint8_t mu[MLDSA_CRHBYTES];
  uint8_t c[MLDSA_CTILDEBYTES];
  uint8_t c2[MLDSA_CTILDEBYTES];
  mld_poly cp;
  mld_polyvecl mat[MLDSA_K], z;
  mld_polyveck t1, w1, tmp, h;

  if (siglen != CRYPTO_BYTES)
  {
    return -1;
  }

  unpack_pk(rho, &t1, pk);
  if (unpack_sig(c, &z, &h, sig))
  {
    return -1;
  }
  if (polyvecl_chknorm(&z, MLDSA_GAMMA1 - MLDSA_BETA))
  {
    return -1;
  }

  if (!externalmu)
  {
    /* Compute CRH(H(rho, t1), pre, msg) */
    uint8_t hpk[MLDSA_CRHBYTES];
    mld_H(hpk, MLDSA_TRBYTES, pk, CRYPTO_PUBLICKEYBYTES, NULL, 0, NULL, 0);
    mld_H(mu, MLDSA_CRHBYTES, hpk, MLDSA_TRBYTES, pre, prelen, m, mlen);
  }
  else
  {
    /* mu has been provided directly */
    memcpy(mu, m, MLDSA_CRHBYTES);
  }

  /* Matrix-vector multiplication; compute Az - c2^dt1 */
  poly_challenge(&cp, c);
  polyvec_matrix_expand(mat, rho);

  polyvecl_ntt(&z);
  polyvec_matrix_pointwise_montgomery(&w1, mat, &z);

  poly_ntt(&cp);
  polyveck_shiftl(&t1);
  polyveck_ntt(&t1);

  polyveck_pointwise_poly_montgomery(&tmp, &cp, &t1);

  polyveck_sub(&w1, &tmp);
  polyveck_reduce(&w1);
  polyveck_invntt_tomont(&w1);

  /* Reconstruct w1 */
  polyveck_caddq(&w1);
  polyveck_use_hint(&tmp, &w1, &h);
  polyveck_pack_w1(buf, &tmp);
  /* Call random oracle and verify challenge */
  mld_H(c2, MLDSA_CTILDEBYTES, mu, MLDSA_CRHBYTES, buf,
        MLDSA_K * MLDSA_POLYW1_PACKEDBYTES, NULL, 0);
  for (i = 0; i < MLDSA_CTILDEBYTES; ++i)
  __loop__(
    invariant(i <= MLDSA_CTILDEBYTES)
  )
  {
    if (c[i] != c2[i])
    {
      return -1;
    }
  }
  return 0;
}

int crypto_sign_verify(const uint8_t *sig, size_t siglen, const uint8_t *m,
                       size_t mlen, const uint8_t *ctx, size_t ctxlen,
                       const uint8_t *pk)
{
  size_t i;
  uint8_t pre[257];

  if (ctxlen > 255)
  {
    return -1;
  }

  pre[0] = 0;
  pre[1] = ctxlen;
  for (i = 0; i < ctxlen; i++)
  __loop__(
    invariant(i <= ctxlen)
  )
  {
    pre[2 + i] = ctx[i];
  }

  return crypto_sign_verify_internal(sig, siglen, m, mlen, pre, 2 + ctxlen, pk,
                                     0);
}

int crypto_sign_verify_extmu(const uint8_t *sig, size_t siglen,
                             const uint8_t mu[MLDSA_CRHBYTES],
                             const uint8_t *pk)
{
  return crypto_sign_verify_internal(sig, siglen, mu, MLDSA_CRHBYTES, NULL, 0,
                                     pk, 1);
}

int crypto_sign_open(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
                     const uint8_t *ctx, size_t ctxlen, const uint8_t *pk)
{
  size_t i;

  if (smlen < CRYPTO_BYTES)
  {
    goto badsig;
  }

  *mlen = smlen - CRYPTO_BYTES;
  if (crypto_sign_verify(sm, CRYPTO_BYTES, sm + CRYPTO_BYTES, *mlen, ctx,
                         ctxlen, pk))
  {
    goto badsig;
  }
  else
  {
    /* All good, copy msg, return 0 */
    for (i = 0; i < *mlen; ++i)
    __loop__(
      assigns(i, memory_slice(m, *mlen))
      invariant(i <= *mlen)
    )
    {
      m[i] = sm[CRYPTO_BYTES + i];
    }
    return 0;
  }

badsig:
  /* Signature verification failed */
  *mlen = 0;
  for (i = 0; i < smlen; ++i)
  __loop__(
    assigns(i, memory_slice(m, smlen))
    invariant(i <= smlen)
  )
  {
    m[i] = 0;
  }

  return -1;
}
