/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../notrandombytes/notrandombytes.h"
#include "mldsa_native.h"
#include "src/sys.h"

#if !defined(MLD_CONFIG_SC) || defined(MLD_CONFIG_NO_RANDOMIZED_API)
int main(void)
{
  printf("MLD_CONFIG_SC not enabled or randomized API disabled; "
         "skipping SC validation.\n");
  return 0;
}
#else

#if defined(MLD_CONFIG_CONTEXT_PARAMETER)
static MLD_CONFIG_CONTEXT_PARAMETER_TYPE g_ctx = NULL;
#define CTX_API_ARG , g_ctx
#define CTX_SC_ARG , g_ctx
#else
#define CTX_API_ARG
#define CTX_SC_ARG
#endif

#ifndef MLDSA_CTILDEBYTES
#if MLD_CONFIG_PARAMETER_SET == 44
#define MLDSA_CTILDEBYTES 32
#elif MLD_CONFIG_PARAMETER_SET == 65
#define MLDSA_CTILDEBYTES 48
#elif MLD_CONFIG_PARAMETER_SET == 87
#define MLDSA_CTILDEBYTES 64
#else
#error "Unsupported parameter set for MLDSA_CTILDEBYTES"
#endif
#endif

#ifndef MLD_SC_DEFAULT_NSIG
#define MLD_SC_DEFAULT_NSIG 100u
#endif
#ifndef MLD_SC_DEFAULT_NSTAT
#define MLD_SC_DEFAULT_NSTAT 1000u
#endif
#ifndef MLD_SC_DEFAULT_NDIST
#define MLD_SC_DEFAULT_NDIST 1000u
#endif

/* Reproduce the paper workloads by running each parameter-set binary with
 *   MLD_SC_NSIG=500 MLD_SC_NSTAT=100000 MLD_SC_NDIST=100000 ./test_scXX
 * (XX in {44,65,87}). */

#define MLEN 64
#define HIST_LEN 16 /* buckets 1..15 plus an overflow bin (>=16) */

#define CHECK_OK(x, msg)                                      \
  do                                                          \
  {                                                           \
    if ((x) != 0)                                             \
    {                                                         \
      fprintf(stderr, "ERROR: %s (%s:%d)\n", msg, __FILE__,   \
              __LINE__);                                      \
      return 1;                                               \
    }                                                         \
  } while (0)

static uint32_t env_u32(const char *name, uint32_t defval)
{
  const char *val = getenv(name);
  char *end = NULL;
  unsigned long tmp;

  if (val == NULL || *val == '\0')
  {
    return defval;
  }
  tmp = strtoul(val, &end, 10);
  if (end == val || *end != '\0' || tmp > UINT32_MAX)
  {
    return defval;
  }
  return (uint32_t)tmp;
}

static void print_histogram(const char *label, const uint64_t *hist,
                            uint64_t overflow)
{
  size_t i;

  printf("%s kappa histogram:\n", label);
  for (i = 1; i < HIST_LEN; ++i)
  {
    if (hist[i] != 0)
    {
      printf("  kappa=%zu: %" PRIu64 "\n", i, hist[i]);
    }
  }
  if (overflow != 0)
  {
    printf("  kappa>=%d: %" PRIu64 "\n", HIST_LEN, overflow);
  }
}

static int test_roundtrip(uint8_t pk[CRYPTO_PUBLICKEYBYTES],
                          uint8_t sk[CRYPTO_SECRETKEYBYTES],
                          const uint8_t sckey[MLDSA_SC_KEYBYTES],
                          uint32_t nsig)
{
  uint8_t msg[MLEN];
  uint8_t sig[CRYPTO_BYTES];
  uint8_t payload[MLDSA_SC_MAX_PAYLOAD_BYTES];
  uint8_t recovered[MLDSA_SC_MAX_PAYLOAD_BYTES];
  size_t siglen;
  size_t cap = MLDSA_SC_MAX_PAYLOAD_BYTES;
  size_t lengths[8];
  size_t num_lengths = 0;
  size_t i;
  uint32_t j;

  lengths[num_lengths++] = 0;
  lengths[num_lengths++] = 16;
  lengths[num_lengths++] = 32;
  lengths[num_lengths++] = 64;
  lengths[num_lengths++] = 256;
  lengths[num_lengths++] = 1024;
  if (cap >= 32)
  {
    lengths[num_lengths++] = cap - 32;
  }
  lengths[num_lengths++] = cap;

  for (i = 0; i < num_lengths; ++i)
  {
    size_t len = lengths[i];
    if (len > cap)
    {
      continue;
    }

    for (j = 0; j < nsig; ++j)
    {
      randombytes(msg, MLEN);
      if (len > 0)
      {
        randombytes(payload, len);
      }

      CHECK_OK(crypto_sign_signature_sc(sig, &siglen, msg, MLEN, NULL, 0, sk,
                                        sckey, payload, len, NULL CTX_SC_ARG),
               "crypto_sign_signature_sc");
      CHECK_OK(crypto_sign_verify(sig, siglen, msg, MLEN, NULL, 0, pk
                                  CTX_API_ARG),
               "crypto_sign_verify");
      CHECK_OK(mld_sc_extract(recovered, len, msg, MLEN, NULL, 0, sig, siglen,
                              sk, sckey, 1 CTX_SC_ARG),
               "mld_sc_extract");

      if (len > 0 && memcmp(payload, recovered, len) != 0)
      {
        fprintf(stderr, "ERROR: payload mismatch (len=%zu)\n", len);
        return 1;
      }
    }
  }

  return 0;
}

int main(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t sckey[MLDSA_SC_KEYBYTES];
  uint8_t msg[MLEN];
  uint8_t sig[CRYPTO_BYTES];
  uint8_t payload[MLDSA_SC_MAX_PAYLOAD_BYTES];
  uint8_t recovered[MLDSA_SC_MAX_PAYLOAD_BYTES];
  size_t siglen;
  uint32_t nsig = env_u32("MLD_SC_NSIG", MLD_SC_DEFAULT_NSIG);
  uint32_t nstat = env_u32("MLD_SC_NSTAT", MLD_SC_DEFAULT_NSTAT);
  uint32_t ndist = env_u32("MLD_SC_NDIST", MLD_SC_DEFAULT_NDIST);
  size_t cap = MLDSA_SC_MAX_PAYLOAD_BYTES;
  size_t stat_payload_len = (cap >= 32) ? 32 : cap;
  mld_sc_stats stats_base = {0};
  mld_sc_stats stats_sc = {0};
  uint64_t hist_base[HIST_LEN] = {0};
  uint64_t hist_sc[HIST_LEN] = {0};
  uint64_t hist_base_over = 0;
  uint64_t hist_sc_over = 0;
  uint32_t i;

  printf("param_set=%d\n", MLD_CONFIG_PARAMETER_SET);
  CHECK_OK(crypto_sign_keypair(pk, sk CTX_API_ARG), "crypto_sign_keypair");
  randombytes(sckey, sizeof(sckey));

  CHECK_OK(test_roundtrip(pk, sk, sckey, nsig), "roundtrip");

  /* Boundary: L > cap must fail. */
  randombytes(msg, MLEN);
  if (crypto_sign_signature_sc(sig, &siglen, msg, MLEN, NULL, 0, sk, sckey,
                               payload, cap + 1, NULL CTX_SC_ARG) == 0)
  {
    fprintf(stderr, "ERROR: crypto_sign_signature_sc accepted L > cap\n");
    return 1;
  }

  randombytes(payload, stat_payload_len);
  CHECK_OK(crypto_sign_signature_sc(sig, &siglen, msg, MLEN, NULL, 0, sk, sckey,
                                    payload, stat_payload_len, NULL CTX_SC_ARG),
           "crypto_sign_signature_sc boundary extract");
  if (mld_sc_extract(recovered, cap + 1, msg, MLEN, NULL, 0, sig, siglen, sk,
                     sckey, 0 CTX_SC_ARG) == 0)
  {
    fprintf(stderr, "ERROR: mld_sc_extract accepted L > cap\n");
    return 1;
  }

  /* Negative control: baseline signatures should not decode chosen payload. */
  randombytes(msg, MLEN);
  randombytes(payload, stat_payload_len);
  CHECK_OK(crypto_sign_signature(sig, &siglen, msg, MLEN, NULL, 0, sk
                                 CTX_API_ARG),
           "crypto_sign_signature baseline");
  CHECK_OK(mld_sc_extract(recovered, stat_payload_len, msg, MLEN, NULL, 0, sig,
                          siglen, sk, sckey, 1 CTX_SC_ARG),
           "mld_sc_extract baseline");
  if (memcmp(payload, recovered, stat_payload_len) == 0)
  {
    fprintf(stderr, "ERROR: baseline extraction matched payload unexpectedly\n");
    return 1;
  }

  /* Tamper test: extraction must fail if verification is enabled. */
  randombytes(msg, MLEN);
  randombytes(payload, stat_payload_len);
  CHECK_OK(crypto_sign_signature_sc(sig, &siglen, msg, MLEN, NULL, 0, sk, sckey,
                                    payload, stat_payload_len, NULL CTX_SC_ARG),
           "crypto_sign_signature_sc tamper");
  sig[0] ^= 0x01;
  if (mld_sc_extract(recovered, stat_payload_len, msg, MLEN, NULL, 0, sig,
                     siglen, sk, sckey, 1 CTX_SC_ARG) == 0)
  {
    fprintf(stderr, "ERROR: tampered signature extracted successfully\n");
    return 1;
  }

  /* Abort-rate stats for baseline vs channel. */
  for (i = 0; i < nstat; ++i)
  {
    uint64_t before;
    uint64_t kappa;

    randombytes(msg, MLEN);

    before = stats_base.attempts;
    CHECK_OK(crypto_sign_signature_stats(sig, &siglen, msg, MLEN, NULL, 0, sk,
                                         &stats_base CTX_SC_ARG),
             "crypto_sign_signature_stats");
    kappa = stats_base.attempts - before;
    if (kappa < HIST_LEN)
    {
      hist_base[kappa]++;
    }
    else
    {
      hist_base_over++;
    }

    randombytes(payload, stat_payload_len);
    before = stats_sc.attempts;
    CHECK_OK(crypto_sign_signature_sc(sig, &siglen, msg, MLEN, NULL, 0, sk,
                                      sckey, payload, stat_payload_len,
                                      &stats_sc CTX_SC_ARG),
             "crypto_sign_signature_sc stats");
    kappa = stats_sc.attempts - before;
    if (kappa < HIST_LEN)
    {
      hist_sc[kappa]++;
    }
    else
    {
      hist_sc_over++;
    }
  }

  printf("Abort stats (nstat=%" PRIu32 "):\n", nstat);
  printf("  baseline mean attempts: %.6f\n",
         (nstat == 0) ? 0.0
                      : (double)stats_base.attempts / (double)nstat);
  printf("  channel  mean attempts: %.6f\n",
         (nstat == 0) ? 0.0 : (double)stats_sc.attempts / (double)nstat);
  printf("  baseline rejects: z=%" PRIu64 " w0=%" PRIu64 " h=%" PRIu64
         " hint=%" PRIu64 "\n",
         stats_base.reject_z, stats_base.reject_w0, stats_base.reject_h,
         stats_base.reject_hint);
  printf("  channel  rejects: z=%" PRIu64 " w0=%" PRIu64 " h=%" PRIu64
         " hint=%" PRIu64 "\n",
         stats_sc.reject_z, stats_sc.reject_w0, stats_sc.reject_h,
         stats_sc.reject_hint);
  print_histogram("baseline", hist_base, hist_base_over);
  print_histogram("channel ", hist_sc, hist_sc_over);

  if (ndist > 0)
  {
    size_t offsets[] = {
        0, 1, MLDSA_CTILDEBYTES - 1, MLDSA_CTILDEBYTES,
        MLDSA_CTILDEBYTES + 1, CRYPTO_BYTES - 1};
    size_t num_offsets = sizeof(offsets) / sizeof(offsets[0]);
    uint64_t counts_base[6][256] = {{0}};
    uint64_t counts_sc[6][256] = {{0}};

    for (i = 0; i < ndist; ++i)
    {
      size_t o;
      randombytes(msg, MLEN);
      CHECK_OK(crypto_sign_signature(sig, &siglen, msg, MLEN, NULL, 0, sk
                                     CTX_API_ARG),
               "crypto_sign_signature dist");
      for (o = 0; o < num_offsets; ++o)
      {
        counts_base[o][sig[offsets[o]]]++;
      }

      randombytes(payload, stat_payload_len);
      CHECK_OK(crypto_sign_signature_sc(sig, &siglen, msg, MLEN, NULL, 0, sk,
                                        sckey, payload, stat_payload_len,
                                        NULL CTX_SC_ARG),
               "crypto_sign_signature_sc dist");
      for (o = 0; o < num_offsets; ++o)
      {
        counts_sc[o][sig[offsets[o]]]++;
      }
    }

    printf("Chi-square (baseline vs channel) on selected signature bytes:\n");
    for (size_t o = 0; o < num_offsets; ++o)
    {
      double chi2 = 0.0;
      for (size_t b_val = 0; b_val < 256; ++b_val)
      {
        uint64_t a = counts_base[o][b_val];
        uint64_t c = counts_sc[o][b_val];
        uint64_t s = a + c;
        if (s != 0)
        {
          double diff = (double)a - (double)c;
          chi2 += (diff * diff) / (double)s;
        }
      }
      printf("  offset=%zu chi2=%.2f\n", offsets[o], chi2);
    }
  }

  printf("SC validation complete.\n");
  return 0;
}
#endif /* !MLD_CONFIG_SC || MLD_CONFIG_NO_RANDOMIZED_API */
