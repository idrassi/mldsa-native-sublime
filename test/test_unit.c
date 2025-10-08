/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) 2025 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * fips202 API tests for mldsa-native
 *
 * Validates low-level x1 primitives against reference while accounting
 * for the bit-interleaved native representation on Cortex-M55.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "notrandombytes/notrandombytes.h"


#define FIPS202_NAMESPACE(A) test_priv_##A
#define MLD_COMMON_H
#define mld_memset memset
#define mld_memcpy memcpy
#define mld_zeroize(PTR, LEN) memset(PTR, 0, LEN)

#include "../mldsa/fips202/fips202.c"
#include "../mldsa/fips202/fips202x4.c"
#include "../mldsa/fips202/keccakf1600.c"

#undef FIPS202_NAMESPACE
#undef mld_keccakf1600_xor_bytes
#undef mld_keccakf1600x4_xor_bytes
#undef mld_keccakf1600_extract_bytes
#undef mld_keccakf1600x4_extract_bytes
#undef mld_keccakf1600_permute
#undef mld_keccakf1600x4_permute
#undef mld_shake256
#undef mld_shake256_release
#undef mld_shake256_squeeze
#undef mld_shake256_finalize
#undef mld_shake256_absorb
#undef mld_shake256_init
#undef mld_shake128_release
#undef mld_shake128_squeeze
#undef mld_shake128_finalize
#undef mld_shake128_absorb
#undef mld_shake128_init
#undef mld_shake256x4_release
#undef mld_shake256x4_init
#undef mld_shake256x4_squeezeblocks
#undef mld_shake256x4_absorb_once
#undef mld_shake128x4_release
#undef mld_shake128x4_init
#undef mld_shake128x4_squeezeblocks
#undef mld_shake128x4_absorb_once
#undef mld_shake256ctx
#undef mld_shake128ctx

#undef mld_memset
#undef mld_memcpy
#undef mld_zeroize

#undef MLD_FIPS202_KECCAKF1600_H
#undef MLD_FIPS202_FIPS202_H
#undef MLD_FIPS202_FIPS202X4_H
#undef MLD_COMMON_H

/* Under test */
#include "../mldsa/fips202/fips202.h"
#include "../mldsa/fips202/fips202x4.h"
#include "../mldsa/fips202/keccakf1600.h"

#define CHECK(x)                                              \
  do                                                          \
  {                                                           \
    int rc;                                                   \
    rc = (x);                                                 \
    if (!rc)                                                  \
    {                                                         \
      fprintf(stderr, "ERROR (%s,%d)\n", __FILE__, __LINE__); \
      return 1;                                               \
    }                                                         \
  } while (0)

#define STATE_BYTES (MLD_KECCAK_LANES * sizeof(uint64_t))

#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE) || \
    defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
/* Bit interleave/deinterleave helpers */
static uint64_t test_priv_bit_interleave(uint64_t in)
{
  uint64_t e = in & 0x5555555555555555ULL;
  uint64_t o = in & 0xAAAAAAAAAAAAAAAAULL;
  e = ((e >> 1) | e) & 0x3333333333333333ULL;
  e = ((e >> 2) | e) & 0x0F0F0F0F0F0F0F0FULL;
  e = ((e >> 4) | e) & 0x00FF00FF00FF00FFULL;
  e = ((e >> 8) | e) & 0x0000FFFF0000FFFFULL;
  e = ((e >> 16) | e) & 0x00000000FFFFFFFFULL;
  o = ((o << 1) | o) & 0xCCCCCCCCCCCCCCCCULL;
  o = ((o << 2) | o) & 0xF0F0F0F0F0F0F0F0ULL;
  o = ((o << 4) | o) & 0xFF00FF00FF00FF00ULL;
  o = ((o << 8) | o) & 0xFFFF0000FFFF0000ULL;
  o = ((o << 16) | o) & 0xFFFFFFFF00000000ULL;
  return e | o;
}

static uint64_t test_priv_bit_deinterleave(uint64_t in)
{
  uint64_t e = in & 0x00000000FFFFFFFFULL;
  uint64_t o = in & 0xFFFFFFFF00000000ULL;
  e = ((e << 16) | e) & 0x0000FFFF0000FFFFULL;
  e = ((e << 8) | e) & 0x00FF00FF00FF00FFULL;
  e = ((e << 4) | e) & 0x0F0F0F0F0F0F0F0FULL;
  e = ((e << 2) | e) & 0x3333333333333333ULL;
  e = ((e << 1) | e) & 0x5555555555555555ULL;
  o = ((o >> 16) | o) & 0xFFFF0000FFFF0000ULL;
  o = ((o >> 8) | o) & 0xFF00FF00FF00FF00ULL;
  o = ((o >> 4) | o) & 0xF0F0F0F0F0F0F0F0ULL;
  o = ((o >> 2) | o) & 0xCCCCCCCCCCCCCCCCULL;
  o = ((o >> 1) | o) & 0xAAAAAAAAAAAAAAAAULL;
  return e | o;
}

static void interleave_state(uint64_t out[MLD_KECCAK_LANES],
                             const uint64_t in[MLD_KECCAK_LANES])
{
  int i;

  for (i = 0; i < MLD_KECCAK_LANES; i++)
  {
    out[i] = test_priv_bit_interleave(in[i]);
  }
}

static void deinterleave_state(uint64_t out[MLD_KECCAK_LANES],
                               const uint64_t in[MLD_KECCAK_LANES])
{
  int i;

  for (i = 0; i < MLD_KECCAK_LANES; i++)
  {
    out[i] = test_priv_bit_deinterleave(in[i]);
  }
}
#endif /* MLD_USE_FIPS202_X1_XOR_NATIVE || MLD_USE_FIPS202_X4_XOR_NATIVE */

#if defined(MLD_USE_FIPS202_X4_NATIVE) && defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
/* X4 native packing: 800 bytes total: [even half(400)] [odd half(400)]
 * Each half: 25 lanes x 16 bytes; each lane holds 4x uint32 (channel 0..3)
 * Value per lane comes from bit-interleaved 64-bit: low32=even, high32=odd. */
static void pack_x4_native(
    uint64_t dst_x4[MLD_KECCAK_LANES * MLD_KECCAK_WAY],
    const uint64_t ch_interleaved[MLD_KECCAK_WAY][MLD_KECCAK_LANES])
{
  uint8_t *b = (uint8_t *)dst_x4;
  const size_t native_half = 25u * 16u; /* 400 bytes */
  int lane;
  int ch;
  size_t even_lane_off;
  size_t odd_lane_off;
  uint64_t v;
  uint32_t even32;
  uint32_t odd32;
  size_t ev_off;
  size_t od_off;

  memset(b, 0, STATE_BYTES * MLD_KECCAK_WAY);
  for (lane = 0; lane < MLD_KECCAK_LANES; lane++)
  {
    even_lane_off = (size_t)lane * 16u;
    odd_lane_off = native_half + (size_t)lane * 16u;
    for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
    {
      v = ch_interleaved[ch][lane];
      even32 = (uint32_t)(v & 0xFFFFFFFFu);
      odd32 = (uint32_t)(v >> 32);
      ev_off = even_lane_off + (size_t)ch * 4u;
      od_off = odd_lane_off + (size_t)ch * 4u;
      /* little-endian stores */
      b[ev_off + 0] = (uint8_t)(even32);
      b[ev_off + 1] = (uint8_t)(even32 >> 8);
      b[ev_off + 2] = (uint8_t)(even32 >> 16);
      b[ev_off + 3] = (uint8_t)(even32 >> 24);
      b[od_off + 0] = (uint8_t)(odd32);
      b[od_off + 1] = (uint8_t)(odd32 >> 8);
      b[od_off + 2] = (uint8_t)(odd32 >> 16);
      b[od_off + 3] = (uint8_t)(odd32 >> 24);
    }
  }
}

static void unpack_x4_native(
    uint64_t ch_interleaved_out[MLD_KECCAK_WAY][MLD_KECCAK_LANES],
    const uint64_t src_x4[MLD_KECCAK_LANES * MLD_KECCAK_WAY])
{
  const uint8_t *b = (const uint8_t *)src_x4;
  const size_t native_half = 25u * 16u; /* 400 bytes */
  int ch;
  int lane;
  size_t even_lane_off;
  size_t odd_lane_off;
  size_t ev_off;
  size_t od_off;
  uint32_t even32;
  uint32_t odd32;

  for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
  {
    for (lane = 0; lane < MLD_KECCAK_LANES; lane++)
    {
      ch_interleaved_out[ch][lane] = 0;
    }
  }
  for (lane = 0; lane < MLD_KECCAK_LANES; lane++)
  {
    even_lane_off = (size_t)lane * 16u;
    odd_lane_off = native_half + (size_t)lane * 16u;
    for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
    {
      ev_off = even_lane_off + (size_t)ch * 4u;
      od_off = odd_lane_off + (size_t)ch * 4u;
      even32 = (uint32_t)b[ev_off + 0] | ((uint32_t)b[ev_off + 1] << 8) |
               ((uint32_t)b[ev_off + 2] << 16) |
               ((uint32_t)b[ev_off + 3] << 24);
      odd32 = (uint32_t)b[od_off + 0] | ((uint32_t)b[od_off + 1] << 8) |
              ((uint32_t)b[od_off + 2] << 16) | ((uint32_t)b[od_off + 3] << 24);
      ch_interleaved_out[ch][lane] = ((uint64_t)odd32 << 32) | (uint64_t)even32;
    }
  }
}
#endif /* MLD_USE_FIPS202_X4_NATIVE && MLD_USE_FIPS202_X4_XOR_NATIVE */

#ifdef MLD_USE_FIPS202_X1_NATIVE
static int shake128_ctx_equals(const test_priv_shake128ctx *ref,
                               const mld_shake128ctx *dut)
{
  if (ref->pos != dut->pos)
  {
    return 0;
  }
#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
  uint64_t norm[MLD_KECCAK_LANES];
  deinterleave_state(norm, dut->s);
  return memcmp(ref->s, norm, sizeof norm) == 0;
#else
  return memcmp(ref->s, dut->s, sizeof ref->s) == 0;
#endif
}
#endif

#ifdef MLD_USE_FIPS202_X1_NATIVE
static int shake256_ctx_equals(const test_priv_shake256ctx *ref,
                               const mld_shake256ctx *dut)
{
  if (ref->pos != dut->pos)
  {
    return 0;
  }
#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
  uint64_t norm[MLD_KECCAK_LANES];
  deinterleave_state(norm, dut->s);
  return memcmp(ref->s, norm, sizeof norm) == 0;
#else
  return memcmp(ref->s, dut->s, sizeof ref->s) == 0;
#endif
}
#endif

#ifdef MLD_USE_FIPS202_X4_NATIVE
static int shake_x4_ctx_equals(const uint64_t *ref_ctx, const uint64_t *dut_ctx)
{
  int ch;
#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
  uint64_t dut_inter[MLD_KECCAK_WAY][MLD_KECCAK_LANES];
  unpack_x4_native(dut_inter, dut_ctx);
#endif

  for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
  {
    const uint64_t *ref_lane = ref_ctx + (size_t)ch * MLD_KECCAK_LANES;
#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
    uint64_t dut_norm[MLD_KECCAK_LANES];
    deinterleave_state(dut_norm, dut_inter[ch]);
    if (memcmp(ref_lane, dut_norm, sizeof dut_norm) != 0)
    {
      return 0;
    }
#else
    const uint64_t *dut_lane = dut_ctx + (size_t)ch * MLD_KECCAK_LANES;
    if (memcmp(ref_lane, dut_lane, sizeof(uint64_t) * MLD_KECCAK_LANES) != 0)
    {
      return 0;
    }
#endif
  }

  return 1;
}
#endif

#ifdef MLD_USE_FIPS202_X4_NATIVE
static int shake128x4_ctx_equals(const test_priv_shake128x4ctx *ref,
                                 const mld_shake128x4ctx *dut)
{
  return shake_x4_ctx_equals(ref->ctx, dut->ctx);
}
#endif

#ifdef MLD_USE_FIPS202_X4_NATIVE
static int shake256x4_ctx_equals(const test_priv_shake256x4ctx *ref,
                                 const mld_shake256x4ctx *dut)
{
  return shake_x4_ctx_equals(ref->ctx, dut->ctx);
}
#endif

#ifdef MLD_USE_FIPS202_X1_NATIVE
static int test_shake128_api(void)
{
  int fails = 0;
  static const size_t absorb_lens[] = {0,
                                       1,
                                       SHAKE128_RATE - 1,
                                       SHAKE128_RATE,
                                       SHAKE128_RATE + 7,
                                       SHAKE128_RATE * 2 + 5};
  static const size_t squeeze_lens[] = {
      0, 1, 32, SHAKE128_RATE, SHAKE128_RATE + 11, SHAKE128_RATE * 3};
  uint8_t chunk[SHAKE128_RATE * 3];
  uint8_t out_ref[SHAKE128_RATE * 4];
  uint8_t out_dut[SHAKE128_RATE * 4];
  test_priv_shake128ctx ref_ctx;
  mld_shake128ctx dut_ctx;
  size_t i;
  size_t len;
  size_t lens_count;

  test_priv_shake128_init(&ref_ctx);
  mld_shake128_init(&dut_ctx);
  CHECK(shake128_ctx_equals(&ref_ctx, &dut_ctx));

  lens_count = sizeof(absorb_lens) / sizeof(absorb_lens[0]);
  for (i = 0; i < lens_count; i++)
  {
    len = absorb_lens[i];
    if (len > 0)
    {
      randombytes(chunk, len);
    }
    test_priv_shake128_absorb(&ref_ctx, chunk, len);
    mld_shake128_absorb(&dut_ctx, chunk, len);
    CHECK(shake128_ctx_equals(&ref_ctx, &dut_ctx));
  }

  test_priv_shake128_finalize(&ref_ctx);
  mld_shake128_finalize(&dut_ctx);
  CHECK(shake128_ctx_equals(&ref_ctx, &dut_ctx));

  lens_count = sizeof(squeeze_lens) / sizeof(squeeze_lens[0]);
  for (i = 0; i < lens_count; i++)
  {
    len = squeeze_lens[i];
    memset(out_ref, 0, len);
    memset(out_dut, 0, len);
    test_priv_shake128_squeeze(out_ref, len, &ref_ctx);
    mld_shake128_squeeze(out_dut, len, &dut_ctx);
    CHECK(memcmp(out_ref, out_dut, len) == 0);
    CHECK(shake128_ctx_equals(&ref_ctx, &dut_ctx));
  }

  return fails;
}
#endif

#ifdef MLD_USE_FIPS202_X1_NATIVE
static int test_shake256_api(void)
{
  int fails = 0;
  static const size_t absorb_lens[] = {0,
                                       1,
                                       SHAKE256_RATE - 1,
                                       SHAKE256_RATE,
                                       SHAKE256_RATE + 9,
                                       SHAKE256_RATE * 2 + 3};
  static const size_t squeeze_lens[] = {
      0, 1, 48, SHAKE256_RATE, SHAKE256_RATE + 13, SHAKE256_RATE * 3};
  uint8_t chunk[SHAKE256_RATE * 3];
  uint8_t out_ref[SHAKE256_RATE * 4];
  uint8_t out_dut[SHAKE256_RATE * 4];
  test_priv_shake256ctx ref_ctx;
  mld_shake256ctx dut_ctx;
  size_t i;
  size_t len;
  size_t lens_count;

  test_priv_shake256_init(&ref_ctx);
  mld_shake256_init(&dut_ctx);
  CHECK(shake256_ctx_equals(&ref_ctx, &dut_ctx));

  lens_count = sizeof(absorb_lens) / sizeof(absorb_lens[0]);
  for (i = 0; i < lens_count; i++)
  {
    len = absorb_lens[i];
    if (len > 0)
    {
      randombytes(chunk, len);
    }
    test_priv_shake256_absorb(&ref_ctx, chunk, len);
    mld_shake256_absorb(&dut_ctx, chunk, len);
    CHECK(shake256_ctx_equals(&ref_ctx, &dut_ctx));
  }

  test_priv_shake256_finalize(&ref_ctx);
  mld_shake256_finalize(&dut_ctx);
  CHECK(shake256_ctx_equals(&ref_ctx, &dut_ctx));

  lens_count = sizeof(squeeze_lens) / sizeof(squeeze_lens[0]);
  for (i = 0; i < lens_count; i++)
  {
    len = squeeze_lens[i];
    memset(out_ref, 0, len);
    memset(out_dut, 0, len);
    test_priv_shake256_squeeze(out_ref, len, &ref_ctx);
    mld_shake256_squeeze(out_dut, len, &dut_ctx);
    CHECK(memcmp(out_ref, out_dut, len) == 0);
    CHECK(shake256_ctx_equals(&ref_ctx, &dut_ctx));
  }

  return fails;
}
#endif

#ifdef MLD_USE_FIPS202_X1_NATIVE
static int test_shake256_function(void)
{
  int fails = 0;
  static const size_t in_lens[] = {0, 1, 50, 200};
  static const size_t out_lens[] = {0, 1, 64, 256};
  uint8_t inbuf[200];
  uint8_t out_ref[256];
  uint8_t out_dut[256];
  size_t i;
  size_t j;
  size_t inlen;
  size_t outlen;
  size_t in_count;
  size_t out_count;

  in_count = sizeof(in_lens) / sizeof(in_lens[0]);
  out_count = sizeof(out_lens) / sizeof(out_lens[0]);
  for (i = 0; i < in_count; i++)
  {
    inlen = in_lens[i];
    if (inlen > 0)
    {
      randombytes(inbuf, inlen);
    }
    for (j = 0; j < out_count; j++)
    {
      outlen = out_lens[j];
      memset(out_ref, 0, outlen);
      memset(out_dut, 0, outlen);
      test_priv_shake256(out_ref, outlen, inbuf, inlen);
      mld_shake256(out_dut, outlen, inbuf, inlen);
      CHECK(memcmp(out_ref, out_dut, outlen) == 0);
    }
  }

  return fails;
}
#endif

#ifdef MLD_USE_FIPS202_X4_NATIVE
static int test_shake128x4_api(void)
{
  int fails = 0;
  static const size_t absorb_lens[] = {0,
                                       1,
                                       SHAKE128_RATE - 1,
                                       SHAKE128_RATE,
                                       SHAKE128_RATE + 7,
                                       SHAKE128_RATE * 2 + 5};
  static const size_t block_counts[] = {0, 1, 2, 3};
  uint8_t in[MLD_KECCAK_WAY][SHAKE128_RATE * 3];
  uint8_t out_ref[MLD_KECCAK_WAY][SHAKE128_RATE * 3];
  uint8_t out_dut[MLD_KECCAK_WAY][SHAKE128_RATE * 3];
  size_t ai;
  size_t bi;
  size_t inlen;
  size_t nblocks;
  size_t absorb_count;
  size_t block_count;
  int ch;

  absorb_count = sizeof(absorb_lens) / sizeof(absorb_lens[0]);
  block_count = sizeof(block_counts) / sizeof(block_counts[0]);

  for (ai = 0; ai < absorb_count; ai++)
  {
    test_priv_shake128x4ctx ref_ctx;
    mld_shake128x4ctx dut_ctx;
    inlen = absorb_lens[ai];
    for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
    {
      if (inlen > 0)
      {
        randombytes(in[ch], inlen);
      }
    }

    test_priv_shake128x4_absorb_once(&ref_ctx, in[0], in[1], in[2], in[3],
                                     inlen);
    mld_shake128x4_absorb_once(&dut_ctx, in[0], in[1], in[2], in[3], inlen);
    CHECK(shake128x4_ctx_equals(&ref_ctx, &dut_ctx));

    for (bi = 0; bi < block_count; bi++)
    {
      test_priv_shake128x4ctx ref_copy;
      mld_shake128x4ctx dut_copy;
      nblocks = block_counts[bi];
      memcpy(&ref_copy, &ref_ctx, sizeof(ref_ctx));
      memcpy(&dut_copy, &dut_ctx, sizeof(dut_ctx));
      for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
      {
        memset(out_ref[ch], 0, nblocks * SHAKE128_RATE);
        memset(out_dut[ch], 0, nblocks * SHAKE128_RATE);
      }
      test_priv_shake128x4_squeezeblocks(out_ref[0], out_ref[1], out_ref[2],
                                         out_ref[3], nblocks, &ref_copy);
      mld_shake128x4_squeezeblocks(out_dut[0], out_dut[1], out_dut[2],
                                   out_dut[3], nblocks, &dut_copy);
      for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
      {
        CHECK(memcmp(out_ref[ch], out_dut[ch], nblocks * SHAKE128_RATE) == 0);
      }
      CHECK(shake128x4_ctx_equals(&ref_copy, &dut_copy));
    }
  }

  return fails;
}
#endif

#ifdef MLD_USE_FIPS202_X4_NATIVE
static int test_shake256x4_api(void)
{
  int fails = 0;
  static const size_t absorb_lens[] = {0,
                                       1,
                                       SHAKE256_RATE - 1,
                                       SHAKE256_RATE,
                                       SHAKE256_RATE + 9,
                                       SHAKE256_RATE * 2 + 3};
  static const size_t block_counts[] = {0, 1, 2, 3};
  uint8_t in[MLD_KECCAK_WAY][SHAKE256_RATE * 3];
  uint8_t out_ref[MLD_KECCAK_WAY][SHAKE256_RATE * 3];
  uint8_t out_dut[MLD_KECCAK_WAY][SHAKE256_RATE * 3];
  size_t ai;
  size_t bi;
  size_t inlen;
  size_t nblocks;
  size_t absorb_count;
  size_t block_count;
  int ch;

  absorb_count = sizeof(absorb_lens) / sizeof(absorb_lens[0]);
  block_count = sizeof(block_counts) / sizeof(block_counts[0]);

  for (ai = 0; ai < absorb_count; ai++)
  {
    test_priv_shake256x4ctx ref_ctx;
    mld_shake256x4ctx dut_ctx;
    inlen = absorb_lens[ai];
    for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
    {
      if (inlen > 0)
      {
        randombytes(in[ch], inlen);
      }
    }

    test_priv_shake256x4_absorb_once(&ref_ctx, in[0], in[1], in[2], in[3],
                                     inlen);
    mld_shake256x4_absorb_once(&dut_ctx, in[0], in[1], in[2], in[3], inlen);
    CHECK(shake256x4_ctx_equals(&ref_ctx, &dut_ctx));

    for (bi = 0; bi < block_count; bi++)
    {
      test_priv_shake256x4ctx ref_copy;
      mld_shake256x4ctx dut_copy;
      nblocks = block_counts[bi];
      memcpy(&ref_copy, &ref_ctx, sizeof(ref_ctx));
      memcpy(&dut_copy, &dut_ctx, sizeof(dut_ctx));

      for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
      {
        memset(out_ref[ch], 0, nblocks * SHAKE256_RATE);
        memset(out_dut[ch], 0, nblocks * SHAKE256_RATE);
      }
      test_priv_shake256x4_squeezeblocks(out_ref[0], out_ref[1], out_ref[2],
                                         out_ref[3], nblocks, &ref_copy);
      mld_shake256x4_squeezeblocks(out_dut[0], out_dut[1], out_dut[2],
                                   out_dut[3], nblocks, &dut_copy);
      for (ch = 0; ch < MLD_KECCAK_WAY; ch++)
      {
        CHECK(memcmp(out_ref[ch], out_dut[ch], nblocks * SHAKE256_RATE) == 0);
      }
      CHECK(shake256x4_ctx_equals(&ref_copy, &dut_copy));
    }
  }

  return fails;
}
#endif

#if defined(MLD_USE_FIPS202_X4_NATIVE)
static int test_x4_xor_bytes(void)
{
  int fails = 0;
  uint8_t d0[STATE_BYTES], d1[STATE_BYTES], d2[STATE_BYTES], d3[STATE_BYTES];
  uint64_t ref[MLD_KECCAK_WAY][MLD_KECCAK_LANES] = {{0}};
  uint64_t x4buf[MLD_KECCAK_LANES * MLD_KECCAK_WAY];
  const unsigned lens[] = {0, 1, 2, 7, 8, 15, 32, 64, 100, STATE_BYTES};
  unsigned li;
  unsigned len;
  unsigned off;
  size_t lens_count;
  int ch;

  randombytes(d0, sizeof d0);
  randombytes(d1, sizeof d1);
  randombytes(d2, sizeof d2);
  randombytes(d3, sizeof d3);

  lens_count = sizeof(lens) / sizeof(lens[0]);
  for (li = 0; li < lens_count; li++)
  {
    len = lens[li];
    if (len > STATE_BYTES)
    {
      continue;
    }
    for (off = 0; off + len <= STATE_BYTES; off += (off < 64 ? 7 : 13))
    {
      memset(ref, 0, sizeof ref);
      memset(x4buf, 0, sizeof x4buf);
      test_priv_keccakf1600_xor_bytes(ref[0], d0, off, len);
      test_priv_keccakf1600_xor_bytes(ref[1], d1, off, len);
      test_priv_keccakf1600_xor_bytes(ref[2], d2, off, len);
      test_priv_keccakf1600_xor_bytes(ref[3], d3, off, len);
      mld_keccakf1600x4_xor_bytes(x4buf, d0, d1, d2, d3, off, len);
#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
      uint64_t ch_inter[MLD_KECCAK_WAY][MLD_KECCAK_LANES];
      unpack_x4_native(ch_inter, x4buf);
      for (ch = 0; ch < 4; ch++)
      {
        uint64_t norm[MLD_KECCAK_LANES];
        deinterleave_state(norm, ch_inter[ch]);
        CHECK(memcmp(norm, ref[ch], sizeof norm) == 0);
      }
#else
      for (ch = 0; ch < 4; ch++)
      {
        uint64_t *ch_state =
            ((uint64_t *)x4buf) + (size_t)ch * MLD_KECCAK_LANES;
        CHECK(memcmp(ch_state, ref[ch], sizeof(ref[ch])) == 0);
      }
#endif
    }
  }
  return fails;
}

static int test_x4_extract_bytes(void)
{
  int fails = 0;
  uint64_t ref[MLD_KECCAK_WAY][MLD_KECCAK_LANES];
  uint64_t x4buf[MLD_KECCAK_LANES * MLD_KECCAK_WAY];
  uint8_t out_ref[4][STATE_BYTES];
  uint8_t out_nat[4][STATE_BYTES];
  int ch;
  const unsigned lens[] = {0, 1, 2, 7, 8, 15, 32, 64, 100, STATE_BYTES};
  unsigned li;
  unsigned len;
  unsigned off;
  size_t lens_count;

  randombytes((uint8_t *)ref[0], sizeof ref[0]);
  randombytes((uint8_t *)ref[1], sizeof ref[1]);
  randombytes((uint8_t *)ref[2], sizeof ref[2]);
  randombytes((uint8_t *)ref[3], sizeof ref[3]);

#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
  {
    uint64_t inter[MLD_KECCAK_WAY][MLD_KECCAK_LANES];
    for (ch = 0; ch < 4; ch++)
    {
      interleave_state(inter[ch], ref[ch]);
    }
    pack_x4_native(x4buf, inter);
  }
#else
  for (ch = 0; ch < 4; ch++)
  {
    memcpy(((uint64_t *)x4buf) + (size_t)ch * MLD_KECCAK_LANES, ref[ch],
           sizeof(ref[ch]));
  }
#endif

  lens_count = sizeof(lens) / sizeof(lens[0]);
  for (li = 0; li < lens_count; li++)
  {
    len = lens[li];
    if (len > STATE_BYTES)
    {
      continue;
    }
    for (off = 0; off + len <= STATE_BYTES; off += (off < 64 ? 5 : 17))
    {
      memset(out_ref, 0, sizeof out_ref);
      memset(out_nat, 0, sizeof out_nat);
      test_priv_keccakf1600_extract_bytes(ref[0], out_ref[0], off, len);
      test_priv_keccakf1600_extract_bytes(ref[1], out_ref[1], off, len);
      test_priv_keccakf1600_extract_bytes(ref[2], out_ref[2], off, len);
      test_priv_keccakf1600_extract_bytes(ref[3], out_ref[3], off, len);
      mld_keccakf1600x4_extract_bytes(x4buf, out_nat[0], out_nat[1], out_nat[2],
                                      out_nat[3], off, len);
      for (ch = 0; ch < 4; ch++)
      {
        CHECK(memcmp(out_ref[ch], out_nat[ch], len) == 0);
      }
    }
  }
  return fails;
}

static int test_x4_permute(void)
{
  int fails = 0;
  int ch;

  /* Testcase 1: first channel all 0x5555..., others zero */
  {
    uint64_t init[4][MLD_KECCAK_LANES] = {{0}};
    uint64_t ref[4][MLD_KECCAK_LANES];
    uint64_t x4buf[MLD_KECCAK_LANES * MLD_KECCAK_WAY];
#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
    uint64_t inter_out[4][MLD_KECCAK_LANES];
    uint64_t inter[4][MLD_KECCAK_LANES];
#endif
    for (ch = 0; ch < 4; ch++)
    {
      init[ch][0] = 0x5555555555555555ULL;
    }

    memcpy(ref[0], init[0], sizeof ref[0]);
    memcpy(ref[1], init[1], sizeof ref[1]);
    memcpy(ref[2], init[2], sizeof ref[2]);
    memcpy(ref[3], init[3], sizeof ref[3]);
    test_priv_keccakf1600_permute(ref[0]);
    test_priv_keccakf1600_permute(ref[1]);
    test_priv_keccakf1600_permute(ref[2]);
    test_priv_keccakf1600_permute(ref[3]);

#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
    for (ch = 0; ch < 4; ch++)
    {
      interleave_state(inter[ch], init[ch]);
    }
    pack_x4_native(x4buf, inter);
    mld_keccakf1600x4_permute(x4buf);
    unpack_x4_native(inter_out, x4buf);
    for (ch = 0; ch < 4; ch++)
    {
      uint64_t norm[MLD_KECCAK_LANES];
      deinterleave_state(norm, inter_out[ch]);
      CHECK(memcmp(norm, ref[ch], sizeof norm) == 0);
    }
#else
    for (ch = 0; ch < 4; ch++)
    {
      memcpy(((uint64_t *)x4buf) + (size_t)ch * MLD_KECCAK_LANES, init[ch],
             sizeof(init[ch]));
    }
    mld_keccakf1600x4_permute(x4buf);
    for (ch = 0; ch < 4; ch++)
    {
      uint64_t *ch_state = ((uint64_t *)x4buf) + (size_t)ch * MLD_KECCAK_LANES;
      CHECK(memcmp(ch_state, ref[ch], sizeof(ref[ch])) == 0);
    }
#endif
  }

  /* Testcase 2: randomized per-channel states */
  {
    uint64_t init[4][MLD_KECCAK_LANES];
    uint64_t ref[4][MLD_KECCAK_LANES];
    uint64_t x4buf[MLD_KECCAK_LANES * MLD_KECCAK_WAY];

#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
    uint64_t inter[4][MLD_KECCAK_LANES];
    uint64_t inter_out[4][MLD_KECCAK_LANES];
#endif

    randombytes((uint8_t *)init[0], sizeof init[0]);
    randombytes((uint8_t *)init[1], sizeof init[1]);
    randombytes((uint8_t *)init[2], sizeof init[2]);
    randombytes((uint8_t *)init[3], sizeof init[3]);

    memcpy(ref[0], init[0], sizeof ref[0]);
    memcpy(ref[1], init[1], sizeof ref[1]);
    memcpy(ref[2], init[2], sizeof ref[2]);
    memcpy(ref[3], init[3], sizeof ref[3]);
    test_priv_keccakf1600_permute(ref[0]);
    test_priv_keccakf1600_permute(ref[1]);
    test_priv_keccakf1600_permute(ref[2]);
    test_priv_keccakf1600_permute(ref[3]);

#if defined(MLD_USE_FIPS202_X4_XOR_NATIVE)
    for (ch = 0; ch < 4; ch++)
    {
      interleave_state(inter[ch], init[ch]);
    }
    pack_x4_native(x4buf, inter);
    mld_keccakf1600x4_permute(x4buf);
    unpack_x4_native(inter_out, x4buf);
    for (ch = 0; ch < 4; ch++)
    {
      uint64_t norm[MLD_KECCAK_LANES];
      deinterleave_state(norm, inter_out[ch]);
      CHECK(memcmp(norm, ref[ch], sizeof norm) == 0);
    }
#else
    for (ch = 0; ch < 4; ch++)
    {
      memcpy(((uint64_t *)x4buf) + (size_t)ch * MLD_KECCAK_LANES, init[ch],
             sizeof(init[ch]));
    }
    mld_keccakf1600x4_permute(x4buf);
    for (ch = 0; ch < 4; ch++)
    {
      uint64_t *ch_state = ((uint64_t *)x4buf) + (size_t)ch * MLD_KECCAK_LANES;
      CHECK(memcmp(ch_state, ref[ch], sizeof(ref[ch])) == 0);
    }
#endif
  }

  return fails;
}
#endif /* MLD_USE_FIPS202_X4_NATIVE */

#if defined(MLD_USE_FIPS202_X1_NATIVE)
static int test_xor_bytes(void)
{
  int fails = 0;
  uint8_t data[STATE_BYTES];
  /* Sweep a set of lengths and offsets */
  const unsigned lens[] = {0, 1, 2, 7, 8, 15, 32, 64, 100, STATE_BYTES};
  unsigned li;
  unsigned len;
  unsigned off;
  /* Random test pattern for coverage */
  randombytes(data, sizeof data);


  for (li = 0; li < sizeof(lens) / sizeof(lens[0]); li++)
  {
    len = lens[li];
    if (len > STATE_BYTES)
    {
      continue;
    }
    for (off = 0; off + len <= STATE_BYTES; off += (off < 64 ? 7 : 13))
    {
      uint64_t ref_s[MLD_KECCAK_LANES] = {0};
      uint64_t nat_s[MLD_KECCAK_LANES] = {0};
#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
      uint64_t nat_s_norm[MLD_KECCAK_LANES];
#endif
      test_priv_keccakf1600_xor_bytes(ref_s, data, off, len);
      mld_keccakf1600_xor_bytes(nat_s, data, off, len);
#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
      deinterleave_state(nat_s_norm, nat_s);
      CHECK(memcmp(ref_s, nat_s_norm, sizeof ref_s) == 0);
#else
      CHECK(memcmp(ref_s, nat_s, sizeof ref_s) == 0);
#endif
    }
  }
  return fails;
}

static int test_extract_bytes(void)
{
  int fails = 0;
  uint64_t ref_s[MLD_KECCAK_LANES];
  uint64_t nat_s[MLD_KECCAK_LANES];
  uint8_t out_ref[STATE_BYTES];
  uint8_t out_nat[STATE_BYTES];

  const unsigned lens[] = {0, 1, 2, 7, 8, 15, 32, 64, 100, STATE_BYTES};
  unsigned li;
  unsigned len;
  unsigned off;

  randombytes((uint8_t *)ref_s, sizeof ref_s);
#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
  interleave_state(nat_s, ref_s);
#else
  memcpy(nat_s, ref_s, sizeof nat_s);
#endif

  for (li = 0; li < sizeof(lens) / sizeof(lens[0]); li++)
  {
    len = lens[li];
    if (len > STATE_BYTES)
    {
      continue;
    }
    for (off = 0; off + len <= STATE_BYTES; off += (off < 64 ? 5 : 17))
    {
      memset(out_ref, 0, len);
      memset(out_nat, 0, len);
      test_priv_keccakf1600_extract_bytes(ref_s, out_ref, off, len);
      mld_keccakf1600_extract_bytes(nat_s, out_nat, off, len);
      CHECK(memcmp(out_ref, out_nat, len) == 0);
    }
  }
  return fails;
}

static int test_permute(void)
{
  int fails = 0;
  uint64_t init[MLD_KECCAK_LANES];
  uint64_t ref_s[MLD_KECCAK_LANES];
  uint64_t nat_s[MLD_KECCAK_LANES];
#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
  uint64_t nat_s_norm[MLD_KECCAK_LANES];
#endif
  randombytes((uint8_t *)init, sizeof init);

  memcpy(ref_s, init, sizeof ref_s);
  test_priv_keccakf1600_permute(ref_s);

#if defined(MLD_USE_FIPS202_X1_XOR_NATIVE)
  interleave_state(nat_s, init);
  mld_keccakf1600_permute(nat_s);
  deinterleave_state(nat_s_norm, nat_s);
  CHECK(memcmp(ref_s, nat_s_norm, sizeof ref_s) == 0);
#else
  memcpy(nat_s, init, sizeof nat_s);
  mld_keccakf1600_permute(nat_s);
  CHECK(memcmp(ref_s, nat_s, sizeof ref_s) == 0);
#endif
  return fails;
}
#endif /* MLD_USE_FIPS202_X1_NATIVE */

int main(void)
{
  int fails = 0;

  randombytes_reset();

#if defined(MLD_USE_FIPS202_X1_NATIVE)
  fails += test_xor_bytes();
  fails += test_extract_bytes();
  fails += test_permute();
#endif
#if defined(MLD_USE_FIPS202_X4_NATIVE)
  fails += test_x4_xor_bytes();
  fails += test_x4_extract_bytes();
  fails += test_x4_permute();
#endif
#if defined(MLD_USE_FIPS202_X1_NATIVE)
  fails += test_shake128_api();
  fails += test_shake256_api();
  fails += test_shake256_function();
#endif
#if defined(MLD_USE_FIPS202_X4_NATIVE)
  fails += test_shake128x4_api();
  fails += test_shake256x4_api();
#endif


  if (fails)
  {
    fprintf(stderr, "unit tests: FAILED (%d failure%s)\n", fails,
            fails == 1 ? "" : "s");
    return 1;
  }
  printf("unit tests: OK\n");
  return 0;
}
