[//]: # (SPDX-License-Identifier: CC-BY-4.0)
[//]: # (This file is auto-generated from BIBLIOGRAPHY.yml)
[//]: # (Do not modify it directly)

# Bibliography

This file lists the citations made throughout the mldsa-native 
source code and documentation.

### `FIPS140_3_IG`

* Implementation Guidance for FIPS 140-3 and the Cryptographic Module Validation Program
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/projects/cryptographic-module-validation-program/fips-140-3-ig-announcements
* Referenced from:
  - [integration/liboqs/config_aarch64.h](integration/liboqs/config_aarch64.h)
  - [integration/liboqs/config_c.h](integration/liboqs/config_c.h)
  - [integration/liboqs/config_x86_64.h](integration/liboqs/config_x86_64.h)
  - [mldsa/config.h](mldsa/config.h)
  - [mldsa/sign.c](mldsa/sign.c)
  - [test/break_pct_config.h](test/break_pct_config.h)
  - [test/custom_memcpy_config.h](test/custom_memcpy_config.h)
  - [test/custom_memset_config.h](test/custom_memset_config.h)
  - [test/custom_randombytes_config.h](test/custom_randombytes_config.h)
  - [test/custom_stdlib_config.h](test/custom_stdlib_config.h)
  - [test/custom_zeroize_config.h](test/custom_zeroize_config.h)
  - [test/no_asm_config.h](test/no_asm_config.h)

### `FIPS202`

* FIPS202 SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/pubs/fips/202/final
* Referenced from:
  - [README.md](README.md)

### `FIPS204`

* FIPS 204 Module-Lattice-Based Digital Signature Standard
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/pubs/fips/204/final
* Referenced from:
  - [README.md](README.md)
  - [mldsa/common.h](mldsa/common.h)
  - [mldsa/config.h](mldsa/config.h)
  - [mldsa/fips202/fips202.c](mldsa/fips202/fips202.c)
  - [mldsa/fips202/fips202x4.c](mldsa/fips202/fips202x4.c)
  - [mldsa/ntt.h](mldsa/ntt.h)
  - [mldsa/poly.c](mldsa/poly.c)
  - [mldsa/poly_kl.c](mldsa/poly_kl.c)
  - [mldsa/polyvec.c](mldsa/polyvec.c)
  - [mldsa/rounding.h](mldsa/rounding.h)
  - [mldsa/sign.c](mldsa/sign.c)
  - [mldsa/sign.h](mldsa/sign.h)
  - [test/break_pct_config.h](test/break_pct_config.h)
  - [test/custom_memcpy_config.h](test/custom_memcpy_config.h)
  - [test/custom_memset_config.h](test/custom_memset_config.h)
  - [test/custom_randombytes_config.h](test/custom_randombytes_config.h)
  - [test/custom_stdlib_config.h](test/custom_stdlib_config.h)
  - [test/custom_zeroize_config.h](test/custom_zeroize_config.h)
  - [test/no_asm_config.h](test/no_asm_config.h)

### `HYBRID`

* Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
* Author(s):
  - Hanno Becker
  - Matthias J. Kannwischer
* URL: https://eprint.iacr.org/2022/1243
* Referenced from:
  - [mldsa/fips202/native/aarch64/auto.h](mldsa/fips202/native/aarch64/auto.h)
  - [mldsa/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm.S](mldsa/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm.S)
  - [mldsa/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm.S](mldsa/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm.S)

### `KyberSlash`

* KyberSlash: Exploiting secret-dependent division timings in Kyber implementations
* Author(s):
  - Daniel J. Bernstein
  - Karthikeyan Bhargavan
  - Shivam Bhasin
  - Anupam Chattopadhyay
  - Tee Kiah Chia
  - Matthias J. Kannwischer
  - Franziskus Kiefer
  - Thales Paiva
  - Prasanna Ravi
  - Goutam Tamvada
* URL: https://kyberslash.cr.yp.to/papers.html
* Referenced from:
  - [nix/valgrind/README.md](nix/valgrind/README.md)

### `NIST_FAQ`

* Post-Quantum Cryptography FAQs
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/Projects/post-quantum-cryptography/faqs#Rdc7
* Referenced from:
  - [README.md](README.md)

### `NIST_FIPS204_SEC6`

* FIPS 204 Section 6 Guidance
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/csrc/media/Projects/post-quantum-cryptography/documents/faq/fips204-sec6-03192025.pdf
* Referenced from:
  - [README.md](README.md)

### `REF`

* CRYSTALS-Dilithium reference implementation
* Author(s):
  - Shi Bai
  - Léo Ducas
  - Eike Kiltz
  - Tancrède Lepoint
  - Vadim Lyubashevsky
  - Peter Schwabe
  - Gregor Seiler
  - Damien Stehlé
* URL: https://github.com/pq-crystals/dilithium/tree/master/ref
* Referenced from:
  - [README.md](README.md)
  - [mldsa/ntt.c](mldsa/ntt.c)
  - [mldsa/poly.c](mldsa/poly.c)
  - [mldsa/poly_kl.c](mldsa/poly_kl.c)

### `REF_AVX2`

* CRYSTALS-Dilithium optimized AVX2 implementation
* Author(s):
  - Shi Bai
  - Léo Ducas
  - Eike Kiltz
  - Tancrède Lepoint
  - Vadim Lyubashevsky
  - Peter Schwabe
  - Gregor Seiler
  - Damien Stehlé
* URL: https://github.com/pq-crystals/dilithium/tree/master/avx2
* Referenced from:
  - [mldsa/native/x86_64/src/align.h](mldsa/native/x86_64/src/align.h)
  - [mldsa/native/x86_64/src/consts.c](mldsa/native/x86_64/src/consts.c)
  - [mldsa/native/x86_64/src/consts.h](mldsa/native/x86_64/src/consts.h)
  - [mldsa/native/x86_64/src/intt.S](mldsa/native/x86_64/src/intt.S)
  - [mldsa/native/x86_64/src/ntt.S](mldsa/native/x86_64/src/ntt.S)
  - [mldsa/native/x86_64/src/nttunpack.S](mldsa/native/x86_64/src/nttunpack.S)
  - [mldsa/native/x86_64/src/pointwise.S](mldsa/native/x86_64/src/pointwise.S)
  - [mldsa/native/x86_64/src/pointwise_acc_l4.S](mldsa/native/x86_64/src/pointwise_acc_l4.S)
  - [mldsa/native/x86_64/src/pointwise_acc_l5.S](mldsa/native/x86_64/src/pointwise_acc_l5.S)
  - [mldsa/native/x86_64/src/pointwise_acc_l7.S](mldsa/native/x86_64/src/pointwise_acc_l7.S)
  - [mldsa/native/x86_64/src/poly_caddq_avx2.c](mldsa/native/x86_64/src/poly_caddq_avx2.c)
  - [mldsa/native/x86_64/src/poly_chknorm_avx2.c](mldsa/native/x86_64/src/poly_chknorm_avx2.c)
  - [mldsa/native/x86_64/src/poly_decompose_32_avx2.c](mldsa/native/x86_64/src/poly_decompose_32_avx2.c)
  - [mldsa/native/x86_64/src/poly_decompose_88_avx2.c](mldsa/native/x86_64/src/poly_decompose_88_avx2.c)
  - [mldsa/native/x86_64/src/poly_use_hint_32_avx2.c](mldsa/native/x86_64/src/poly_use_hint_32_avx2.c)
  - [mldsa/native/x86_64/src/poly_use_hint_88_avx2.c](mldsa/native/x86_64/src/poly_use_hint_88_avx2.c)
  - [mldsa/native/x86_64/src/polyz_unpack_17_avx2.c](mldsa/native/x86_64/src/polyz_unpack_17_avx2.c)
  - [mldsa/native/x86_64/src/polyz_unpack_19_avx2.c](mldsa/native/x86_64/src/polyz_unpack_19_avx2.c)
  - [mldsa/native/x86_64/src/rej_uniform_avx2.c](mldsa/native/x86_64/src/rej_uniform_avx2.c)
  - [mldsa/native/x86_64/src/rej_uniform_eta2_avx2.c](mldsa/native/x86_64/src/rej_uniform_eta2_avx2.c)
  - [mldsa/native/x86_64/src/rej_uniform_eta4_avx2.c](mldsa/native/x86_64/src/rej_uniform_eta4_avx2.c)

### `Round3_Spec`

* CRYSTALS-Dilithium Algorithm Specifications and Supporting Documentation (Version 3.1)
* Author(s):
  - Shi Bai
  - Léo Ducas
  - Eike Kiltz
  - Tancrède Lepoint
  - Vadim Lyubashevsky
  - Peter Schwabe
  - Gregor Seiler
  - Damien Stehlé
* URL: https://pq-crystals.org/dilithium/data/dilithium-specification-round3-20210208.pdf
* Referenced from:
  - [mldsa/sign.c](mldsa/sign.c)

### `libmceliece`

* libmceliece implementation of Classic McEliece
* Author(s):
  - Daniel J. Bernstein
  - Tung Chou
* URL: https://lib.mceliece.org/
* Referenced from:
  - [mldsa/ct.h](mldsa/ct.h)

### `m1cycles`

* Cycle counting on Apple M1
* Author(s):
  - Dougall Johnson
* URL: https://gist.github.com/dougallj/5bafb113492047c865c0c8cfbc930155#file-m1_robsize-c-L390
* Referenced from:
  - [test/hal/hal.c](test/hal/hal.c)

### `mupq`

* Common files for pqm4, pqm3, pqriscv
* Author(s):
  - Matthias J. Kannwischer
  - Richard Petri
  - Joost Rijneveld
  - Peter Schwabe
  - Ko Stoffelen
* URL: https://github.com/mupq/mupq
* Referenced from:
  - [mldsa/fips202/fips202.c](mldsa/fips202/fips202.c)
  - [mldsa/fips202/keccakf1600.c](mldsa/fips202/keccakf1600.c)

### `optblocker`

* PQC forum post on opt-blockers using volatile globals
* Author(s):
  - Daniel J. Bernstein
* URL: https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/hqbtIGFKIpU/m/H14H0wOlBgAJ
* Referenced from:
  - [mldsa/ct.h](mldsa/ct.h)

### `supercop`

* SUPERCOP benchmarking framework
* Author(s):
  - Daniel J. Bernstein
* URL: http://bench.cr.yp.to/supercop.html
* Referenced from:
  - [mldsa/fips202/fips202.c](mldsa/fips202/fips202.c)
  - [mldsa/fips202/keccakf1600.c](mldsa/fips202/keccakf1600.c)

### `surf`

* SURF: Simple Unpredictable Random Function
* Author(s):
  - Daniel J. Bernstein
* URL: https://cr.yp.to/papers.html#surf
* Referenced from:
  - [examples/basic/test_only_rng/notrandombytes.c](examples/basic/test_only_rng/notrandombytes.c)
  - [examples/basic/test_only_rng/notrandombytes.h](examples/basic/test_only_rng/notrandombytes.h)
  - [test/notrandombytes/notrandombytes.c](test/notrandombytes/notrandombytes.c)
  - [test/notrandombytes/notrandombytes.h](test/notrandombytes/notrandombytes.h)

### `tweetfips`

* 'tweetfips202' FIPS202 implementation
* Author(s):
  - Gilles Van Assche
  - Daniel J. Bernstein
  - Peter Schwabe
* URL: https://keccak.team/2015/tweetfips202.html
* Referenced from:
  - [mldsa/fips202/fips202.c](mldsa/fips202/fips202.c)
  - [mldsa/fips202/keccakf1600.c](mldsa/fips202/keccakf1600.c)
