/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLD_API_H
#define MLD_API_H

#include <stddef.h>
#include <stdint.h>
#include "common.h"

#define MLD_44_PUBLICKEYBYTES 1312
#define MLD_44_SECRETKEYBYTES 2560
#define MLD_44_BYTES 2420

#define MLD_65_PUBLICKEYBYTES 1952
#define MLD_65_SECRETKEYBYTES 4032
#define MLD_65_BYTES 3309

#define MLD_87_PUBLICKEYBYTES 2592
#define MLD_87_SECRETKEYBYTES 4896
#define MLD_87_BYTES 4627


#if MLD_CONFIG_PARAMETER_SET == 44
#define CRYPTO_PUBLICKEYBYTES MLD_44_PUBLICKEYBYTES
#define CRYPTO_SECRETKEYBYTES MLD_44_SECRETKEYBYTES
#define CRYPTO_BYTES MLD_44_BYTES
#elif MLD_CONFIG_PARAMETER_SET == 65
#define CRYPTO_PUBLICKEYBYTES MLD_65_PUBLICKEYBYTES
#define CRYPTO_SECRETKEYBYTES MLD_65_SECRETKEYBYTES
#define CRYPTO_BYTES MLD_65_BYTES
#elif MLD_CONFIG_PARAMETER_SET == 87
#define CRYPTO_PUBLICKEYBYTES MLD_87_PUBLICKEYBYTES
#define CRYPTO_SECRETKEYBYTES MLD_87_SECRETKEYBYTES
#define CRYPTO_BYTES MLD_87_BYTES
#endif

#define crypto_sign_keypair MLD_NAMESPACE_K(keypair)
#define crypto_sign_signature MLD_NAMESPACE_K(signature)
#define crypto_sign MLD_NAMESPACE_K(sign)
#define crypto_sign_verify MLD_NAMESPACE_K(verify)
#define crypto_sign_open MLD_NAMESPACE_K(open)


#endif /* !MLD_API_H */
