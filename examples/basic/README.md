[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Building mldsa-native

This directory contains a minimal example for how to build mldsa-native.

## Components

An application using mldsa-native as-is needs to include the following components:

1. mldsa-native source tree, including [`mldsa/`](../../mldsa) and [`mldsa/fips202/`](../../mldsa/fips202).
2. A secure pseudo random number generator, implementing [`randombytes.h`](../../mldsa/randombytes.h).
3. The application source code

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.

## Usage

Build this example with `make build`, run with `make run`.

## What this example demonstrates

This basic example shows how to use the ML-DSA (Module-Lattice-Based Digital Signature Algorithm) for:

1. **Key Generation**: Generate a public/private key pair
2. **Signing**: Sign a message with a private key and optional context
3. **Signature Verification**: Verify a signature using the public key
4. **Signed Messages**: Create and open signed messages (signature + message combined)

The example demonstrates both the detached signature API (`crypto_sign_signature`/`crypto_sign_verify`) and the combined signature API (`crypto_sign`/`crypto_sign_open`).

## Parameter Sets

ML-DSA supports three parameter sets:
- **ML-DSA-44**
- **ML-DSA-65**
- **ML-DSA-87**

The example builds and runs all three parameter sets to demonstrate the different security levels and their corresponding key/signature sizes.
