# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = mld_attempt_signature_generation_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mld_attempt_signature_generation

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mldsa/sign.c

CHECK_FUNCTION_CONTRACTS=mld_attempt_signature_generation
USE_FUNCTION_CONTRACTS=mld_polyvecl_uniform_gamma1 \
                       mld_polyvecl_ntt \
                       mld_polyvec_matrix_pointwise_montgomery \
                       mld_polyveck_reduce \
                       mld_polyveck_invntt_tomont \
                       mld_polyveck_caddq \
                       mld_polyveck_decompose \
                       mld_polyveck_pack_w1 \
                       mld_H \
                       mld_poly_challenge \
                       mld_poly_ntt \
                       mld_polyvecl_pointwise_poly_montgomery \
                       mld_polyvecl_invntt_tomont \
                       mld_polyvecl_add \
                       mld_polyvecl_reduce \
                       mld_polyvecl_chknorm \
                       mld_polyveck_pointwise_poly_montgomery \
                       mld_polyveck_sub \
                       mld_polyveck_reduce \
                       mld_polyveck_chknorm \
                       mld_polyveck_add \
                       mld_polyveck_make_hint \
                       mld_pack_sig
USE_FUNCTION_CONTRACTS+=mld_zeroize

APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2
CBMCFLAGS += --slice-formula
CBMCFLAGS += --no-array-field-sensitivity

FUNCTION_NAME = mld_attempt_signature_generation

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

# This function is large enough to need...
CBMC_OBJECT_BITS = 11

# If you require access to a file-local ("static") function or object to conduct
# your proof, set the following (and do not include the original source file
# ("mldsa/poly.c") in PROJECT_SOURCES).
# REWRITTEN_SOURCES = $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i
# include ../Makefile.common
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_SOURCE = $(SRCDIR)/mldsa/poly.c
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_FUNCTIONS = foo bar
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_OBJECTS = baz
# Care is required with variables on the left-hand side: REWRITTEN_SOURCES must
# be set before including Makefile.common, but any use of variables on the
# left-hand side requires those variables to be defined. Hence, _SOURCE,
# _FUNCTIONS, _OBJECTS is set after including Makefile.common.

include ../Makefile.common
