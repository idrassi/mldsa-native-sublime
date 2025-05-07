# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

######
# To run, see the README.md file
######
.PHONY: all clean

# ISA to optimize for
TARGET_ISA=Arm_AArch64

# MicroArch target to optimize for
TARGET_MICROARCH=Arm_Cortex_A55

SLOTHY_EXTRA_FLAGS ?=

SLOTHY_FLAGS=-c sw_pipelining.enabled=true \
             -c inputs_are_outputs \
             -c sw_pipelining.minimize_overlapping=False \
             -c sw_pipelining.allow_post \
             -c variable_size \
             -c constraints.stalls_first_attempt=64 \
             -c timeout=120 \
             $(SLOTHY_EXTRA_FLAGS)

# For kernels which stash callee-saved v8-v15 but don't stash callee-saved GPRs x19-x30. 
# Allow SLOTHY to use all V-registers, but only caller-saved GPRs.
RESERVE_X_ONLY_FLAG=-c reserved_regs="[x18--x30,sp]"

# Used for kernels which don't stash callee-saved registers.
# Restrict SLOTHY to caller-saved registers.
RESERVE_ALL_FLAG=-c reserved_regs="[x18--x30,sp,v8--v15]"

all: ntt.S 

# These units explicitly save and restore registers v8-v15, so SLOTHY can freely use
# those registers.
ntt.S: ../../../../dev/aarch64_clean/src/ntt.S
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l layer123_start -l layer45678_start $(SLOTHY_FLAGS) $(RESERVE_X_ONLY_FLAG)

clean:
	-$(RM) -rf *.S
