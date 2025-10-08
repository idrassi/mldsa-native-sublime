# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean size
.DEFAULT_GOAL := all

# Append cross-prefix for cross compilation
# Remove or ignore for native builds
CC  ?= gcc
SIZE ?= size
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

ifeq (,$(findstring $(CROSS_PREFIX),$(SIZE)))
SIZE  := $(CROSS_PREFIX)$(SIZE)
endif

# Part A:
#
# mldsa-native source and header files
#
# If you are not concerned about minimizing for a specific backend,
# you can just include _all_ source files into your build.
MLD_SOURCE=$(wildcard                    \
	../../mldsa/*.c                      \
	../../mldsa/**/*.c                   \
	../../mldsa/**/**/*.c                \
	../../mldsa/**/**/**/*.c)

# Part B:
#
# Random number generator
#
# !!! WARNING !!!
#
# The randombytes() implementation used here is for TESTING ONLY.
# You MUST NOT use this implementation outside of testing.
#
# !!! WARNING !!!
RNG_SOURCE=$(wildcard test_only_rng/*.c)

# Part C:
#
# Your application source code
APP_SOURCE=$(wildcard *.c)

ALL_SOURCE=$(MLD_SOURCE) $(RNG_SOURCE) $(APP_SOURCE)

BUILD_DIR=build
BIN=test_binary

CFLAGS := \
	-Wall \
	-Wextra \
	-Werror \
	-Wmissing-prototypes \
	-Wshadow \
	-Werror \
	-Wpointer-arith \
	-Wredundant-decls \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
	$(CFLAGS)

# Use the default namespace prefix from config.h
# CFLAGS += -DMLD_CONFIG_NAMESPACE_PREFIX=mldsa

BINARY_NAME_FULL_44=$(BUILD_DIR)/$(BIN)44
BINARY_NAME_FULL_65=$(BUILD_DIR)/$(BIN)65
BINARY_NAME_FULL_87=$(BUILD_DIR)/$(BIN)87
BINARIES_FULL=$(BINARY_NAME_FULL_44) $(BINARY_NAME_FULL_65) $(BINARY_NAME_FULL_87)

$(BINARY_NAME_FULL_44): CFLAGS += -DMLD_CONFIG_PARAMETER_SET=44
$(BINARY_NAME_FULL_65): CFLAGS += -DMLD_CONFIG_PARAMETER_SET=65
$(BINARY_NAME_FULL_87): CFLAGS += -DMLD_CONFIG_PARAMETER_SET=87

$(BINARIES_FULL): $(ALL_SOURCE)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) $^ -o $@

all: build size

build: $(BINARIES_FULL)

run: $(BINARIES_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_44)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_65)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_87)

size: build
	@echo "=== Size info for $(BINARY_NAME_FULL_44) ==="
	@$(SIZE) $(BINARY_NAME_FULL_44)
	@echo "=== Size info for $(BINARY_NAME_FULL_65) ==="
	@$(SIZE) $(BINARY_NAME_FULL_65)
	@echo "=== Size info for $(BINARY_NAME_FULL_87) ==="
	@$(SIZE) $(BINARY_NAME_FULL_87)

clean:
	rm -rf $(BUILD_DIR)
