# Copyright lowRISC contributors.
# Copyright 2024 University of Oxford, see also CREDITS.md.
# Licensed under the Apache License, Version 2.0 (see LICENSE for details).
# Original Author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0
#
# kudu-fv: the "sv" target of cheriot-ibex dv/formal/Makefile, pointed at the
# kudu-fv port of CHERIoT-Platform/cheriot-sail (dii-read-from-file).
# Run from this directory; the output goes to ./build/ (as in cheriot-ibex),
# because the post-processing scripts use the relative path build/ibexspec.sv.

SAIL ?= sail

LOWRISC_CHERIOT_SAIL_SRC ?= $(abspath ../cheriot-sail)
SAIL_RISCV_MODEL_DIR = $(LOWRISC_CHERIOT_SAIL_SRC)/sail-riscv/model
# Relative to SAIL_RISCV_MODEL_DIR (Sources.mk prefixes every file with it).
CHERI = ../../src

include Sources.mk

COMPRESSED_INSTRS=C_J C_JALR C_LW C_ADDIW C_LI C_ANDI C_BEQZ C_LD C_ILLEGAL C_AND C_JAL C_MV C_XOR \
					C_CSC C_CIncAddr16CSP C_ADD C_CSCSP C_EBREAK C_CLC C_SDSP C_ADDI4SPN C_CJR C_SW C_SUB \
					C_SWSP C_SRLI C_LDSP C_SD C_SRAI C_LUI C_OR C_SUBW C_CIncAddr4CSPN C_JR C_CJALR C_ADDI \
					C_ADDW C_BNEZ C_ADDI16SP C_NOP C_CJAL C_SLLI C_CLCSP

SAIL_EXTRA_SRCS = $(abspath spec/main.sail)

SAIL_UNREACHABLE=translate lookup_TLB translate_tlb_miss translate_tlb_hit pt_walk
SAIL_UNREACHABLE+=pmpReadCfgReg pmpReadAddrReg pmpWriteCfg pmpWriteCfgReg pmpWriteAddr pmpWriteAddrReg mseccfgWrite
SAIL_UNREACHABLE+=pmpAddrRange pmpCheckRWX pmpCheckPerms pmpMatchAddr pmpMatchEntry accessToFault

# zz8operatorz0zI_uz9 (operator <_u) is needed by encCapabilityToCapability since upstream 087d07f (implicit T).
SAIL_EXTRACTED=encCapabilityToCapability capToEncCap bit_to_bool bool_to_bit to_bits zero_extend capBitsToCapability capBitsToEncCapability zz8operatorz0zI_uz9
SAIL_CULL=count_trailing_zeros

SAIL_SV_FLAGS=-sv -sv-comb -sv-inregs -sv-outregs -sv-nostrings -sv-nopacked -sv-nomem -sv-unroll-loops 32 -Oconstant_fold -memo-z3 \
	$(addprefix -sv-unreachable ,$(SAIL_UNREACHABLE)) \
	-sv-fun2wires 2:read_ram \
	-sv-fun2wires 2:write_ram \
	-sv-fun2wires wX \
	-sv-fun2wires wC \
	-sv-fun2wires __WriteRAM_Meta \
	-sv-fun2wires __ReadRAM_Meta \
	-sv-fun2wires mem_read_cap_revoked \
	-sv-fun2wires match_reservation

.DEFAULT_GOAL := sv

.PHONY: sv
sv:
	mkdir -p build
	cd build && $(SAIL) $(SAIL_SRCS) $(SAIL_EXTRA_SRCS) $(SAIL_SV_FLAGS) $(addprefix -sv_unreachable execute_,$(COMPRESSED_INSTRS)) -o ibexspec
	python3 spec/fix_pmp_bug.py
	python3 spec/unreachable_loc_info.py
	python3 spec/extract_funcs.py $(SAIL_EXTRACTED) > build/extracted.sv
	python3 spec/cull_funcs.py $(SAIL_CULL)

.PHONY: clean
clean:
	rm -rf build/
