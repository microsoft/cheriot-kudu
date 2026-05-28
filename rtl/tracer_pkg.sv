// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package tracer_pkg;
  import cheri_pkg::*;
  import super_pkg::*;
  import csr_pkg::*;

  parameter logic [1:0] OPCODE_C0 = 2'b00;
  parameter logic [1:0] OPCODE_C1 = 2'b01;
  parameter logic [1:0] OPCODE_C2 = 2'b10;

  // instruction masks (for tracer)
  parameter logic [31:0] INSN_LUI     = { 25'h?,                           {OPCODE_LUI  } };
  parameter logic [31:0] INSN_AUIPC   = { 25'h?,                           {OPCODE_AUIPC} };
  parameter logic [31:0] INSN_JAL     = { 25'h?,                           {OPCODE_JAL  } };
  parameter logic [31:0] INSN_JALR    = { 17'h?,             3'b000, 5'h?, {OPCODE_JALR } };

  // BRANCH
  parameter logic [31:0] INSN_BEQ     = { 17'h?,             3'b000, 5'h?, {OPCODE_BRANCH} };
  parameter logic [31:0] INSN_BNE     = { 17'h?,             3'b001, 5'h?, {OPCODE_BRANCH} };
  parameter logic [31:0] INSN_BLT     = { 17'h?,             3'b100, 5'h?, {OPCODE_BRANCH} };
  parameter logic [31:0] INSN_BGE     = { 17'h?,             3'b101, 5'h?, {OPCODE_BRANCH} };
  parameter logic [31:0] INSN_BLTU    = { 17'h?,             3'b110, 5'h?, {OPCODE_BRANCH} };
  parameter logic [31:0] INSN_BGEU    = { 17'h?,             3'b111, 5'h?, {OPCODE_BRANCH} };

  // OPIMM
  parameter logic [31:0] INSN_ADDI    = { 17'h?,             3'b000, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SLTI    = { 17'h?,             3'b010, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SLTIU   = { 17'h?,             3'b011, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_XORI    = { 17'h?,             3'b100, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORI     = { 17'h?,             3'b110, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ANDI    = { 17'h?,             3'b111, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SLLI    = { 7'b0000000, 10'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SRLI    = { 7'b0000000, 10'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SRAI    = { 7'b0100000, 10'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

  // OP
  parameter logic [31:0] INSN_ADD     = { 7'b0000000, 10'h?, 3'b000, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SUB     = { 7'b0100000, 10'h?, 3'b000, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SLL     = { 7'b0000000, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SLT     = { 7'b0000000, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SLTU    = { 7'b0000000, 10'h?, 3'b011, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_XOR     = { 7'b0000000, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SRL     = { 7'b0000000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SRA     = { 7'b0100000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_OR      = { 7'b0000000, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_AND     = { 7'b0000000, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };

  // SYSTEM
  parameter logic [31:0] INSN_CSRRW   = { 17'h?,             3'b001, 5'h?, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_CSRRS   = { 17'h?,             3'b010, 5'h?, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_CSRRC   = { 17'h?,             3'b011, 5'h?, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_CSRRWI  = { 17'h?,             3'b101, 5'h?, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_CSRRSI  = { 17'h?,             3'b110, 5'h?, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_CSRRCI  = { 17'h?,             3'b111, 5'h?, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_ECALL   = { 12'b000000000000,         13'b0, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_EBREAK  = { 12'b000000000001,         13'b0, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_MRET    = { 12'b001100000010,         13'b0, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_DRET    = { 12'b011110110010,         13'b0, {OPCODE_SYSTEM} };
  parameter logic [31:0] INSN_WFI     = { 12'b000100000101,         13'b0, {OPCODE_SYSTEM} };

  // RV32M
  parameter logic [31:0] INSN_DIV     = { 7'b0000001, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_DIVU    = { 7'b0000001, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_REM     = { 7'b0000001, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_REMU    = { 7'b0000001, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PMUL    = { 7'b0000001, 10'h?, 3'b000, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PMUH    = { 7'b0000001, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PMULHSU = { 7'b0000001, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PMULHU  = { 7'b0000001, 10'h?, 3'b011, 5'h?, {OPCODE_OP} };

  // RV32B
  // ZBA
  parameter logic [31:0] INSN_SH1ADD = { 7'b0010000, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SH2ADD = { 7'b0010000, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SH3ADD = { 7'b0010000, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };

  // ZBB
  // Only log2(XLEN) bits of the immediate are used. For RV32, this means only the bits in
  // instr[24:20] are effectively used. Whenever instr[26] is set, sroi/rori is instead decoded as
  // fsri.
  parameter logic [31:0] INSN_RORI = { 5'b01100  , 1'b0, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CLZ  = { 12'b011000000000, 5'h?,  3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CTZ  = { 12'b011000000001, 5'h?,  3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CPOP = { 12'b011000000010, 5'h?,  3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SEXTB = { 12'b011000000100, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_SEXTH = { 12'b011000000101, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };

  // The zext.h and zext.b pseudo-instructions are defined in the ratified v.1.0.0 and draft v.0.94
  // specifications of the bitmanip extension, respectively. They are currently not emitted by the
  // tracer due to a lack of support in the LLVM and GCC toolchains. Enabling this functionality
  // when the time is right is tracked in https://github.com/lowRISC/ibex/issues/1228
  // zext.b -- pseudo-instruction: andi rd, rs 255
  // parameter logic [31:0] INSN_ZEXTB =
  //     { 4'b0000, 8'b11111111, 5'h?, 3'b111, 5'h?, {OPCODE_OP_IMM} };
  // zext.h -- pseudo-instruction: pack rd, rs zero
  // parameter logic [31:0] INSN_ZEXTH = { 7'b0000100, 5'b00000, 5'h?, 3'b100, 5'h?, {OPCODE_OP} };

  parameter logic [31:0] INSN_ROL   = { 7'b0110000, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_ROR   = { 7'b0110000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_MIN   = { 7'b0000101, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_MAX   = { 7'b0000101, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_MINU  = { 7'b0000101, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_MAXU  = { 7'b0000101, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_XNOR  = { 7'b0100000, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_ORN   = { 7'b0100000, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_ANDN  = { 7'b0100000, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PACK  = { 7'b0000100, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PACKU = { 7'b0100100, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_PACKH = { 7'b0000100, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };

  // ZBS
  parameter logic [31:0] INSN_BCLRI = { 5'b01001, 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_BSETI = { 5'b00101, 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_BINVI = { 5'b01101, 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  // Only log2(XLEN) bits of the immediate are used. For RV32, this means only the bits in
  // instr[24:20] are effectively used. Whenever instr[26] is set, bexti is instead decoded as fsri.
  parameter logic [31:0] INSN_BEXTI = { 5'b01001, 1'b0, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

  parameter logic [31:0] INSN_BCLR = { 7'b0100100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_BSET = { 7'b0010100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_BINV = { 7'b0110100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_BEXT = { 7'b0100100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };

  // ZBP
  // grevi
  // Only log2(XLEN) bits of the immediate are used. For RV32, this means only the bits in
  // instr[24:20] are effectively used. Whenever instr[26] is set, grevi is instead decoded as fsri.
  parameter logic [31:0] INSN_GREVI = { 5'b01101, 1'b0, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  // grevi -- pseudo-instructions
  parameter logic [31:0] INSN_REV_P =
      { 5'b01101, 1'b0, 1'b?, 5'b00001, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV2_N =
      { 5'b01101, 1'b0, 1'b?, 5'b00010, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV_N =
      { 5'b01101, 1'b0, 1'b?, 5'b00011, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV4_B =
      { 5'b01101, 1'b0, 1'b?, 5'b00100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV2_B =
      { 5'b01101, 1'b0, 1'b?, 5'b00110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV_B =
      { 5'b01101, 1'b0, 1'b?, 5'b00111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV8_H =
      { 5'b01101, 1'b0, 1'b?, 5'b01000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV4_H =
      { 5'b01101, 1'b0, 1'b?, 5'b01100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV2_H =
      { 5'b01101, 1'b0, 1'b?, 5'b01110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV_H =
      { 5'b01101, 1'b0, 1'b?, 5'b01111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV16 =
      { 5'b01101, 1'b0, 1'b?, 5'b10000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV8 =
      { 5'b01101, 1'b0, 1'b?, 5'b11000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV4 =
      { 5'b01101, 1'b0, 1'b?, 5'b11100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV2 =
      { 5'b01101, 1'b0, 1'b?, 5'b11110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_REV =
      { 5'b01101, 1'b0, 1'b?, 5'b11111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  // gorci
  // Only log2(XLEN) bits of the immediate are used. For RV32, this means only the bits in
  // instr[24:20] are effectively used. Whenever instr[26] is set, gorci is instead decoded as fsri.
  parameter logic [31:0] INSN_GORCI = { 5'b00101, 1'b0, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  // gorci -- pseudo-instructions
  parameter logic [31:0] INSN_ORC_P =
      { 5'b00101, 1'b0, 1'b?, 5'b00001, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC2_N =
      { 5'b00101, 1'b0, 1'b?, 5'b00010, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC_N =
      { 5'b00101, 1'b0, 1'b?, 5'b00011, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC4_B =
      { 5'b00101, 1'b0, 1'b?, 5'b00100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC2_B =
      { 5'b00101, 1'b0, 1'b?, 5'b00110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC_B =
      { 5'b00101, 1'b0, 1'b?, 5'b00111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC8_H =
      { 5'b00101, 1'b0, 1'b?, 5'b01000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC4_H =
      { 5'b00101, 1'b0, 1'b?, 5'b01100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC2_H =
      { 5'b00101, 1'b0, 1'b?, 5'b01110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC_H =
      { 5'b00101, 1'b0, 1'b?, 5'b01111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC16 =
      { 5'b00101, 1'b0, 1'b?, 5'b10000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC8 =
      { 5'b00101, 1'b0, 1'b?, 5'b11000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC4 =
      { 5'b00101, 1'b0, 1'b?, 5'b11100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC2 =
      { 5'b00101, 1'b0, 1'b?, 5'b11110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ORC =
      { 5'b00101, 1'b0, 1'b?, 5'b11111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  // shfli
  parameter logic [31:0] INSN_SHFLI = { 6'b000010, 11'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  // shfli -- pseudo-instructions
  parameter logic [31:0] INSN_ZIP_N =
      { 6'b000010, 2'h?, 4'b0001, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP2_B =
      { 6'b000010, 2'h?, 4'b0010, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP_B =
      { 6'b000010, 2'h?, 4'b0011, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP4_H =
      { 6'b000010, 2'h?, 4'b0100, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP2_H =
      { 6'b000010, 2'h?, 4'b0110, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP_H =
      { 6'b000010, 2'h?, 4'b0111, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP8 =
      { 6'b000010, 2'h?, 4'b1000, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP4 =
      { 6'b000010, 2'h?, 4'b1100, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP2 =
      { 6'b000010, 2'h?, 4'b1110, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_ZIP =
      { 6'b000010, 2'h?, 4'b1111, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  // unshfli
  parameter logic [31:0] INSN_UNSHFLI = { 6'b000010, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  // unshfli -- pseudo-instructions
  parameter logic [31:0] INSN_UNZIP_N =
      { 6'b000010, 2'h?, 4'b0001, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP2_B =
      { 6'b000010, 2'h?, 4'b0010, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP_B =
      { 6'b000010, 2'h?, 4'b0011, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP4_H =
      { 6'b000010, 2'h?, 4'b0100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP2_H =
      { 6'b000010, 2'h?, 4'b0110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP_H =
      { 6'b000010, 2'h?, 4'b0111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP8 =
      { 6'b000010, 2'h?, 4'b1000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP4 =
      { 6'b000010, 2'h?, 4'b1100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP2 =
      { 6'b000010, 2'h?, 4'b1110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_UNZIP =
      { 6'b000010, 2'h?, 4'b1111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

  parameter logic [31:0] INSN_GREV   = { 7'b0110100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_GORC   = { 7'b0010100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SHFL   = { 7'b0000100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_UNSHFL = { 7'b0000100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };

  parameter logic [31:0] INSN_XPERM_N = { 7'b0010100, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_XPERM_B = { 7'b0010100, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_XPERM_H = { 7'b0010100, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };

  parameter logic [31:0] INSN_SLO    = { 7'b0010000, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SRO    = { 7'b0010000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_SLOI   = { 5'b00100        , 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  // Only log2(XLEN) bits of the immediate are used. For RV32, this means only the bits in
  // instr[24:20] are effectively used. Whenever instr[26] is set, sroi/rori is instead decoded as
  // fsri.
  parameter logic [31:0] INSN_SROI   = { 5'b00100  , 1'b0, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

  // ZBE
  parameter logic [31:0] INSN_BDECOMPRESS = {7'b0100100, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_BCOMPRESS   = {7'b0000100, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };

  // ZBT
  parameter logic [31:0] INSN_FSRI = { 5'h?, 1'b1, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

  parameter logic [31:0] INSN_CMIX = {5'h?, 2'b11, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_CMOV = {5'h?, 2'b11, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_FSL  = {5'h?, 2'b10, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_FSR  = {5'h?, 2'b10, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };

  // ZBF
  parameter logic [31:0] INSN_BFP  = {7'b0100100, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };

  // ZBC
  parameter logic [31:0] INSN_CLMUL  = {7'b0000101, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_CLMULR = {7'b0000101, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
  parameter logic [31:0] INSN_CLMULH = {7'b0000101, 10'h?, 3'b011, 5'h?, {OPCODE_OP} };

  // ZBR
  parameter logic [31:0] INSN_CRC32_B  =
      {7'b0110000, 5'b10000, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CRC32_H  =
      {7'b0110000, 5'b10001, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CRC32_W  =
      {7'b0110000, 5'b10010, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CRC32C_B =
      {7'b0110000, 5'b11000, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CRC32C_H =
      {7'b0110000, 5'b11001, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
  parameter logic [31:0] INSN_CRC32C_W =
      {7'b0110000, 5'b11010, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };

  // LOAD & STORE
  parameter logic [31:0] INSN_LOAD    = {25'h?,                            {OPCODE_LOAD } };
  parameter logic [31:0] INSN_STORE   = {25'h?,                            {OPCODE_STORE} };

  // MISC-MEM
  parameter logic [31:0] INSN_FENCE   = { 17'h?,             3'b000, 5'h?, {OPCODE_MISC_MEM} };
  parameter logic [31:0] INSN_FENCEI  = { 17'h0,             3'b001, 5'h0, {OPCODE_MISC_MEM} };

  // Compressed Instructions
  // C0
  parameter logic [15:0] INSN_CADDI4SPN  = { 3'b000,       11'h?,                    {OPCODE_C0} };
  parameter logic [15:0] INSN_CLW        = { 3'b010,       11'h?,                    {OPCODE_C0} };
  parameter logic [15:0] INSN_CSW        = { 3'b110,       11'h?,                    {OPCODE_C0} };
  parameter logic [15:0] INSN_CCLC       = { 3'b011,       11'h?,                    {OPCODE_C0} };
  parameter logic [15:0] INSN_CCSC       = { 3'b111,       11'h?,                    {OPCODE_C0} };

  // C1
  parameter logic [15:0] INSN_CADDI      = { 3'b000,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CJAL       = { 3'b001,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CJ         = { 3'b101,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CLI        = { 3'b010,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CLUI       = { 3'b011,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CBEQZ      = { 3'b110,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CBNEZ      = { 3'b111,       11'h?,                    {OPCODE_C1} };
  parameter logic [15:0] INSN_CSRLI      = { 3'b100, 1'h?, 2'b00, 8'h?,              {OPCODE_C1} };
  parameter logic [15:0] INSN_CSRAI      = { 3'b100, 1'h?, 2'b01, 8'h?,              {OPCODE_C1} };
  parameter logic [15:0] INSN_CANDI      = { 3'b100, 1'h?, 2'b10, 8'h?,              {OPCODE_C1} };
  parameter logic [15:0] INSN_CSUB       = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b00, 3'h?, {OPCODE_C1} };
  parameter logic [15:0] INSN_CXOR       = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b01, 3'h?, {OPCODE_C1} };
  parameter logic [15:0] INSN_COR        = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b10, 3'h?, {OPCODE_C1} };
  parameter logic [15:0] INSN_CAND       = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b11, 3'h?, {OPCODE_C1} };

  // C2
  parameter logic [15:0] INSN_CSLLI      = { 3'b000,       11'h?,                    {OPCODE_C2} };
  parameter logic [15:0] INSN_CLWSP      = { 3'b010,       11'h?,                    {OPCODE_C2} };
  parameter logic [15:0] INSN_SWSP       = { 3'b110,       11'h?,                    {OPCODE_C2} };
  parameter logic [15:0] INSN_CMV        = { 3'b100, 1'b0, 10'h?,                    {OPCODE_C2} };
  parameter logic [15:0] INSN_CADD       = { 3'b100, 1'b1, 10'h?,                    {OPCODE_C2} };
  parameter logic [15:0] INSN_CEBREAK    = { 3'b100, 1'b1,        5'h0,  5'h0,       {OPCODE_C2} };
  parameter logic [15:0] INSN_CJR        = { 3'b100, 1'b0,        5'h0,  5'h0,       {OPCODE_C2} };
  parameter logic [15:0] INSN_CJALR      = { 3'b100, 1'b1,        5'h?,  5'h0,       {OPCODE_C2} };
  parameter logic [15:0] INSN_CCLCSP     = { 3'b011,       11'h?,                    {OPCODE_C2} };  // FLWSP
  parameter logic [15:0] INSN_CCSCSP     = { 3'b111,       11'h?,                    {OPCODE_C2} };  // FSWSP

  // 32-bit CHERI instructions
  parameter logic [31:0] INSN_CHGETPERM    = {7'h7f, 5'h0, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETTYPE    = {7'h7f, 5'h1, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETBASE    = {7'h7f, 5'h2, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETHIGH    = {7'h7f, 5'h17, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETTOP     = {7'h7f, 5'h18, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETLEN     = {7'h7f, 5'h3, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETTAG     = {7'h7f, 5'h4, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETSEALED  = {7'h7f, 5'h5, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHGETADDR    = {7'h7f, 5'hf, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };

  parameter logic [31:0] INSN_CHSEAL          = {7'h0b, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHUNSEAL        = {7'h0c, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHANDPERM       = {7'h0d, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETADDR       = {7'h10, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHINCADDR       = {7'h11, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHINCADDRIMM    = {12'h?, 5'h?,  3'b001, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETBOUNDS     = {7'h08, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETBOUNDSEX   = {7'h09, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETBOUNDSRNDN = {7'h0a, 10'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETBOUNDSIMM  = {12'h?, 5'h?,  3'b010, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHCLEARTAG      = {7'h7f, 5'hb, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHCRRL          = {7'h7f, 5'h8, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHCRAM          = {7'h7f, 5'h9, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };

  parameter logic [31:0] INSN_CHSUB      = {7'h14, 5'h?, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHMOVE     = {7'h7f, 5'ha, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHTESTSUB  = {7'h20, 5'h?, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETEQUAL = {7'h21, 5'h?, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_CHSETHIGH  = {7'h16, 5'h?, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };

  parameter logic [31:0] INSN_CHJALR   = {7'h7f, 5'hc, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };

  parameter logic [31:0] INSN_CHCSRRW = {7'h01, 5'h?, 5'h?, 3'b000, 5'h?, {OPCODE_CHERI} };
  parameter logic [31:0] INSN_AUICGP  = { 25'h?,                          {OPCODE_AUICGP} };

  // RV32 A extentions
  parameter logic [31:0] INSN_LR       = {5'h2,  2'b??, 5'h0, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_SC       = {5'h3,  2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOSWAP  = {5'h1,  2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOADD   = {5'h0,  2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOXOR   = {5'h4,  2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOAND   = {5'hc,  2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOOR    = {5'h8,  2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOMIN   = {5'h10, 2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOMAX   = {5'h14, 2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOMINU  = {5'h18, 2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };
  parameter logic [31:0] INSN_AMOMAXU  = {5'h1c, 2'b??, 5'h?, 5'h?, 3'b010,  5'h?, {OPCODE_AMO} };

  localparam logic [9:0] RS1 = (1 << 0);
  localparam logic [9:0] RS2 = (1 << 1);
  localparam logic [9:0] RS3 = (1 << 2);
  localparam logic [9:0] RD  = (1 << 3);
  localparam logic [9:0] MEM = (1 << 4);
  localparam logic [9:0] CS1 = (1 << 5);
  localparam logic [9:0] CS2 = (1 << 6);
  localparam logic [9:0] CD  = (1 << 7);
  localparam logic [9:0] MEMC = (1 << 8);
  localparam logic [9:0] MEM2 = (1 << 9);

  typedef struct packed {
    logic            valid;
    logic [63:0]     order;
    logic [31:0]     insn;
    logic            trap;
    logic            halt;
    logic            intr;
    logic [ 1:0]     mode;
    logic [ 1:0]     ixl;
    logic [ 4:0]     rs1_addr;
    logic [ 4:0]     rs2_addr;
    logic [ 4:0]     rs3_addr;
    logic [RegW-1:0] rs1_rdata;
    logic [RegW-1:0] rs2_rdata;
    logic [RegW-1:0] rs3_rdata;
    logic [ 4:0]     rd_addr;
    logic [RegW-1:0] rd_wdata;
    logic [31:0]     pc_rdata;
    logic [31:0]     pc_wdata;
    logic [31:0]     mem_addr;
    logic [ 3:0]     mem_rmask;
    logic [ 3:0]     mem_wmask;
    logic [RegW-1:0] mem_rdata;
    logic [MemW-1:0] mem_wdata;
    logic            mem_is_cap;
  } rvfi_t;


  // Format register address with "x" prefix, left-aligned to a fixed width of 3 characters.
  function automatic string reg_addr_to_str(input logic [4:0] addr);
    if (addr < 10) begin
      return $sformatf(" x%0d", addr);
    end else begin
      return $sformatf("x%0d", addr);
    end
  endfunction

  // Get a SCR name for a CHERI SCR address.
  function automatic string get_scr_name(input logic [4:0] scr_addr);
    unique case (scr_addr)
      5'd27:   return "ztopc";
      5'd28:   return "mtcc";
      5'd29:   return "mtdc";
      5'd30:   return "mscratchc";
      5'd31:   return "mepcc";
      default: return $sformatf("scr%d", scr_addr);
    endcase
  endfunction

  // Get a CSR name for a CSR address.
  function automatic string get_csr_name(input logic [11:0] csr_addr);
    unique case (csr_addr)
      12'd0: return "ustatus";
      12'd4: return "uie";
      12'd5: return "utvec";
      12'd64: return "uscratch";
      12'd65: return "uepc";
      12'd66: return "ucause";
      12'd67: return "utval";
      12'd68: return "uip";
      12'd1: return "fflags";
      12'd2: return "frm";
      12'd3: return "fcsr";
      12'd3072: return "cycle";
      12'd3073: return "time";
      12'd3074: return "instret";
      12'd3075: return "hpmcounter3";
      12'd3076: return "hpmcounter4";
      12'd3077: return "hpmcounter5";
      12'd3078: return "hpmcounter6";
      12'd3079: return "hpmcounter7";
      12'd3080: return "hpmcounter8";
      12'd3081: return "hpmcounter9";
      12'd3082: return "hpmcounter10";
      12'd3083: return "hpmcounter11";
      12'd3084: return "hpmcounter12";
      12'd3085: return "hpmcounter13";
      12'd3086: return "hpmcounter14";
      12'd3087: return "hpmcounter15";
      12'd3088: return "hpmcounter16";
      12'd3089: return "hpmcounter17";
      12'd3090: return "hpmcounter18";
      12'd3091: return "hpmcounter19";
      12'd3092: return "hpmcounter20";
      12'd3093: return "hpmcounter21";
      12'd3094: return "hpmcounter22";
      12'd3095: return "hpmcounter23";
      12'd3096: return "hpmcounter24";
      12'd3097: return "hpmcounter25";
      12'd3098: return "hpmcounter26";
      12'd3099: return "hpmcounter27";
      12'd3100: return "hpmcounter28";
      12'd3101: return "hpmcounter29";
      12'd3102: return "hpmcounter30";
      12'd3103: return "hpmcounter31";
      12'd3200: return "cycleh";
      12'd3201: return "timeh";
      12'd3202: return "instreth";
      12'd3203: return "hpmcounter3h";
      12'd3204: return "hpmcounter4h";
      12'd3205: return "hpmcounter5h";
      12'd3206: return "hpmcounter6h";
      12'd3207: return "hpmcounter7h";
      12'd3208: return "hpmcounter8h";
      12'd3209: return "hpmcounter9h";
      12'd3210: return "hpmcounter10h";
      12'd3211: return "hpmcounter11h";
      12'd3212: return "hpmcounter12h";
      12'd3213: return "hpmcounter13h";
      12'd3214: return "hpmcounter14h";
      12'd3215: return "hpmcounter15h";
      12'd3216: return "hpmcounter16h";
      12'd3217: return "hpmcounter17h";
      12'd3218: return "hpmcounter18h";
      12'd3219: return "hpmcounter19h";
      12'd3220: return "hpmcounter20h";
      12'd3221: return "hpmcounter21h";
      12'd3222: return "hpmcounter22h";
      12'd3223: return "hpmcounter23h";
      12'd3224: return "hpmcounter24h";
      12'd3225: return "hpmcounter25h";
      12'd3226: return "hpmcounter26h";
      12'd3227: return "hpmcounter27h";
      12'd3228: return "hpmcounter28h";
      12'd3229: return "hpmcounter29h";
      12'd3230: return "hpmcounter30h";
      12'd3231: return "hpmcounter31h";
      12'd256: return "sstatus";
      12'd258: return "sedeleg";
      12'd259: return "sideleg";
      12'd260: return "sie";
      12'd261: return "stvec";
      12'd262: return "scounteren";
      12'd320: return "sscratch";
      12'd321: return "sepc";
      12'd322: return "scause";
      12'd323: return "stval";
      12'd324: return "sip";
      12'd384: return "satp";
      12'd3857: return "mvendorid";
      12'd3858: return "marchid";
      12'd3859: return "mimpid";
      12'd3860: return "mhartid";
      12'd768: return "mstatus";
      12'd769: return "misa";
      12'd770: return "medeleg";
      12'd771: return "mideleg";
      12'd772: return "mie";
      12'd773: return "mtvec";
      12'd774: return "mcounteren";
      12'd832: return "mscratch";
      12'd833: return "mepc";
      12'd834: return "mcause";
      12'd835: return "mtval";
      12'd836: return "mip";
      12'd928: return "pmpcfg0";
      12'd929: return "pmpcfg1";
      12'd930: return "pmpcfg2";
      12'd931: return "pmpcfg3";
      12'd944: return "pmpaddr0";
      12'd945: return "pmpaddr1";
      12'd946: return "pmpaddr2";
      12'd947: return "pmpaddr3";
      12'd948: return "pmpaddr4";
      12'd949: return "pmpaddr5";
      12'd950: return "pmpaddr6";
      12'd951: return "pmpaddr7";
      12'd952: return "pmpaddr8";
      12'd953: return "pmpaddr9";
      12'd954: return "pmpaddr10";
      12'd955: return "pmpaddr11";
      12'd956: return "pmpaddr12";
      12'd957: return "pmpaddr13";
      12'd958: return "pmpaddr14";
      12'd959: return "pmpaddr15";
      12'd2816: return "mcycle";
      12'd2818: return "minstret";
      12'd2819: return "mhpmcounter3";
      12'd2820: return "mhpmcounter4";
      12'd2821: return "mhpmcounter5";
      12'd2822: return "mhpmcounter6";
      12'd2823: return "mhpmcounter7";
      12'd2824: return "mhpmcounter8";
      12'd2825: return "mhpmcounter9";
      12'd2826: return "mhpmcounter10";
      12'd2827: return "mhpmcounter11";
      12'd2828: return "mhpmcounter12";
      12'd2829: return "mhpmcounter13";
      12'd2830: return "mhpmcounter14";
      12'd2831: return "mhpmcounter15";
      12'd2832: return "mhpmcounter16";
      12'd2833: return "mhpmcounter17";
      12'd2834: return "mhpmcounter18";
      12'd2835: return "mhpmcounter19";
      12'd2836: return "mhpmcounter20";
      12'd2837: return "mhpmcounter21";
      12'd2838: return "mhpmcounter22";
      12'd2839: return "mhpmcounter23";
      12'd2840: return "mhpmcounter24";
      12'd2841: return "mhpmcounter25";
      12'd2842: return "mhpmcounter26";
      12'd2843: return "mhpmcounter27";
      12'd2844: return "mhpmcounter28";
      12'd2845: return "mhpmcounter29";
      12'd2846: return "mhpmcounter30";
      12'd2847: return "mhpmcounter31";
      12'd2944: return "mcycleh";
      12'd2946: return "minstreth";
      12'd2947: return "mhpmcounter3h";
      12'd2948: return "mhpmcounter4h";
      12'd2949: return "mhpmcounter5h";
      12'd2950: return "mhpmcounter6h";
      12'd2951: return "mhpmcounter7h";
      12'd2952: return "mhpmcounter8h";
      12'd2953: return "mhpmcounter9h";
      12'd2954: return "mhpmcounter10h";
      12'd2955: return "mhpmcounter11h";
      12'd2956: return "mhpmcounter12h";
      12'd2957: return "mhpmcounter13h";
      12'd2958: return "mhpmcounter14h";
      12'd2959: return "mhpmcounter15h";
      12'd2960: return "mhpmcounter16h";
      12'd2961: return "mhpmcounter17h";
      12'd2962: return "mhpmcounter18h";
      12'd2963: return "mhpmcounter19h";
      12'd2964: return "mhpmcounter20h";
      12'd2965: return "mhpmcounter21h";
      12'd2966: return "mhpmcounter22h";
      12'd2967: return "mhpmcounter23h";
      12'd2968: return "mhpmcounter24h";
      12'd2969: return "mhpmcounter25h";
      12'd2970: return "mhpmcounter26h";
      12'd2971: return "mhpmcounter27h";
      12'd2972: return "mhpmcounter28h";
      12'd2973: return "mhpmcounter29h";
      12'd2974: return "mhpmcounter30h";
      12'd2975: return "mhpmcounter31h";
      12'd803: return "mhpmevent3";
      12'd804: return "mhpmevent4";
      12'd805: return "mhpmevent5";
      12'd806: return "mhpmevent6";
      12'd807: return "mhpmevent7";
      12'd808: return "mhpmevent8";
      12'd809: return "mhpmevent9";
      12'd810: return "mhpmevent10";
      12'd811: return "mhpmevent11";
      12'd812: return "mhpmevent12";
      12'd813: return "mhpmevent13";
      12'd814: return "mhpmevent14";
      12'd815: return "mhpmevent15";
      12'd816: return "mhpmevent16";
      12'd817: return "mhpmevent17";
      12'd818: return "mhpmevent18";
      12'd819: return "mhpmevent19";
      12'd820: return "mhpmevent20";
      12'd821: return "mhpmevent21";
      12'd822: return "mhpmevent22";
      12'd823: return "mhpmevent23";
      12'd824: return "mhpmevent24";
      12'd825: return "mhpmevent25";
      12'd826: return "mhpmevent26";
      12'd827: return "mhpmevent27";
      12'd828: return "mhpmevent28";
      12'd829: return "mhpmevent29";
      12'd830: return "mhpmevent30";
      12'd831: return "mhpmevent31";
      12'd1952: return "tselect";
      12'd1953: return "tdata1";
      12'd1954: return "tdata2";
      12'd1955: return "tdata3";
      12'd1968: return "dcsr";
      12'd1969: return "dpc";
      12'd1970: return "dscratch";
      12'd512: return "hstatus";
      12'd514: return "hedeleg";
      12'd515: return "hideleg";
      12'd516: return "hie";
      12'd517: return "htvec";
      12'd576: return "hscratch";
      12'd577: return "hepc";
      12'd578: return "hcause";
      12'd579: return "hbadaddr";
      12'd580: return "hip";
      12'd896: return "mbase";
      12'd897: return "mbound";
      12'd898: return "mibase";
      12'd899: return "mibound";
      12'd900: return "mdbase";
      12'd901: return "mdbound";
      12'd800: return "mcountinhibit";
      12'd3009: return "mshwm";
      12'd3010: return "mshwmb";
      12'd3012: return "cdbgctrl";
      default: return $sformatf("0x%x", csr_addr);
    endcase
  endfunction

  function automatic string build_disp_str(input string decode_str, input rvfi_t rvfi_data, 
                                           input logic [9:0] data_accessed);
    string rvfi_insn_str;
    string disp_str;
    string prefix_str;
    logic [32:0] tmp33;
    logic insn_is_compressed;

    insn_is_compressed = (rvfi_data.insn[1:0] != 2'b11);

    // Write compressed instructions as four hex digits (16 bit word), and
    // uncompressed ones as 8 hex digits (32 bit words).
    if (insn_is_compressed) begin
      rvfi_insn_str = $sformatf("    %4h", rvfi_data.insn[15:0]);
    end else begin
      rvfi_insn_str = $sformatf("%8h", rvfi_data.insn);
    end

    prefix_str = rvfi_data.trap ?  "-->" : "";
                    
    disp_str = $sformatf("%h\t%s\t%s%s\t", rvfi_data.pc_rdata, rvfi_insn_str, prefix_str, decode_str);


    if ((data_accessed & RS1) != 0) begin
      disp_str = {disp_str, $sformatf(" %s:0x%08x", reg_addr_to_str(rvfi_data.rs1_addr), rvfi_data.rs1_rdata[31:0])};
    end

    if ((data_accessed & CS1) != 0) begin
      tmp33 = (RegW >= 65) ? trace_reg_fmt(rvfi_data.rs1_rdata) : 0;
      disp_str = {disp_str, $sformatf(" %s:0x%08x+0x%09x", reg_addr_to_str(rvfi_data.rs1_addr), rvfi_data.rs1_rdata[31:0], tmp33)};
    end

    if ((data_accessed & RS2) != 0) begin
      disp_str = {disp_str, $sformatf(" %s:0x%08x", reg_addr_to_str(rvfi_data.rs2_addr), rvfi_data.rs2_rdata[31:0])};
    end

    if ((data_accessed & CS2) != 0) begin
      tmp33 = (RegW >= 65) ? trace_reg_fmt(rvfi_data.rs2_rdata) : 0;
      disp_str = {disp_str, $sformatf(" %s:0x%08x+0x%09x", reg_addr_to_str(rvfi_data.rs2_addr), rvfi_data.rs2_rdata[31:0], tmp33)};
    end

    if ((data_accessed & RS3) != 0) begin
      disp_str = {disp_str, $sformatf(" %s:0x%08x", reg_addr_to_str(rvfi_data.rs3_addr), rvfi_data.rs3_rdata[31:0])};
    end

    if ((data_accessed & RD) != 0) begin
      disp_str = {disp_str, $sformatf(" %s=0x%08x", reg_addr_to_str(rvfi_data.rd_addr), rvfi_data.rd_wdata[31:0])};
    end

    if ((data_accessed & CD) != 0) begin
      tmp33 = (RegW >= 65) ? trace_reg_fmt(rvfi_data.rd_wdata) : 0;
      disp_str = {disp_str, $sformatf(" %s=0x%08x+0x%09x", reg_addr_to_str(rvfi_data.rd_addr), rvfi_data.rd_wdata[31:0], tmp33)};
    end

    if ((data_accessed & MEM) != 0) begin
      disp_str = {disp_str, $sformatf(" PA:0x%08x", rvfi_data.mem_addr)}; 
      if (rvfi_data.mem_wmask == 4'b0001) begin
        disp_str = {disp_str, $sformatf(" store:0x??????%02x", rvfi_data.mem_wdata[7:0])};
      end else if (rvfi_data.mem_wmask == 4'b0011) begin
        disp_str = {disp_str, $sformatf(" store:0x????%04x", rvfi_data.mem_wdata[15:0])};
      end else if (rvfi_data.mem_wmask != 4'b0000) begin
        disp_str = {disp_str, $sformatf(" store:0x%08x", rvfi_data.mem_wdata[31:0])};
      end

      if (rvfi_data.mem_rmask != 4'b0000) begin
        disp_str = {disp_str, $sformatf(" load:0x%08x", rvfi_data.mem_rdata[31:0])};
      end
    end

    if ((data_accessed & MEMC) != 0) begin
      disp_str = {disp_str, $sformatf(" PA:0x%08x", rvfi_data.mem_addr)};

      if (rvfi_data.mem_wmask != 0) begin
        tmp33 = (MemW == 65) ? trace_mem_fmt(rvfi_data.mem_wdata) : 0;
        disp_str = {disp_str, $sformatf(" store:0x%08x+0x%09x", rvfi_data.mem_wdata[31:0], tmp33)};
      end else begin
        tmp33 = (MemW == 65) ? trace_reg_fmt(rvfi_data.mem_rdata) : 0;
        disp_str = {disp_str, $sformatf(" load:0x%08x+0x%09x", rvfi_data.mem_rdata[31:0], tmp33)};
      end
    end

    return disp_str;
  endfunction

  function automatic string decode_mnemonic(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = 0;
    decode_str = $sformatf("%s", mnemonic);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction


  function automatic string decode_r_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RS2 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr,
        rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_r1_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_r_cmixcmov_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RS2 | RS3 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d,x%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs2_addr,
        rvfi_data.rs1_addr, rvfi_data.rs3_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_r_funnelshift_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RS2 | RS3 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d,x%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr,
        rvfi_data.rs3_addr, rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_i_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d,%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr,
                    $signed({{20 {rvfi_data.insn[31]}}, rvfi_data.insn[31:20]}));
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_i_shift_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    // SLLI, SRLI, SRAI, SROI, SLOI, RORI
    logic [4:0] shamt;
    shamt = {rvfi_data.insn[24:20]};
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d,0x%0x", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr, shamt);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_i_funnelshift_insn( input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    // fsri
    logic [5:0] shamt;
    shamt = {rvfi_data.insn[25:20]};
    data_accessed = RS1 | RS3 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d,x%0d,0x%0x", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr,
        rvfi_data.rs3_addr, shamt);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_i_jalr_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    // JALR
    if (cheri_pmode) begin
      data_accessed = CS1 | CD;
      // CH.cjalr
      decode_str = $sformatf("CH.c%s\tc%0d,%0d(c%0d)", mnemonic, rvfi_data.rd_addr,
          $signed({{20 {rvfi_data.insn[31]}}, rvfi_data.insn[31:20]}), rvfi_data.rs1_addr);
    end else begin
      // jalr
      data_accessed = RS1 | RD;
      decode_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_data.rd_addr,
          $signed({{20 {rvfi_data.insn[31]}}, rvfi_data.insn[31:20]}), rvfi_data.rs1_addr);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_u_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RD;
    decode_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_data.rd_addr, {rvfi_data.insn[31:12]});
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_j_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    // JAL
    if (cheri_pmode) begin
      data_accessed = CD;
      decode_str = $sformatf("%s\tc%0d,%0x", "CH.cjal", rvfi_data.rd_addr, rvfi_data.pc_wdata);
    end else begin
      data_accessed = RD;
      decode_str = $sformatf("%s\tx%0d,%0x", mnemonic, rvfi_data.rd_addr, rvfi_data.pc_wdata);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_b_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [31:0] branch_target;
    logic [31:0] imm;

    // We cannot use rvfi_data.pc_wdata for conditional jumps.
    imm = $signed({ {19 {rvfi_data.insn[31]}}, rvfi_data.insn[31], rvfi_data.insn[7],
             rvfi_data.insn[30:25], rvfi_data.insn[11:8], 1'b0 });
    branch_target = rvfi_data.pc_rdata + imm;

    data_accessed = RS1 | RS2;
    decode_str = $sformatf("%s\tx%0d,x%0d,%0x",
                            mnemonic, rvfi_data.rs1_addr, rvfi_data.rs2_addr, branch_target);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_csr_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [11:0] csr;
    string csr_name;
    csr = rvfi_data.insn[31:20];
    csr_name = get_csr_name(csr);

    data_accessed = RD;

    if (!rvfi_data.insn[14]) begin
      data_accessed |= RS1;
      decode_str = $sformatf("%s\tx%0d,%s,x%0d",
                              mnemonic, rvfi_data.rd_addr, csr_name, rvfi_data.rs1_addr);
    end else begin
      decode_str = $sformatf("%s\tx%0d,%s,%0d",
                              mnemonic, rvfi_data.rd_addr, csr_name, {27'b0, rvfi_data.insn[19:15]});
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cr_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    if (rvfi_data.rs2_addr == 5'b0) begin
      if ((rvfi_data.insn[12] == 1'b1) && cheri_pmode) begin
        // C.CH.JALR
        data_accessed = CS1 | CD;
        decode_str = $sformatf("%s\tc%0d", "c.CH.cjalr", rvfi_data.rs1_addr);
      end else if (rvfi_data.insn[12] == 1'b1) begin
        // C.JALR
        data_accessed = RS1 | RD;
        decode_str = $sformatf("%s\tx%0d", mnemonic, rvfi_data.rs1_addr);
      end else if (cheri_pmode) begin
        // C.CH.JR
        data_accessed = CS1;
        decode_str = $sformatf("%s\tc%0d", "c.CH.cjr" , rvfi_data.rs1_addr);
      end else begin
        // C.JR
        data_accessed = RS1;
        decode_str = $sformatf("%s\tx%0d", mnemonic, rvfi_data.rs1_addr);
      end
    end else begin
      data_accessed = RS1 | RS2 | RD; // RS1 == RD
      decode_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs2_addr);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_ci_cli_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [5:0] imm;
    imm = {rvfi_data.insn[12], rvfi_data.insn[6:2]};
    data_accessed = RD;
    decode_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_data.rd_addr, $signed(imm));
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_ci_caddi_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [5:0] nzimm;
    nzimm = {rvfi_data.insn[12], rvfi_data.insn[6:2]};
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_data.rd_addr, $signed(nzimm));
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_ci_caddi16sp_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    logic [9:0] nzimm;
    nzimm = {rvfi_data.insn[12], rvfi_data.insn[4:3], rvfi_data.insn[5], rvfi_data.insn[2], rvfi_data.insn[6], 4'b0};
    if (cheri_pmode) begin
      data_accessed = CS1 | CD;
      decode_str = $sformatf("%s\tc%0d,%0d", "c.CH.cinc16csp", rvfi_data.rd_addr, $signed(nzimm));
    end else begin
      data_accessed = RS1 | RD;
      decode_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_data.rd_addr, $signed(nzimm));
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_ci_clui_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [5:0] nzimm;
    nzimm = {rvfi_data.insn[12], rvfi_data.insn[6:2]};
    data_accessed = RD;
    decode_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_data.rd_addr, 20'($signed(nzimm)));
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_ci_cslli_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [5:0] shamt;
    shamt = {rvfi_data.insn[12], rvfi_data.insn[6:2]};
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_data.rd_addr, shamt);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_ciw_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    // C.ADDI4SPN
    logic [9:0] nzuimm;
    nzuimm = {rvfi_data.insn[10:7], rvfi_data.insn[12:11], rvfi_data.insn[5], rvfi_data.insn[6], 2'b00};
    if (cheri_pmode) begin
      // c.CH.incaddr4spn
      data_accessed = CD | CS1;
      decode_str = $sformatf("%s\tc%0d,csp,%0d", mnemonic, rvfi_data.rd_addr, nzuimm);
    end else begin
      // c.addi4spn
      data_accessed = RD;
      decode_str = $sformatf("%s\tx%0d,x2,%0d", mnemonic, rvfi_data.rd_addr, nzuimm);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cb_sr_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [5:0] shamt;
    shamt = {rvfi_data.insn[12], rvfi_data.insn[6:2]};
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_data.rs1_addr, shamt);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cb_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [7:0] imm;
    logic [31:0] jump_target;
    if (rvfi_data.insn[15:13] == 3'b110 || rvfi_data.insn[15:13] == 3'b111) begin
      // C.BNEZ and C.BEQZ
      // We cannot use rvfi_data.pc_wdata for conditional jumps.
      imm = {rvfi_data.insn[12], rvfi_data.insn[6:5], rvfi_data.insn[2], rvfi_data.insn[11:10], rvfi_data.insn[4:3]};
      jump_target = rvfi_data.pc_rdata + 32'($signed({imm, 1'b0}));
      data_accessed = RS1;
      decode_str = $sformatf("%s\tx%0d,%0x", mnemonic, rvfi_data.rs1_addr, jump_target);
    end else if (rvfi_data.insn[15:13] == 3'b100) begin
      // C.ANDI
      imm = {{2{rvfi_data.insn[12]}}, rvfi_data.insn[12], rvfi_data.insn[6:2]};
      data_accessed = RS1 | RD; // RS1 == RD
      decode_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_data.rd_addr, $signed(imm));
    end else begin
      imm = {rvfi_data.insn[12], rvfi_data.insn[6:2], 2'b00};
      data_accessed = RS1;
      decode_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_data.rs1_addr, imm);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cs_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RS2 | RD; // RS1 == RD
    decode_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cj_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    if (rvfi_data.insn[15:13] == 3'b001) begin
      // C.JAL
      if (cheri_pmode) begin
        data_accessed = CD;
        decode_str = $sformatf("%s\t%0x", "c.CH.cjal", rvfi_data.pc_wdata);
      end else begin
        data_accessed = RD;
        decode_str = $sformatf("%s\t%0x", mnemonic, rvfi_data.pc_wdata);
      end
    end else begin
      // C.J
      if (cheri_pmode)
        decode_str = $sformatf("%s\t%0x", "c.CH.cj", rvfi_data.pc_wdata);
      else
        decode_str = $sformatf("%s\t%0x", mnemonic, rvfi_data.pc_wdata);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_compressed_load_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    logic [7:0] imm;

    if ((rvfi_data.insn[15:13] == 3'b011) && (rvfi_data.insn[1:0] == OPCODE_C0))  begin
      // CHERI: c.clc, use RV64 c.ld encoding
      imm = {rvfi_data.insn[6:5], rvfi_data.insn[12:10], 3'b000};
      data_accessed = CS1 | CD | MEMC;
      decode_str = $sformatf("%s\tc%0d,%0d(c%0d)", mnemonic, rvfi_data.rd_addr, imm, rvfi_data.rs1_addr);
    end else if ((rvfi_data.insn[15:13] == 3'b011) && (rvfi_data.insn[1:0] == OPCODE_C2))  begin
      // CHERI: c.clcsp, RV32: c.ldsp
      imm = {rvfi_data.insn[4:2], rvfi_data.insn[12], rvfi_data.insn[6:5], 3'b000};
      data_accessed = CS1 | CD | MEMC;
      decode_str = $sformatf("%s\tc%0d,%0d(c%0d)", mnemonic, rvfi_data.rd_addr, imm, rvfi_data.rs1_addr);
    end else begin
      if (rvfi_data.insn[1:0] == OPCODE_C0) begin
        // C.LW
        imm = {1'b0, rvfi_data.insn[5], rvfi_data.insn[12:10], rvfi_data.insn[6], 2'b00};
      end else begin
        // C.LWSP
        imm = {rvfi_data.insn[3:2], rvfi_data.insn[12], rvfi_data.insn[6:4], 2'b00};
      end
      if (cheri_pmode) begin
        data_accessed = CS1 | RD | MEM;
        decode_str = $sformatf("%s\tx%0d,%0d(c%0d)", mnemonic, rvfi_data.rd_addr, imm, rvfi_data.rs1_addr);
      end else begin
        data_accessed = RS1 | RD | MEM;
        decode_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_data.rd_addr, imm, rvfi_data.rs1_addr);
      end
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_compressed_store_insn(input string mnemonic, input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    logic [7:0] imm;


    if ((rvfi_data.insn[15:13] == 3'b111) && (rvfi_data.insn[1:0] == OPCODE_C0)) begin
      // CHERI: c.csc, use RV64 c.sd encoding
      imm = {rvfi_data.insn[6:5], rvfi_data.insn[12:10], 3'b000};
      data_accessed = CS1 | CS2 | MEMC;
      decode_str = $sformatf("%s\tc%0d,%0d(c%0d)", mnemonic, rvfi_data.rs2_addr, imm, rvfi_data.rs1_addr);
    end else if ((rvfi_data.insn[15:13] == 3'b111) && (rvfi_data.insn[1:0] == OPCODE_C2)) begin
      // CHERI: c.cscsp, RV32: c.sdsp
      imm = {rvfi_data.insn[9:7], rvfi_data.insn[12:10], 3'b000};
      data_accessed = CS1 | CS2 | MEMC;
      decode_str = $sformatf("%s\tc%0d,%0d(c%0d)", mnemonic, rvfi_data.rs2_addr, imm, rvfi_data.rs1_addr);
    end else begin
      if (rvfi_data.insn[1:0] == OPCODE_C0) begin
        // C.SW
        imm = {1'b0, rvfi_data.insn[5], rvfi_data.insn[12:10], rvfi_data.insn[6], 2'b00};
      end else begin
        // C.SWSP
        imm = {rvfi_data.insn[8:7], rvfi_data.insn[12:9], 2'b00};
      end
      if (cheri_pmode) begin
        data_accessed = CS1 | RS2 | MEM;
        decode_str = $sformatf("%s\tx%0d,%0d(c%0d)", mnemonic, rvfi_data.rs2_addr, imm, rvfi_data.rs1_addr);
      end else begin
        data_accessed = RS1 | RS2 | MEM;
        decode_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_data.rs2_addr, imm, rvfi_data.rs1_addr);
      end
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_load_insn(input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    string       mnemonic;
    logic [13:0] imm;

    logic [2:0] size;
    logic is_cap;

    size = rvfi_data.insn[14:12];
    is_cap = 1'b0;

    if (size == 3'b000) begin
      mnemonic = cheri_pmode ? "clb" : "lb";
    end else if (size == 3'b001) begin
      mnemonic = cheri_pmode ? "clh" :"lh";
    end else if (size == 3'b010) begin
      mnemonic = cheri_pmode ? "clw" :"lw";
    end else if (size == 3'b100) begin
      mnemonic = cheri_pmode ? "clbu" :"lbu";
    end else if (size == 3'b101) begin
      mnemonic = cheri_pmode ? "clhu" :"lhu";
    end else if (size == 3'b011) begin
      mnemonic = "CH.clc";
      is_cap = 1'b1;
    end else begin
      decode_str = "INVALID";
      return decode_str;
    end

    imm = {{3{rvfi_data.insn[31]}},rvfi_data.insn[30:20]};

    if (is_cap) begin
      data_accessed = CD | CS1 | MEMC;
      decode_str = $sformatf("%s\tc%0d,%0d(c%0d)", mnemonic, rvfi_data.rd_addr,
                      $signed(imm), rvfi_data.rs1_addr);
    end else if (cheri_pmode) begin
      data_accessed = RD | CS1 | MEM;
      decode_str = $sformatf("%s\tx%0d,%0d(c%0d)", mnemonic, rvfi_data.rd_addr,
                      $signed(imm), rvfi_data.rs1_addr);
    end else begin
      data_accessed = RD | RS1 | MEM;
      decode_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_data.rd_addr,
                      $signed(imm), rvfi_data.rs1_addr);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_store_insn(input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    string    mnemonic;
    logic     is_cap;
    logic [13:0] imm;

    is_cap = 1'b0;
    unique case (rvfi_data.insn[13:12])
      2'b00:  mnemonic = cheri_pmode ? "csb" : "sb";
      2'b01:  mnemonic = cheri_pmode ? "csh" : "sh";
      2'b10:  mnemonic = cheri_pmode ? "csw" : "sw";
      2'b11:  begin
        mnemonic = "CH.csc";
        is_cap = 1'b1;
      end
      default: begin
        decode_str = "INVALID";
        return decode_str;
      end
    endcase

    imm = {{3{rvfi_data.insn[31]}},rvfi_data.insn[30:25], rvfi_data.insn[11:7]};

    if (!rvfi_data.insn[14]) begin
      // regular store
      if (is_cap) begin
        data_accessed = CS1 | CS2 | MEMC;
        decode_str = $sformatf("%s\tc%0d,%0d(c%0d)",
                                mnemonic,
                                rvfi_data.rs2_addr,
                                $signed(imm),
                                rvfi_data.rs1_addr);
      end else if (cheri_pmode) begin
        data_accessed = CS1 | RS2 | MEM;
        decode_str = $sformatf("%s\tx%0d,%0d(c%0d)",
                                mnemonic,
                                rvfi_data.rs2_addr,
                                $signed(imm),
                                rvfi_data.rs1_addr);
      end else begin
        data_accessed = RS1 | RS2 | MEM;
        decode_str = $sformatf("%s\tx%0d,%0d(x%0d)",
                                mnemonic,
                                rvfi_data.rs2_addr,
                                $signed(imm),
                                rvfi_data.rs1_addr);
      end
    end else begin
      decode_str = "INVALID";
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string get_fence_description(logic [3:0] bits);
    string desc = "";
    if (bits[3]) begin
      desc = {desc, "i"};
    end
    if (bits[2]) begin
      desc = {desc, "o"};
    end
    if (bits[1]) begin
      desc = {desc, "r"};
    end
    if (bits[0]) begin
      desc = {desc, "w"};
    end
    return desc;
  endfunction

  function automatic string decode_fence(input rvfi_t rvfi_data);
    logic [9:0] data_accessed;

    string decode_str;
    string predecessor;
    string successor;
    data_accessed = 0;
    predecessor = get_fence_description(rvfi_data.insn[27:24]);
    successor = get_fence_description(rvfi_data.insn[23:20]);
    decode_str = $sformatf("fence\t%s,%s", predecessor, successor);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_rd_rs1_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RD;
    decode_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_rd_cs1_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = CS1 | RD;
    decode_str = $sformatf("%s\tx%0d,c%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_cd_cs1_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = CS1 | CD;
    decode_str = $sformatf("%s\tc%0d,c%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_rd_cs1_cs2_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = CS2 | CS1 | RD;
    decode_str = $sformatf("%s\tx%0d,c%0d,c%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr, rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_cd_cs1_cs2_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = CS2 | CS1 | CD;
    decode_str = $sformatf("%s\tc%0d,c%0d,c%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr, rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_cd_cs1_rs2_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS2 | CS1 | CD;
    decode_str = $sformatf("%s\tc%0d,c%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr, rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_cd_cs1_imm_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [13:0] imm;

    data_accessed =  CS1 | CD;

    // cincaddrimm and csetboundsimm
    imm = {{3{rvfi_data.insn[31]}}, rvfi_data.insn[30:20]};  // imm not extended

    if (rvfi_data.insn[14:12] == 3'b001) // cincaddrimm
      decode_str = $sformatf("%s\tc%0d,c%0d,%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr, $signed(imm));
    else                            // csetboundsimm
      decode_str = $sformatf("%s\tc%0d,c%0d,%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr, imm);

    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_auipcc_insn(input rvfi_t rvfi_data, input logic cheri_pmode);
    logic [9:0] data_accessed;
    string decode_str;
    logic [31:0] imm;

    // We cannot use rvfi_data.pc_wdata for conditional jumps.
    imm = rvfi_data.insn[31:12];
    data_accessed =  CD;
    if (cheri_pmode) begin
      decode_str = $sformatf("%s\tc%0d,0x%0x", "CH.auipcc", rvfi_data.rd_addr, imm);
    end else begin
      decode_str = $sformatf("%s\tx%0d,0x%0x", "auipc", rvfi_data.rd_addr, imm);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction


  function automatic string decode_cheri_auicgp_insn(input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    logic [31:0] imm;

    // We cannot use rvfi_data.pc_wdata for conditional jumps.
    imm = rvfi_data.insn[31:12];
    data_accessed =  CD | CS1;
    decode_str = $sformatf("%s\tc%0d,0x%0x", "CH.auicgp", rvfi_data.rd_addr, imm);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction


  function automatic string decode_cheri_cs1_cs2_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = CS2 | CS1;
    decode_str = $sformatf("%s\tc%0d,c%0d", mnemonic, rvfi_data.rs1_addr, rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_cheri_scrrw_insn(input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    string mnemonic, scr_name;

    scr_name = get_scr_name(rvfi_data.insn[24:20]);
    data_accessed = CS1 | CD;

    if (rvfi_data.rd_addr == 0) begin
      mnemonic = "CH.cspecialw";
      decode_str = $sformatf("%s\t%s,c%0d", mnemonic, scr_name, rvfi_data.rs1_addr);
    end else if (rvfi_data.rs1_addr == 0) begin
      mnemonic = "CH.cspecialr";
      decode_str = $sformatf("%s\tc%0d,%s", mnemonic, rvfi_data.rd_addr, scr_name);
    end else begin
      mnemonic = "CH.cspecialrw";
      decode_str = $sformatf("%s\tc%0d,%s,c%0d", mnemonic, rvfi_data.rd_addr, scr_name, rvfi_data.rs1_addr);
    end
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  function automatic string decode_amo_insn(input string mnemonic, input rvfi_t rvfi_data);
    logic [9:0] data_accessed;
    string decode_str;
    data_accessed = RS1 | RS2 | RD |MEM;
    decode_str = $sformatf("%s\tx%0d,x%0d,x%0d", mnemonic, rvfi_data.rd_addr, rvfi_data.rs1_addr,
        rvfi_data.rs2_addr);
    decode_str = build_disp_str(decode_str, rvfi_data, data_accessed);
    return decode_str;
  endfunction

  //
  // final top-level display functions
  //
  function string decode_rvfi_instr_vlog(input rvfi_t rvfi_data, input logic cheri_pmode);
    string decode_str;
    logic insn_is_compressed;
    decode_str = "";
    insn_is_compressed = 0;

    // Check for compressed instructions
    if (rvfi_data.intr) begin
      decode_str = "==>";  // interrupts are not tied to a particular instruction 
    end else if (rvfi_data.insn[1:0] != 2'b11) begin
      insn_is_compressed = 1;
      // Separate case to avoid overlapping decoding
      if (rvfi_data.insn[15:13] == INSN_CMV[15:13] && rvfi_data.insn[1:0] == OPCODE_C2) begin
        if (rvfi_data.insn[12] == INSN_CADD[12]) begin
          if (rvfi_data.insn[11:2] == INSN_CEBREAK[11:2]) begin
            decode_str = "c.ebreak";
          end else if (rvfi_data.insn[6:2] == INSN_CJALR[6:2]) begin
            decode_str = decode_cr_insn("c.jalr", rvfi_data, cheri_pmode);
          end else begin
            decode_str = decode_cr_insn("c.add", rvfi_data, cheri_pmode);
          end
        end else begin
          if (rvfi_data.insn[6:2] == INSN_CJR[6:2]) begin
            decode_str = decode_cr_insn("c.jr", rvfi_data, cheri_pmode);
          end else begin
            decode_str = decode_cr_insn("c.mv", rvfi_data, cheri_pmode);
          end
        end
      end else begin
        unique casez (rvfi_data.insn[15:0])
          // C0 Opcodes
          INSN_CADDI4SPN: begin
            if (rvfi_data.insn[12:2] == 11'h0) begin
              // Align with pseudo-mnemonic used by GNU binutils and LLVM's MC layer
              decode_str = decode_mnemonic("c.unimp", rvfi_data);
            end else begin
              decode_str = decode_ciw_insn("c.addi4spn", rvfi_data, cheri_pmode);
            end
          end
          INSN_CLW:        decode_str = decode_compressed_load_insn("c.lw", rvfi_data, cheri_pmode);
          INSN_CSW:        decode_str = decode_compressed_store_insn("c.sw", rvfi_data, cheri_pmode);
          INSN_CCLC:       decode_str = decode_compressed_load_insn("c.CH.clc", rvfi_data, cheri_pmode);
          INSN_CCSC:       decode_str = decode_compressed_store_insn("c.CH.csc", rvfi_data, cheri_pmode);
          // C1 Opcodes
          INSN_CADDI:      decode_str = decode_ci_caddi_insn("c.addi", rvfi_data);
          INSN_CJAL:       decode_str = decode_cj_insn("c.jal", rvfi_data, cheri_pmode);
          INSN_CJ:         decode_str = decode_cj_insn("c.j", rvfi_data, cheri_pmode);
          INSN_CLI:        decode_str = decode_ci_cli_insn("c.li", rvfi_data);
          INSN_CLUI: begin
            // These two instructions share opcode
            if (rvfi_data.insn[11:7] == 5'd2) begin
              decode_str = decode_ci_caddi16sp_insn("c.addi16sp", rvfi_data, cheri_pmode);
            end else begin
              decode_str = decode_ci_clui_insn("c.lui", rvfi_data);
            end
          end
          INSN_CSRLI:      decode_str = decode_cb_sr_insn("c.srli", rvfi_data);
          INSN_CSRAI:      decode_str = decode_cb_sr_insn("c.srai", rvfi_data);
          INSN_CANDI:      decode_str = decode_cb_insn("c.andi", rvfi_data);
          INSN_CSUB:       decode_str = decode_cs_insn("c.sub", rvfi_data);
          INSN_CXOR:       decode_str = decode_cs_insn("c.xor", rvfi_data);
          INSN_COR:        decode_str = decode_cs_insn("c.or", rvfi_data);
          INSN_CAND:       decode_str = decode_cs_insn("c.and", rvfi_data);
          INSN_CBEQZ:      decode_str = decode_cb_insn("c.beqz", rvfi_data);
          INSN_CBNEZ:      decode_str = decode_cb_insn("c.bnez", rvfi_data);
          // C2 Opcodes
          INSN_CSLLI:      decode_str = decode_ci_cslli_insn("c.slli", rvfi_data);
          INSN_CLWSP:      decode_str = decode_compressed_load_insn("c.lwsp", rvfi_data, cheri_pmode);
          INSN_SWSP:       decode_str = decode_compressed_store_insn("c.swsp", rvfi_data, cheri_pmode);
          INSN_CCLCSP:     decode_str = decode_compressed_load_insn("c.CH.clcsp", rvfi_data, cheri_pmode);
          INSN_CCSCSP:     decode_str = decode_compressed_store_insn("c.CH.cscsp", rvfi_data, cheri_pmode);
          default:         decode_str = decode_mnemonic("INVALID", rvfi_data);
        endcase
      end
    end else begin
      unique casez (rvfi_data.insn)
        // Regular opcodes
        INSN_LUI:        decode_str = decode_u_insn("lui", rvfi_data);
        // INSN_AUIPC:      decode_u_insn("auipc");
        INSN_JAL:        decode_str = decode_j_insn("jal", rvfi_data, cheri_pmode);
        INSN_JALR:       decode_str = decode_i_jalr_insn("jalr", rvfi_data, cheri_pmode);
        // BRANCH
        INSN_BEQ:        decode_str = decode_b_insn("beq", rvfi_data);
        INSN_BNE:        decode_str = decode_b_insn("bne", rvfi_data);
        INSN_BLT:        decode_str = decode_b_insn("blt", rvfi_data);
        INSN_BGE:        decode_str = decode_b_insn("bge", rvfi_data);
        INSN_BLTU:       decode_str = decode_b_insn("bltu", rvfi_data);
        INSN_BGEU:       decode_str = decode_b_insn("bgeu", rvfi_data);
        // OPIMM
        INSN_ADDI: begin
          if (rvfi_data.insn == 32'h00_00_00_13) begin
            // TODO: objdump doesn't decode this as nop currently, even though it would be helpful
            // Decide what to do here: diverge from objdump, or make the trace less readable to
            // users.
            decode_str = decode_i_insn("addi", rvfi_data);
          end else begin
            decode_str = decode_i_insn("addi", rvfi_data);
          end
        end
        INSN_SLTI:       decode_str = decode_i_insn("slti", rvfi_data);
        INSN_SLTIU:      decode_str = decode_i_insn("sltiu", rvfi_data);
        INSN_XORI:       decode_str = decode_i_insn("xori", rvfi_data);
        INSN_ORI:        decode_str = decode_i_insn("ori", rvfi_data);
        // Unlike the ratified v.1.0.0 bitmanip extension, the v.0.94 draft extension continues to
        // define the pseudo-instruction
        //   zext.b rd rs = andi rd, rs, 255.
        // However, for now the tracer doesn't emit this due to a lack of support in the LLVM and
        // GCC toolchains. Enabling this functionality when the time is right is tracked in
        // https://github.com/lowRISC/ibex/issues/1228
        INSN_ANDI:       decode_str = decode_i_insn("andi", rvfi_data);
        // INSN_ANDI:begin
          // casez (rvfi_data.insn)
            // INSN_ZEXTB:  decode_r1_insn("zext.b");
            // default:     decode_i_insn("andi");
          // endcase
        // end
        INSN_SLLI:       decode_str = decode_i_shift_insn("slli", rvfi_data);
        INSN_SRLI:       decode_str = decode_i_shift_insn("srli", rvfi_data);
        INSN_SRAI:       decode_str = decode_i_shift_insn("srai", rvfi_data);
        // OP
        INSN_ADD:        decode_str = decode_r_insn("add", rvfi_data);
        INSN_SUB:        decode_str = decode_r_insn("sub", rvfi_data);
        INSN_SLL:        decode_str = decode_r_insn("sll", rvfi_data);
        INSN_SLT:        decode_str = decode_r_insn("slt", rvfi_data);
        INSN_SLTU:       decode_str = decode_r_insn("sltu", rvfi_data);
        INSN_XOR:        decode_str = decode_r_insn("xor", rvfi_data);
        INSN_SRL:        decode_str = decode_r_insn("srl", rvfi_data);
        INSN_SRA:        decode_str = decode_r_insn("sra", rvfi_data);
        INSN_OR:         decode_str = decode_r_insn("or", rvfi_data);
        INSN_AND:        decode_str = decode_r_insn("and", rvfi_data);
        // SYSTEM (CSR manipulation)
        INSN_CSRRW:      decode_str = decode_csr_insn("csrrw", rvfi_data);
        INSN_CSRRS:      decode_str = decode_csr_insn("csrrs", rvfi_data);
        INSN_CSRRC:      decode_str = decode_csr_insn("csrrc", rvfi_data);
        INSN_CSRRWI:     decode_str = decode_csr_insn("csrrwi", rvfi_data);
        INSN_CSRRSI:     decode_str = decode_csr_insn("csrrsi", rvfi_data);
        INSN_CSRRCI:     decode_str = decode_csr_insn("csrrci", rvfi_data);
        // SYSTEM (others)
        INSN_ECALL:      decode_str = decode_mnemonic("ecall", rvfi_data);
        INSN_EBREAK:     decode_str = decode_mnemonic("ebreak", rvfi_data);
        INSN_MRET:       decode_str = decode_mnemonic("mret", rvfi_data);
        INSN_DRET:       decode_str = decode_mnemonic("dret", rvfi_data);
        INSN_WFI:        decode_str = decode_mnemonic("wfi", rvfi_data);
        // RV32M
        INSN_PMUL:       decode_str = decode_r_insn("mul", rvfi_data);
        INSN_PMUH:       decode_str = decode_r_insn("mulh", rvfi_data);
        INSN_PMULHSU:    decode_str = decode_r_insn("mulhsu", rvfi_data);
        INSN_PMULHU:     decode_str = decode_r_insn("mulhu", rvfi_data);
        INSN_DIV:        decode_str = decode_r_insn("div", rvfi_data);
        INSN_DIVU:       decode_str = decode_r_insn("divu", rvfi_data);
        INSN_REM:        decode_str = decode_r_insn("rem", rvfi_data);
        INSN_REMU:       decode_str = decode_r_insn("remu", rvfi_data);
        // LOAD & STORE
        INSN_LOAD:       decode_str = decode_load_insn(rvfi_data, cheri_pmode);
        INSN_STORE:      decode_str = decode_store_insn(rvfi_data, cheri_pmode);
        // MISC-MEM
        INSN_FENCE:      decode_str = decode_fence(rvfi_data);
        INSN_FENCEI:     decode_str = decode_mnemonic("fence.i", rvfi_data);
        // RV32B - ZBA
        INSN_SH1ADD:     decode_str = decode_r_insn("sh1add", rvfi_data);
        INSN_SH2ADD:     decode_str = decode_r_insn("sh2add", rvfi_data);
        INSN_SH3ADD:     decode_str = decode_r_insn("sh3add", rvfi_data);
        // RV32B - ZBB
        INSN_RORI:       decode_str = decode_i_shift_insn("rori", rvfi_data);
        INSN_ROL:        decode_str = decode_r_insn("rol", rvfi_data);
        INSN_ROR:        decode_str = decode_r_insn("ror", rvfi_data);
        INSN_MIN:        decode_str = decode_r_insn("min", rvfi_data);
        INSN_MAX:        decode_str = decode_r_insn("max", rvfi_data);
        INSN_MINU:       decode_str = decode_r_insn("minu", rvfi_data);
        INSN_MAXU:       decode_str = decode_r_insn("maxu", rvfi_data);
        INSN_XNOR:       decode_str = decode_r_insn("xnor", rvfi_data);
        INSN_ORN:        decode_str = decode_r_insn("orn", rvfi_data);
        INSN_ANDN:       decode_str = decode_r_insn("andn", rvfi_data);
        // The ratified v.1.0.0 bitmanip extension defines the pseudo-instruction
        //   zext.h rd rs = pack rd, rs, zero.
        // However, for now the tracer doesn't emit this due to a lack of support in the LLVM and
        // GCC toolchains. Enabling this functionality when the time is right is tracked in
        // https://github.com/lowRISC/ibex/issues/1228
        INSN_PACK:       decode_str = decode_r_insn("pack", rvfi_data);
        // INSN_PACK: begin
          // casez (rvfi_data.insn)
            // INSN_ZEXTH:  decode_r1_insn("zext.h");
            // default:     decode_r_insn("pack");
          // endcase
        // end
        INSN_PACKH:      decode_str = decode_r_insn("packh", rvfi_data);
        INSN_PACKU:      decode_str = decode_r_insn("packu", rvfi_data);
        INSN_CLZ:        decode_str = decode_r1_insn("clz", rvfi_data);
        INSN_CTZ:        decode_str = decode_r1_insn("ctz", rvfi_data);
        INSN_CPOP:       decode_str = decode_r1_insn("cpop", rvfi_data);
        INSN_SEXTB:      decode_str = decode_r1_insn("sext.b", rvfi_data);
        INSN_SEXTH:      decode_str = decode_r1_insn("sext.h", rvfi_data);
        // RV32B - ZBS
        INSN_BCLRI:     decode_str = decode_i_insn("bclri", rvfi_data);
        INSN_BSETI:     decode_str = decode_i_insn("bseti", rvfi_data);
        INSN_BINVI:     decode_str = decode_i_insn("binvi", rvfi_data);
        INSN_BEXTI:     decode_str = decode_i_insn("bexti", rvfi_data);
        INSN_BCLR:      decode_str = decode_r_insn("bclr", rvfi_data);
        INSN_BSET:      decode_str = decode_r_insn("bset", rvfi_data);
        INSN_BINV:      decode_str = decode_r_insn("binv", rvfi_data);
        INSN_BEXT:      decode_str = decode_r_insn("bext", rvfi_data);
        // RV32B - ZBE
        INSN_BDECOMPRESS: decode_str = decode_r_insn("bdecompress", rvfi_data);
        INSN_BCOMPRESS:   decode_str = decode_r_insn("bcompress", rvfi_data);
        // RV32B - ZBP
        INSN_GREV:       decode_str = decode_r_insn("grev", rvfi_data);
        INSN_GREVI: begin
          unique casez (rvfi_data.insn)
            INSN_REV_P:  decode_str = decode_r1_insn("rev.p", rvfi_data);
            INSN_REV2_N: decode_str = decode_r1_insn("rev2.n", rvfi_data);
            INSN_REV_N:  decode_str = decode_r1_insn("rev.n", rvfi_data);
            INSN_REV4_B: decode_str = decode_r1_insn("rev4.b", rvfi_data);
            INSN_REV2_B: decode_str = decode_r1_insn("rev2.b", rvfi_data);
            INSN_REV_B:  decode_str = decode_r1_insn("rev.b", rvfi_data);
            INSN_REV8_H: decode_str = decode_r1_insn("rev8.h", rvfi_data);
            INSN_REV4_H: decode_str = decode_r1_insn("rev4.h", rvfi_data);
            INSN_REV2_H: decode_str = decode_r1_insn("rev2.h", rvfi_data);
            INSN_REV_H:  decode_str = decode_r1_insn("rev.h", rvfi_data);
            INSN_REV16:  decode_str = decode_r1_insn("rev16", rvfi_data);
            INSN_REV8:   decode_str = decode_r1_insn("rev8", rvfi_data);
            INSN_REV4:   decode_str = decode_r1_insn("rev4", rvfi_data);
            INSN_REV2:   decode_str = decode_r1_insn("rev2", rvfi_data);
            INSN_REV:    decode_str = decode_r1_insn("rev", rvfi_data);
            default:     decode_str = decode_i_insn("grevi", rvfi_data);
          endcase
        end
        INSN_GORC:       decode_str = decode_r_insn("gorc", rvfi_data);
        INSN_GORCI: begin
          unique casez (rvfi_data.insn)
            INSN_ORC_P:  decode_str = decode_r1_insn("orc.p", rvfi_data);
            INSN_ORC2_N: decode_str = decode_r1_insn("orc2.n", rvfi_data);
            INSN_ORC_N:  decode_str = decode_r1_insn("orc.n", rvfi_data);
            INSN_ORC4_B: decode_str = decode_r1_insn("orc4.b", rvfi_data);
            INSN_ORC2_B: decode_str = decode_r1_insn("orc2.b", rvfi_data);
            INSN_ORC_B:  decode_str = decode_r1_insn("orc.b", rvfi_data);
            INSN_ORC8_H: decode_str = decode_r1_insn("orc8.h", rvfi_data);
            INSN_ORC4_H: decode_str = decode_r1_insn("orc4.h", rvfi_data);
            INSN_ORC2_H: decode_str = decode_r1_insn("orc2.h", rvfi_data);
            INSN_ORC_H:  decode_str = decode_r1_insn("orc.h", rvfi_data);
            INSN_ORC16:  decode_str = decode_r1_insn("orc16", rvfi_data);
            INSN_ORC8:   decode_str = decode_r1_insn("orc8", rvfi_data);
            INSN_ORC4:   decode_str = decode_r1_insn("orc4", rvfi_data);
            INSN_ORC2:   decode_str = decode_r1_insn("orc2", rvfi_data);
            INSN_ORC:    decode_str = decode_r1_insn("orc", rvfi_data);
            default:     decode_str = decode_i_insn("gorci", rvfi_data);
          endcase
        end
        INSN_SHFL:       decode_str = decode_r_insn("shfl", rvfi_data);
        INSN_SHFLI: begin
          unique casez (rvfi_data.insn)
            INSN_ZIP_N:  decode_str = decode_r1_insn("zip.n", rvfi_data);
            INSN_ZIP2_B: decode_str = decode_r1_insn("zip2.b", rvfi_data);
            INSN_ZIP_B:  decode_str = decode_r1_insn("zip.b", rvfi_data);
            INSN_ZIP4_H: decode_str = decode_r1_insn("zip4.h", rvfi_data);
            INSN_ZIP2_H: decode_str = decode_r1_insn("zip2.h", rvfi_data);
            INSN_ZIP_H:  decode_str = decode_r1_insn("zip.h", rvfi_data);
            INSN_ZIP8:   decode_str = decode_r1_insn("zip8", rvfi_data);
            INSN_ZIP4:   decode_str = decode_r1_insn("zip4", rvfi_data);
            INSN_ZIP2:   decode_str = decode_r1_insn("zip2", rvfi_data);
            INSN_ZIP:    decode_str = decode_r1_insn("zip", rvfi_data);
            default:     decode_str = decode_i_insn("shfli", rvfi_data);
          endcase
        end
        INSN_UNSHFL:       decode_str = decode_r_insn("unshfl", rvfi_data);
        INSN_UNSHFLI: begin
          unique casez (rvfi_data.insn)
            INSN_UNZIP_N:  decode_str = decode_r1_insn("unzip.n", rvfi_data);
            INSN_UNZIP2_B: decode_str = decode_r1_insn("unzip2.b", rvfi_data);
            INSN_UNZIP_B:  decode_str = decode_r1_insn("unzip.b", rvfi_data);
            INSN_UNZIP4_H: decode_str = decode_r1_insn("unzip4.h", rvfi_data);
            INSN_UNZIP2_H: decode_str = decode_r1_insn("unzip2.h", rvfi_data);
            INSN_UNZIP_H:  decode_str = decode_r1_insn("unzip.h", rvfi_data);
            INSN_UNZIP8:   decode_str = decode_r1_insn("unzip8", rvfi_data);
            INSN_UNZIP4:   decode_str = decode_r1_insn("unzip4", rvfi_data);
            INSN_UNZIP2:   decode_str = decode_r1_insn("unzip2", rvfi_data);
            INSN_UNZIP:    decode_str = decode_r1_insn("unzip", rvfi_data);
            default:       decode_str = decode_i_insn("unshfli", rvfi_data);
          endcase
        end
        INSN_XPERM_N:    decode_str = decode_r_insn("xperm_n", rvfi_data);
        INSN_XPERM_B:    decode_str = decode_r_insn("xperm_b", rvfi_data);
        INSN_XPERM_H:    decode_str = decode_r_insn("xperm_h", rvfi_data);
        INSN_SLO:        decode_str = decode_r_insn("slo", rvfi_data);
        INSN_SRO:        decode_str = decode_r_insn("sro", rvfi_data);
        INSN_SLOI:       decode_str = decode_i_shift_insn("sloi", rvfi_data);
        INSN_SROI:       decode_str = decode_i_shift_insn("sroi", rvfi_data);

        // RV32B - ZBT
        INSN_CMIX:       decode_str = decode_r_cmixcmov_insn("cmix", rvfi_data);
        INSN_CMOV:       decode_str = decode_r_cmixcmov_insn("cmov", rvfi_data);
        INSN_FSR:        decode_str = decode_r_funnelshift_insn("fsr", rvfi_data);
        INSN_FSL:        decode_str = decode_r_funnelshift_insn("fsl", rvfi_data);
        INSN_FSRI:       decode_str = decode_i_funnelshift_insn("fsri", rvfi_data);

        // RV32B - ZBF
        INSN_BFP:        decode_str = decode_r_insn("bfp", rvfi_data);

        // RV32B - ZBC
        INSN_CLMUL:      decode_str = decode_r_insn("clmul", rvfi_data);
        INSN_CLMULR:     decode_str = decode_r_insn("clmulr", rvfi_data);
        INSN_CLMULH:     decode_str = decode_r_insn("clmulh", rvfi_data);

        // RV32B - ZBR
        INSN_CRC32_B:    decode_str = decode_r1_insn("crc32.b", rvfi_data);
        INSN_CRC32_H:    decode_str = decode_r1_insn("crc32.h", rvfi_data);
        INSN_CRC32_W:    decode_str = decode_r1_insn("crc32.w", rvfi_data);
        INSN_CRC32C_B:   decode_str = decode_r1_insn("crc32c.b", rvfi_data);
        INSN_CRC32C_H:   decode_str = decode_r1_insn("crc32c.h", rvfi_data);
        INSN_CRC32C_W:   decode_str = decode_r1_insn("crc32c.w", rvfi_data);

        // CHERI, get fields
        INSN_CHGETPERM:    decode_str = decode_cheri_rd_cs1_insn("CH.cgetperm", rvfi_data);
        INSN_CHGETTYPE:    decode_str = decode_cheri_rd_cs1_insn("CH.cgettype", rvfi_data);
        INSN_CHGETBASE:    decode_str = decode_cheri_rd_cs1_insn("CH.cgetbase", rvfi_data);
        INSN_CHGETTOP:     decode_str = decode_cheri_rd_cs1_insn("CH.cgettop", rvfi_data);
        INSN_CHGETLEN:     decode_str = decode_cheri_rd_cs1_insn("CH.cgetlen", rvfi_data);
        INSN_CHGETTAG:     decode_str = decode_cheri_rd_cs1_insn("CH.cgettag", rvfi_data);
        INSN_CHGETSEALED:  decode_str = decode_cheri_rd_cs1_insn("CH.cgetseald", rvfi_data);
        INSN_CHGETADDR:    decode_str = decode_cheri_rd_cs1_insn("CH.cgetaddr", rvfi_data);
        INSN_CHGETHIGH:     decode_str = decode_cheri_rd_cs1_insn("CH.cgethigh", rvfi_data);

        INSN_CHSEAL:       decode_str = decode_cheri_cd_cs1_cs2_insn("CH.cseal", rvfi_data);
        INSN_CHUNSEAL:     decode_str = decode_cheri_cd_cs1_cs2_insn("CH.cunseal", rvfi_data);
        INSN_CHANDPERM:    decode_str = decode_cheri_cd_cs1_rs2_insn("CH.candperm", rvfi_data);
        INSN_CHSETADDR:    decode_str = decode_cheri_cd_cs1_rs2_insn("CH.csetaddr", rvfi_data);
        INSN_CHINCADDR:    decode_str = decode_cheri_cd_cs1_rs2_insn("CH.cincaddr", rvfi_data);
        INSN_CHINCADDRIMM: decode_str = decode_cheri_cd_cs1_imm_insn("CH.cincaddrimm", rvfi_data);
        INSN_CHSETBOUNDS:  decode_str = decode_cheri_cd_cs1_rs2_insn("CH.csetbounds", rvfi_data);
        INSN_CHSETBOUNDSEX:  decode_str = decode_cheri_cd_cs1_rs2_insn("CH.csetboundsexact", rvfi_data);
        INSN_CHSETBOUNDSRNDN: decode_str = decode_cheri_cd_cs1_rs2_insn("CH.csetboundsrounddown", rvfi_data);

        INSN_CHSETBOUNDSIMM: decode_str = decode_cheri_cd_cs1_imm_insn("CH.csetboundsimm", rvfi_data);
        INSN_CHCLEARTAG:     decode_str = decode_cheri_cd_cs1_insn("CH.ccleartag", rvfi_data);
        INSN_CHCRRL:         decode_str = decode_cheri_rd_rs1_insn("CH.crrl", rvfi_data);
        INSN_CHCRAM:         decode_str = decode_cheri_rd_rs1_insn("CH.cram", rvfi_data);

        INSN_CHSUB:        decode_str = decode_cheri_rd_cs1_cs2_insn("CH.csub", rvfi_data);
        INSN_CHMOVE:       decode_str = decode_cheri_cd_cs1_insn("CH.cmove", rvfi_data);
        INSN_CHTESTSUB:    decode_str = decode_cheri_rd_cs1_cs2_insn("CH.ctestsubset", rvfi_data);
        INSN_CHSETEQUAL:   decode_str = decode_cheri_rd_cs1_cs2_insn("CH.csetequalexact", rvfi_data);
        INSN_CHSETHIGH:    decode_str = decode_cheri_cd_cs1_rs2_insn("CH.csethigh", rvfi_data);
        //INSN_CHJALR:       decode_cheri_cd_cs1_insn("CH.jalr");
        INSN_CHCSRRW:      decode_str = decode_cheri_scrrw_insn(rvfi_data);
        INSN_AUIPC:        decode_str = decode_cheri_auipcc_insn(rvfi_data, cheri_pmode);
        INSN_AUICGP:       decode_str = decode_cheri_auicgp_insn(rvfi_data);

        // ATOMIC 
        INSN_LR:         decode_str = decode_amo_insn("lr.w", rvfi_data);
        INSN_SC:         decode_str = decode_amo_insn("sc.w", rvfi_data);
        INSN_AMOSWAP:    decode_str = decode_amo_insn("amoswap.w", rvfi_data);
        INSN_AMOADD:     decode_str = decode_amo_insn("amoadd.w", rvfi_data);
        INSN_AMOXOR:     decode_str = decode_amo_insn("amoxor.w", rvfi_data);
        INSN_AMOOR:      decode_str = decode_amo_insn("amoor.w", rvfi_data);
        INSN_AMOMIN:     decode_str = decode_amo_insn("amomin.w", rvfi_data);
        INSN_AMOMAX:     decode_str = decode_amo_insn("amomax.w", rvfi_data);
        INSN_AMOMINU:    decode_str = decode_amo_insn("amominu.w", rvfi_data);
        INSN_AMOMAXU:    decode_str = decode_amo_insn("amomaxu.w", rvfi_data);

        default:         decode_str = decode_mnemonic("INVALID", rvfi_data);
      endcase
    end

    return decode_str;
  endfunction




endpackage
