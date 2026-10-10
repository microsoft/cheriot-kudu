// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_ISA_INSTR -- layer 1 instruction coverage.
//
// Every coverpoint in this file is written against the architectural
// instruction word or architectural state at retire.  Nothing here names an
// RTL pipeline signal, an internal enum, a FIFO pointer or an FSM state; that
// is the mechanical test used throughout the plan to decide whether a
// coverpoint belongs in layer 1 (FC_ISA_*) or layer 2 (FC_MA_*).
//
// The retire tap is the one integration point in this coverage model that
// needs human review: it mirrors the tracer's own retire loop
// (tracer.sv:456-469) rather than being an independent decode.
//
// Bound to rtl/tracer.sv.
// See doc/functional_coverage_plan.md section 6.

module kudu_fcov_isa
  import cheri_pkg::*;
  import super_pkg::*;
  import tracer_pkg::*;
  import kudu_fcov_pkg::*;
#(
  // Use the tracer's shared type rather than maintaining a packed mirror.
  parameter int unsigned TW = $bits(instr_trace_t)
) (
  input logic          clk_i,
  input logic          rst_ni,

  input logic [TW-1:0] instr_trace_fifo [0:63],
  input logic [5:0]    rd_ptr,
  input logic [5:0]    rd_ptr_nxt,
  input logic [1:0]    cmt_instr_err,

  input logic [TW-1:0] amo_instr_q,
  input logic          amo_retire
);

`ifndef KUDU_FCOV_OFF

  initial begin
    assert (TW == $unsigned($bits(instr_trace_t)))
      else $fatal(1, "FC_ISA_INSTR trace port width differs from instr_trace_t");
  end

  wire cheri_cov_en = kudu_top.CHERIoTEn && tracer.cheri_pmode_i;
  logic [63:0] trace_cheri_mode_q;
  logic [63:0] final_cheri_mode_q;
  logic amo_cheri_mode_q;

  // instr_trace_t has no mode field. Keep a sideband at the tracer's enqueue
  // boundary, using its pointers/enables rather than reconstructing retirement.
  // Saved decode below still determines aliases expanded before this boundary.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      trace_cheri_mode_q <= '0;
      final_cheri_mode_q <= '0;
      amo_cheri_mode_q <= 1'b0;
    end else begin
      if (|cmt_instr_err)
        trace_cheri_mode_q <= '0;
      else if (!tracer.issue_cmplx && tracer.issued_instr[0].rvfi.valid) begin
        trace_cheri_mode_q[tracer.wr_ptr] <= cheri_cov_en;
        if (tracer.issued_instr[1].rvfi.valid)
          trace_cheri_mode_q[(tracer.wr_ptr + 1) % 64] <= cheri_cov_en;
      end
      if (tracer.issue_cmplx)
        amo_cheri_mode_q <= cheri_cov_en;
      if (tracer.tsafe_en_i) begin
        automatic int unsigned final_index = 32'(tracer.final_wr_ptr);
        for (int unsigned i = 32'(rd_ptr); i != 32'(rd_ptr_nxt); i = (i + 1) % 64) begin
          automatic instr_trace_t t = instr_trace_t'(instr_trace_fifo[i]);
          if (!t.is_amo) begin
            final_cheri_mode_q[final_index] <= trace_cheri_mode_q[i];
            final_index = (final_index + 1) % 64;
          end
        end
      end
    end
  end

  // These bits were saved with the instruction, not sampled from live pmode
  // at retirement. In RV32 mode the decoder marks CHERI-only opcodes illegal;
  // the compressed expander and AUIPC decode select the mode aliases earlier.
  function automatic bit has_legal_cheri_op(ir_dec_t d);
    return (|d.cheri_op) && !d.errs.illegal_insn && !d.errs.illegal_c_insn;
  endfunction

  typedef enum int unsigned {
    ISA_UNKNOWN,
    ISA_LUI, ISA_AUIPC, ISA_JAL, ISA_BEQ, ISA_BNE,
    ISA_BLT, ISA_BGE, ISA_BLTU, ISA_BGEU, ISA_SB,
    ISA_SH, ISA_SW, ISA_JALR, ISA_LB, ISA_LH,
    ISA_LW, ISA_LBU, ISA_LHU, ISA_ADDI, ISA_SLTI,
    ISA_SLTIU, ISA_XORI, ISA_ORI, ISA_ANDI, ISA_SLLI,
    ISA_SRLI, ISA_SRAI, ISA_FENCE, ISA_FENCEI, ISA_ECALL,
    ISA_EBREAK, ISA_MRET, ISA_DRET, ISA_WFI, ISA_ADD,
    ISA_SUB, ISA_SLL, ISA_SLT, ISA_SLTU, ISA_XOR,
    ISA_SRL, ISA_SRA, ISA_OR, ISA_AND, ISA_CSRRW,
    ISA_CSRRS, ISA_CSRRC, ISA_CSRRWI, ISA_CSRRSI, ISA_CSRRCI,
    ISA_MUL, ISA_MULH, ISA_MULHSU, ISA_MULHU, ISA_DIV,
    ISA_DIVU, ISA_REM, ISA_REMU, ISA_LR_W, ISA_SC_W,
    ISA_AMOSWAP, ISA_AMOADD, ISA_AMOXOR, ISA_AMOAND, ISA_AMOOR,
    ISA_AMOMIN, ISA_AMOMAX, ISA_AMOMINU, ISA_AMOMAXU, ISA_SH1ADD,
    ISA_SH2ADD, ISA_SH3ADD, ISA_ANDN, ISA_ORN, ISA_XNOR,
    ISA_ZEXTH, ISA_MIN, ISA_MINU, ISA_MAX, ISA_MAXU,
    ISA_ROL, ISA_ROR, ISA_CLMUL, ISA_CLMULR, ISA_CLMULH,
    ISA_BCLR, ISA_BEXT, ISA_BINV, ISA_BSET, ISA_CLZ,
    ISA_CTZ, ISA_CPOP, ISA_SEXTB, ISA_SEXTH, ISA_RORI,
    ISA_ORCB, ISA_REV8, ISA_BCLRI, ISA_BEXTI, ISA_BINVI,
    ISA_BSETI, ISA_C_ADDI4SPN, ISA_C_LW, ISA_C_SW, ISA_C_NOP,
    ISA_C_ADDI, ISA_C_LI, ISA_C_ADDI16SP, ISA_C_LUI, ISA_C_SLLI,
    ISA_C_LWSP, ISA_C_SRLI, ISA_C_SRAI, ISA_C_ANDI, ISA_C_BEQZ,
    ISA_C_BNEZ, ISA_C_SUB, ISA_C_XOR, ISA_C_OR, ISA_C_AND,
    ISA_C_JAL, ISA_C_J, ISA_C_JR, ISA_C_MV, ISA_C_EBREAK,
    ISA_C_JALR, ISA_C_ADD, ISA_C_SWSP, ISA_CSCRRW, ISA_CSETBOUNDS,
    ISA_CSETBOUNDSEX, ISA_CSETBOUNDSRNDN, ISA_CSEAL, ISA_CUNSEAL, ISA_CANDPERM,
    ISA_CSETADDR, ISA_CINCADDR, ISA_CSUB, ISA_CSETHIGH, ISA_CTESTSUB,
    ISA_CSETEQX, ISA_CGETPERM, ISA_CGETTYPE, ISA_CGETBASE, ISA_CGETHIGH,
    ISA_CGETTOP, ISA_CGETLEN, ISA_CGETTAG, ISA_CRRL, ISA_CRAM,
    ISA_CGETADDR, ISA_CMOVE, ISA_CCLEARTAG, ISA_CSETBOUNDSIMM, ISA_CINCADDRIMM,
    ISA_CLC, ISA_CSC, ISA_AUIPCC, ISA_AUICGP, ISA_C_INCADDR4CSPN,
    ISA_C_INCADDR16CSP, ISA_C_CLCSP, ISA_C_CLC, ISA_C_CSC, ISA_C_CSCSP
  } isa_instr_e;

  function automatic isa_instr_e instruction_id(instr_trace_t t, bit mode);
    logic [15:0] word16;
    word16 = t.rvfi.insn[15:0];
    if (t.ir_dec.errs.illegal_insn || t.ir_dec.errs.illegal_c_insn)
      return ISA_UNKNOWN;
    casez (t.rvfi.insn)
      32'b?????????????????????????0110111: return ISA_LUI;
      32'b?????????????????????????0010111: begin
        if (!t.ir_dec.cheri_op.auipcc) return ISA_AUIPC;
        if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_AUIPCC;
      end
      32'b?????????????????????????1101111: return ISA_JAL;
      32'b?????????????????000?????1100011: return ISA_BEQ;
      32'b?????????????????001?????1100011: return ISA_BNE;
      32'b?????????????????100?????1100011: return ISA_BLT;
      32'b?????????????????101?????1100011: return ISA_BGE;
      32'b?????????????????110?????1100011: return ISA_BLTU;
      32'b?????????????????111?????1100011: return ISA_BGEU;
      32'b?????????????????000?????0100011: return ISA_SB;
      32'b?????????????????001?????0100011: return ISA_SH;
      32'b?????????????????010?????0100011: return ISA_SW;
      32'b?????????????????000?????1100111: return ISA_JALR;
      32'b?????????????????000?????0000011: return ISA_LB;
      32'b?????????????????001?????0000011: return ISA_LH;
      32'b?????????????????010?????0000011: return ISA_LW;
      32'b?????????????????100?????0000011: return ISA_LBU;
      32'b?????????????????101?????0000011: return ISA_LHU;
      32'b?????????????????000?????0010011: return ISA_ADDI;
      32'b?????????????????010?????0010011: return ISA_SLTI;
      32'b?????????????????011?????0010011: return ISA_SLTIU;
      32'b?????????????????100?????0010011: return ISA_XORI;
      32'b?????????????????110?????0010011: return ISA_ORI;
      32'b?????????????????111?????0010011: return ISA_ANDI;
      32'b0000000??????????001?????0010011: return ISA_SLLI;
      32'b0000000??????????101?????0010011: return ISA_SRLI;
      32'b0100000??????????101?????0010011: return ISA_SRAI;
      32'b?????????????????000?????0001111: return ISA_FENCE;
      32'b?????????????????001?????0001111: return ISA_FENCEI;
      32'h0000_0073: return ISA_ECALL;
      32'h0010_0073: return ISA_EBREAK;
      32'h3020_0073: return ISA_MRET;
      32'h7b20_0073: return ISA_DRET;
      32'h1050_0073: return ISA_WFI;
      32'b0000000??????????000?????0110011: return ISA_ADD;
      32'b0100000??????????000?????0110011: return ISA_SUB;
      32'b0000000??????????001?????0110011: return ISA_SLL;
      32'b0000000??????????010?????0110011: return ISA_SLT;
      32'b0000000??????????011?????0110011: return ISA_SLTU;
      32'b0000000??????????100?????0110011: return ISA_XOR;
      32'b0000000??????????101?????0110011: return ISA_SRL;
      32'b0100000??????????101?????0110011: return ISA_SRA;
      32'b0000000??????????110?????0110011: return ISA_OR;
      32'b0000000??????????111?????0110011: return ISA_AND;
      32'b?????????????????001?????1110011: return ISA_CSRRW;
      32'b?????????????????010?????1110011: return ISA_CSRRS;
      32'b?????????????????011?????1110011: return ISA_CSRRC;
      32'b?????????????????101?????1110011: return ISA_CSRRWI;
      32'b?????????????????110?????1110011: return ISA_CSRRSI;
      32'b?????????????????111?????1110011: return ISA_CSRRCI;
      32'b0000001??????????000?????0110011: return ISA_MUL;
      32'b0000001??????????001?????0110011: return ISA_MULH;
      32'b0000001??????????010?????0110011: return ISA_MULHSU;
      32'b0000001??????????011?????0110011: return ISA_MULHU;
      32'b0000001??????????100?????0110011: return ISA_DIV;
      32'b0000001??????????101?????0110011: return ISA_DIVU;
      32'b0000001??????????110?????0110011: return ISA_REM;
      32'b0000001??????????111?????0110011: return ISA_REMU;
      32'b00010??00000?????010?????0101111: return ISA_LR_W;
      32'b00011????????????010?????0101111: return ISA_SC_W;
      32'b00001????????????010?????0101111: return ISA_AMOSWAP;
      32'b00000????????????010?????0101111: return ISA_AMOADD;
      32'b00100????????????010?????0101111: return ISA_AMOXOR;
      32'b01100????????????010?????0101111: return ISA_AMOAND;
      32'b01000????????????010?????0101111: return ISA_AMOOR;
      32'b10000????????????010?????0101111: return ISA_AMOMIN;
      32'b10100????????????010?????0101111: return ISA_AMOMAX;
      32'b11000????????????010?????0101111: return ISA_AMOMINU;
      32'b11100????????????010?????0101111: return ISA_AMOMAXU;
      32'b0010000??????????010?????0110011: return ISA_SH1ADD;
      32'b0010000??????????100?????0110011: return ISA_SH2ADD;
      32'b0010000??????????110?????0110011: return ISA_SH3ADD;
      32'b0100000??????????111?????0110011: return ISA_ANDN;
      32'b0100000??????????110?????0110011: return ISA_ORN;
      32'b0100000??????????100?????0110011: return ISA_XNOR;
      32'b000010000000?????100?????0110011: return ISA_ZEXTH;
      32'b0000101??????????100?????0110011: return ISA_MIN;
      32'b0000101??????????101?????0110011: return ISA_MINU;
      32'b0000101??????????110?????0110011: return ISA_MAX;
      32'b0000101??????????111?????0110011: return ISA_MAXU;
      32'b0110000??????????001?????0110011: return ISA_ROL;
      32'b0110000??????????101?????0110011: return ISA_ROR;
      32'b0000101??????????001?????0110011: return ISA_CLMUL;
      32'b0000101??????????010?????0110011: return ISA_CLMULR;
      32'b0000101??????????011?????0110011: return ISA_CLMULH;
      32'b0100100??????????001?????0110011: return ISA_BCLR;
      32'b0100100??????????101?????0110011: return ISA_BEXT;
      32'b0110100??????????001?????0110011: return ISA_BINV;
      32'b0010100??????????001?????0110011: return ISA_BSET;
      32'b011000000000?????001?????0010011: return ISA_CLZ;
      32'b011000000001?????001?????0010011: return ISA_CTZ;
      32'b011000000010?????001?????0010011: return ISA_CPOP;
      32'b011000000100?????001?????0010011: return ISA_SEXTB;
      32'b011000000101?????001?????0010011: return ISA_SEXTH;
      32'b0110000??????????101?????0010011: return ISA_RORI;
      32'b001010000111?????101?????0010011: return ISA_ORCB;
      32'b011010011000?????101?????0010011: return ISA_REV8;
      32'b0100100??????????001?????0010011: return ISA_BCLRI;
      32'b0100100??????????101?????0010011: return ISA_BEXTI;
      32'b0110100??????????001?????0010011: return ISA_BINVI;
      32'b0010100??????????001?????0010011: return ISA_BSETI;
      32'b0000001??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSCRRW;
      32'b0001000??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETBOUNDS;
      32'b0001001??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETBOUNDSEX;
      32'b0001010??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETBOUNDSRNDN;
      32'b0001011??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSEAL;
      32'b0001100??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CUNSEAL;
      32'b0001101??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CANDPERM;
      32'b0010000??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETADDR;
      32'b0010001??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CINCADDR;
      32'b0010100??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSUB;
      32'b0010110??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETHIGH;
      32'b0100000??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CTESTSUB;
      32'b0100001??????????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETEQX;
      32'b111111100000?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETPERM;
      32'b111111100001?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETTYPE;
      32'b111111100010?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETBASE;
      32'b111111110111?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETHIGH;
      32'b111111111000?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETTOP;
      32'b111111100011?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETLEN;
      32'b111111100100?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETTAG;
      32'b111111101000?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CRRL;
      32'b111111101001?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CRAM;
      32'b111111101111?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CGETADDR;
      32'b111111101010?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CMOVE;
      32'b111111101011?????000?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CCLEARTAG;
      32'b?????????????????010?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSETBOUNDSIMM;
      32'b?????????????????001?????1011011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CINCADDRIMM;
      32'b?????????????????011?????0000011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CLC;
      32'b?????????????????011?????0100011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_CSC;
      32'b?????????????????????????1111011: if (mode && has_legal_cheri_op(t.ir_dec)) return ISA_AUICGP;
      default: ;
    endcase
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h0000:16'h1fff]} &&
        word16[1:0] == 2'b00 && word16[12:5] != 0 &&
        !t.ir_dec.cheri_op.cincaddrimm)
      return ISA_C_ADDI4SPN;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b010???????????00})
      return ISA_C_LW;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b110???????????00})
      return ISA_C_SW;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'h0001})
      return ISA_C_NOP;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h0000:16'h1fff]} &&
        word16[1:0] == 2'b01 && word16[11:7] != 0 && {word16[12], word16[6:2]} != 0)
      return ISA_C_ADDI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h4000:16'h5fff]} &&
        word16[1:0] == 2'b01 && word16[11:7] != 0)
      return ISA_C_LI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h6000:16'h7fff]} &&
        word16[1:0] == 2'b01 && word16[11:7] == 2 && {word16[12], word16[6:2]} != 0 &&
        !t.ir_dec.cheri_op.cincaddrimm)
      return ISA_C_ADDI16SP;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h6000:16'h7fff]} &&
        word16[1:0] == 2'b01 && word16[11:7] != 0 && word16[11:7] != 2 && {word16[12], word16[6:2]} != 0)
      return ISA_C_LUI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h0000:16'h0fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0 && word16[6:2] != 0)
      return ISA_C_SLLI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h4000:16'h5fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0)
      return ISA_C_LWSP;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h8000:16'h83ff]} &&
        word16[1:0] == 2'b01 && word16[6:2] != 0)
      return ISA_C_SRLI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h8400:16'h87ff]} &&
        word16[1:0] == 2'b01 && word16[6:2] != 0)
      return ISA_C_SRAI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b100?10????????01})
      return ISA_C_ANDI;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b110???????????01})
      return ISA_C_BEQZ;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b111???????????01})
      return ISA_C_BNEZ;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b100011???00???01})
      return ISA_C_SUB;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b100011???01???01})
      return ISA_C_XOR;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b100011???10???01})
      return ISA_C_OR;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b100011???11???01})
      return ISA_C_AND;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b001???????????01})
      return ISA_C_JAL;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b101???????????01})
      return ISA_C_J;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h8000:16'h8fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0 && word16[6:2] == 0)
      return ISA_C_JR;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h8000:16'h8fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0 && word16[6:2] != 0)
      return ISA_C_MV;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'h9002})
      return ISA_C_EBREAK;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h9000:16'h9fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0 && word16[6:2] == 0)
      return ISA_C_JALR;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h9000:16'h9fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0 && word16[6:2] != 0)
      return ISA_C_ADD;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b110???????????10})
      return ISA_C_SWSP;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h0000:16'h1fff]} &&
        word16[1:0] == 2'b00 && word16[12:5] != 0 &&
        mode && has_legal_cheri_op(t.ir_dec))
      return ISA_C_INCADDR4CSPN;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h6000:16'h7fff]} &&
        word16[1:0] == 2'b01 && word16[11:7] == 2 && {word16[12], word16[6:2]} != 0 &&
        mode && has_legal_cheri_op(t.ir_dec))
      return ISA_C_INCADDR16CSP;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {[16'h6000:16'h7fff]} &&
        word16[1:0] == 2'b10 && word16[11:7] != 0 &&
        mode && has_legal_cheri_op(t.ir_dec))
      return ISA_C_CLCSP;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b011???????????00} &&
        mode && has_legal_cheri_op(t.ir_dec))
      return ISA_C_CLC;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b111???????????00} &&
        mode && has_legal_cheri_op(t.ir_dec))
      return ISA_C_CSC;
    if (t.rvfi.insn[1:0] != 2'b11 &&
        word16 inside {16'b111???????????10} &&
        mode && has_legal_cheri_op(t.ir_dec))
      return ISA_C_CSCSP;
    return ISA_UNKNOWN;
  endfunction

  function automatic bit instruction_mode(isa_instr_e instruction, bit mode);
    if (instruction >= ISA_CSCRRW) return mode;
    if (instruction inside {ISA_AUIPC, ISA_C_ADDI4SPN, ISA_C_ADDI16SP}) return !mode;
    return instruction != ISA_UNKNOWN;
  endfunction

  typedef enum int unsigned {
    OF_ARITHMETIC, OF_MULDIV, OF_BITMANIP, OF_CONTROL, OF_MEMORY,
    OF_ATOMIC, OF_SYSTEM, OF_CHERI
  } operand_family_e;

  function automatic operand_family_e operand_family(isa_instr_e instruction);
    if (instruction >= ISA_CSCRRW) return OF_CHERI;
    if (instruction inside {[ISA_MUL:ISA_REMU]}) return OF_MULDIV;
    if (instruction inside {[ISA_SH1ADD:ISA_BSETI]}) return OF_BITMANIP;
    if (instruction inside {[ISA_LR_W:ISA_AMOMAXU]}) return OF_ATOMIC;
    if (instruction inside {
        ISA_JAL, [ISA_BEQ:ISA_BGEU], ISA_JALR, ISA_C_BEQZ, ISA_C_BNEZ,
        ISA_C_JAL, ISA_C_J, ISA_C_JR, ISA_C_JALR}) return OF_CONTROL;
    if (instruction inside {
        ISA_SB, ISA_SH, ISA_SW, [ISA_LB:ISA_LHU],
        ISA_C_LW, ISA_C_SW, ISA_C_LWSP, ISA_C_SWSP}) return OF_MEMORY;
    if (instruction inside {
        [ISA_FENCE:ISA_WFI], [ISA_CSRRW:ISA_CSRRCI], ISA_C_EBREAK}) return OF_SYSTEM;
    return OF_ARITHMETIC;
  endfunction

  typedef enum int unsigned {
    OP_ZERO, OP_ONE, OP_MINUS_ONE, OP_MIN_INT, OP_MAX_INT, OP_POSITIVE, OP_NEGATIVE
  } operand_class_e;

  function automatic operand_class_e operand_class(logic [31:0] value);
    case (value)
      32'h0000_0000: return OP_ZERO;
      32'h0000_0001: return OP_ONE;
      32'hffff_ffff: return OP_MINUS_ONE;
      32'h8000_0000: return OP_MIN_INT;
      32'h7fff_ffff: return OP_MAX_INT;
      default: return value[31] ? OP_NEGATIVE : OP_POSITIVE;
    endcase
  endfunction

  function automatic int unsigned operand_size(logic [31:0] value);
    for (int i = 31; i >= 0; i--)
      if (value[i]) return i + 1;
    return 0;
  endfunction

  function automatic bit uses_source(isa_instr_e instruction, bit second);
    if (second)
      return instruction inside {
        [ISA_BEQ:ISA_SW], [ISA_ADD:ISA_AND], [ISA_MUL:ISA_REMU],
        [ISA_SC_W:ISA_XNOR], [ISA_MIN:ISA_BSET],
        ISA_C_SW, [ISA_C_SUB:ISA_C_AND], ISA_C_MV, ISA_C_ADD, ISA_C_SWSP,
        [ISA_CSETBOUNDS:ISA_CSETEQX], ISA_CSC, ISA_C_CSC, ISA_C_CSCSP
      };
    return !(instruction inside {
      ISA_UNKNOWN, ISA_LUI, ISA_AUIPC, ISA_JAL, [ISA_FENCE:ISA_WFI],
      [ISA_CSRRWI:ISA_CSRRCI], ISA_C_NOP, ISA_C_LI, ISA_C_LUI,
      ISA_C_JAL, ISA_C_J, ISA_C_MV, ISA_C_EBREAK, ISA_AUIPCC
    });
  endfunction

  function automatic bit capability_source(isa_instr_e instruction, bit mode, bit second);
    if (!mode || !uses_source(instruction, second)) return 1'b0;
    if (second)
      return instruction inside {
        ISA_CSEAL, ISA_CUNSEAL, ISA_CSUB, ISA_CTESTSUB, ISA_CSETEQX,
        ISA_CSC, ISA_C_CSC, ISA_C_CSCSP
      };
    return (instruction >= ISA_CSCRRW && !(instruction inside {ISA_CRRL, ISA_CRAM})) ||
           instruction inside {
             [ISA_SB:ISA_LHU], [ISA_LR_W:ISA_AMOMAXU],
             ISA_C_LW, ISA_C_SW, ISA_C_LWSP, ISA_C_SWSP, ISA_C_JR, ISA_C_JALR
           };
  endfunction

  function automatic bit source_register(isa_instr_e instruction, bit mode,
                                         bit second, int unsigned address);
    if (!instruction_mode(instruction, mode) || !uses_source(instruction, second) ||
        address > (mode ? 15 : 31)) return 1'b0;
    if (!second) begin
      if (instruction == ISA_CSCRRW) return address != 0;
      if (instruction == ISA_AUICGP) return address == 3;
      if (instruction inside {
          ISA_C_ADDI4SPN, ISA_C_ADDI16SP, ISA_C_LWSP, ISA_C_SWSP,
          ISA_C_INCADDR4CSPN, ISA_C_INCADDR16CSP, ISA_C_CLCSP, ISA_C_CSCSP})
        return address == 2;
      if (instruction inside {
          ISA_C_LW, ISA_C_SW, [ISA_C_SRLI:ISA_C_AND], ISA_C_CLC, ISA_C_CSC})
        return address inside {[8:15]};
      if (instruction inside {ISA_C_ADDI, ISA_C_SLLI, ISA_C_JR, ISA_C_JALR, ISA_C_ADD})
        return address != 0;
    end else begin
      if (instruction inside {ISA_C_SW, [ISA_C_SUB:ISA_C_AND], ISA_C_CSC})
        return address inside {[8:15]};
      if (instruction inside {ISA_C_MV, ISA_C_ADD}) return address != 0;
    end
    return 1'b1;
  endfunction

  function automatic bit instruction_available(isa_instr_e instruction);
    return instruction_mode(instruction, 0) ||
           (kudu_top.CHERIoTEn && instruction_mode(instruction, 1));
  endfunction

  function automatic bit source_available(instr_trace_t t, isa_instr_e instruction, bit second);
    return (!t.rvfi.trap || t.is_ex) && uses_source(instruction, second) &&
           (second || instruction != ISA_CSCRRW || t.rvfi.rs1_addr != 0);
  endfunction

  function automatic bit source_register_goal(isa_instr_e instruction, bit second,
                                              int unsigned address);
    return source_register(instruction, 0, second, address) ||
           (kudu_top.CHERIoTEn && source_register(instruction, 1, second, address));
  endfunction

  function automatic bit integer_source_goal(isa_instr_e instruction, bit second);
    return uses_source(instruction, second) &&
           ((instruction_mode(instruction, 0) && !capability_source(instruction, 0, second)) ||
            (kudu_top.CHERIoTEn && instruction_mode(instruction, 1) &&
             !capability_source(instruction, 1, second)));
  endfunction

  function automatic bit integer_register_goal(isa_instr_e instruction, bit second,
                                                int unsigned address);
    return (source_register(instruction, 0, second, address) &&
            !capability_source(instruction, 0, second)) ||
           (kudu_top.CHERIoTEn && source_register(instruction, 1, second, address) &&
            !capability_source(instruction, 1, second));
  endfunction

  function automatic bit capability_source_goal(isa_instr_e instruction, bit second);
    return kudu_top.CHERIoTEn && instruction_mode(instruction, 1) &&
           capability_source(instruction, 1, second);
  endfunction

  function automatic bit capability_destination(isa_instr_e instruction, bit mode);
    return mode && instruction inside {
      ISA_CSCRRW, ISA_CSETBOUNDS, ISA_CSETBOUNDSEX, ISA_CSETBOUNDSRNDN,
      ISA_CSEAL, ISA_CUNSEAL, ISA_CANDPERM, ISA_CSETADDR, ISA_CINCADDR,
      ISA_CSETHIGH, ISA_CMOVE, ISA_CCLEARTAG, ISA_CSETBOUNDSIMM, ISA_CINCADDRIMM,
      ISA_CLC, ISA_AUIPCC, ISA_AUICGP, ISA_C_INCADDR4CSPN, ISA_C_INCADDR16CSP,
      ISA_C_CLCSP, ISA_C_CLC, ISA_JAL, ISA_JALR, ISA_C_JAL, ISA_C_JALR
    };
  endfunction

  function automatic bit destination_available(instr_trace_t t, isa_instr_e instruction, bit mode);
    return capability_destination(instruction, mode) && !t.rvfi.trap &&
           t.rvfi.rd_addr != 0;
  endfunction

  typedef enum int unsigned {
    CF_TAG, CF_RESERVED, CF_CPERMS, CF_OTYPE, CF_CEXP, CF_BASE, CF_TOP
  } capability_field_e;

  function automatic bit destination_field_goal(isa_instr_e instruction,
                                                 capability_field_e field_id,
                                                 int unsigned value);
    if (!kudu_top.CHERIoTEn || !capability_destination(instruction, 1)) return 1'b0;
    if (field_id == CF_TAG && instruction inside {ISA_CCLEARTAG, ISA_CSETHIGH})
      return value == 0;
    if (field_id == CF_OTYPE) begin
      if (instruction == ISA_CUNSEAL) return value == 0;
      if (instruction inside {ISA_C_JAL, ISA_C_JALR}) return value inside {4, 5};
    end
    if (field_id == CF_CEXP) begin
      // CEXP complements EXP except denormal zero; bounds setting limits EXP.
      if (instruction == ISA_CSETBOUNDSIMM) return value == 0 || value >= 27;
      if (instruction == ISA_CSETBOUNDSRNDN) return value == 0 || value >= 8;
      if (instruction inside {ISA_CSETBOUNDS, ISA_CSETBOUNDSEX})
        return value == 0 || value >= 7;
    end
    return 1'b1;
  endfunction

  function automatic int unsigned mantissa_bin(capability_field_e field_id, int unsigned value);
    int unsigned midpoint;
    midpoint = (field_id == CF_BASE) ? 256 : 128;
    if (value <= 1) return value;
    if (value < midpoint - 1) return 2;
    if (value == midpoint - 1) return 3;
    if (value == midpoint) return 4;
    return value == 2 * midpoint - 1 ? 6 : 5;
  endfunction

  function automatic bit source_destination_goal(isa_instr_e instruction, bit second,
                                                  capability_field_e field_id,
                                                  int unsigned source_value,
                                                  int unsigned destination_value);
    bit transforms_cs1, copies_field;
    if (!capability_source_goal(instruction, second) ||
        !destination_field_goal(instruction, field_id, destination_value)) return 1'b0;
    transforms_cs1 = instruction inside {
      ISA_CSETBOUNDS, ISA_CSETBOUNDSEX, ISA_CSETBOUNDSRNDN, ISA_CSETBOUNDSIMM,
      ISA_CSEAL, ISA_CUNSEAL, ISA_CANDPERM, ISA_CSETADDR, ISA_CINCADDR,
      ISA_CMOVE, ISA_CCLEARTAG, ISA_CINCADDRIMM, ISA_AUICGP,
      ISA_C_INCADDR4CSPN, ISA_C_INCADDR16CSP
    };
    if (field_id == CF_TAG) begin
      if (!second && instruction == ISA_CMOVE) return source_value == destination_value;
      if (transforms_cs1) return destination_value <= source_value;
    end
    if (second) begin
      if (instruction == ISA_CUNSEAL && field_id == CF_CPERMS)
        return source_value[5] || !destination_value[5];
      return 1'b1;
    end
    if (!transforms_cs1) return 1'b1;

    copies_field = field_id == CF_RESERVED;
    case (field_id)
      CF_CPERMS: begin
        if (instruction == ISA_CANDPERM)
          return (expand_perms(CPERMS_W'(destination_value)) &
                  ~expand_perms(CPERMS_W'(source_value))) == 0;
        if (instruction == ISA_CUNSEAL)
          return destination_value == 32'(compress_perms(expand_perms(CPERMS_W'(source_value)), 0)) ||
                 destination_value == 32'(compress_perms(expand_perms(CPERMS_W'(source_value)) &
                                                         ~(PERMS_W'(1) << PERM_GL), 0));
        copies_field = 1'b1;
      end
      CF_OTYPE: copies_field = !(instruction inside {ISA_CSEAL, ISA_CUNSEAL});
      CF_CEXP: copies_field = !(instruction inside {
        ISA_CSETBOUNDS, ISA_CSETBOUNDSEX, ISA_CSETBOUNDSRNDN, ISA_CSETBOUNDSIMM
      });
      CF_BASE, CF_TOP: begin
        if (!(instruction inside {
            ISA_CSETBOUNDS, ISA_CSETBOUNDSEX, ISA_CSETBOUNDSRNDN, ISA_CSETBOUNDSIMM}))
          // Preserve grouped diagonal bins, not just equal raw mantissa values.
          return mantissa_bin(field_id, source_value) == mantissa_bin(field_id, destination_value);
      end
      default: ;
    endcase
    return !copies_field || source_value == destination_value;
  endfunction

  typedef enum int unsigned {
    IMM_NONE, IMM_I, IMM_S, IMM_B, IMM_U, IMM_J, IMM_SHAMT, IMM_ZIMM,
    IMM_U12, IMM_C20
  } immediate_kind_e;

  function automatic immediate_kind_e immediate_kind(isa_instr_e instruction);
    case (instruction)
      ISA_LUI, ISA_AUIPC, ISA_C_LUI: return IMM_U;
      ISA_AUIPCC, ISA_AUICGP: return IMM_C20;
      ISA_JAL, ISA_C_JAL, ISA_C_J: return IMM_J;
      ISA_BEQ, ISA_BNE, ISA_BLT, ISA_BGE, ISA_BLTU, ISA_BGEU,
      ISA_C_BEQZ, ISA_C_BNEZ: return IMM_B;
      ISA_SB, ISA_SH, ISA_SW, ISA_C_SW, ISA_C_SWSP,
      ISA_CSC, ISA_C_CSC, ISA_C_CSCSP: return IMM_S;
      ISA_SLLI, ISA_SRLI, ISA_SRAI, ISA_RORI, ISA_BCLRI, ISA_BEXTI,
      ISA_BINVI, ISA_BSETI, ISA_C_SLLI, ISA_C_SRLI, ISA_C_SRAI: return IMM_SHAMT;
      ISA_CSRRWI, ISA_CSRRSI, ISA_CSRRCI: return IMM_ZIMM;
      ISA_CSETBOUNDSIMM: return IMM_U12;
      ISA_JALR, ISA_LB, ISA_LH, ISA_LW, ISA_LBU, ISA_LHU,
      ISA_ADDI, ISA_SLTI, ISA_SLTIU, ISA_XORI, ISA_ORI, ISA_ANDI,
      ISA_C_ADDI4SPN, ISA_C_LW, ISA_C_ADDI, ISA_C_LI, ISA_C_ADDI16SP,
      ISA_C_LWSP, ISA_C_ANDI, ISA_CINCADDRIMM, ISA_CLC,
      ISA_C_INCADDR4CSPN, ISA_C_INCADDR16CSP, ISA_C_CLCSP, ISA_C_CLC:
        return IMM_I;
      default: return IMM_NONE;
    endcase
  endfunction

  function automatic logic [31:0] immediate_value(instr_trace_t t, isa_instr_e instruction);
    logic [31:0] word32;
    word32 = t.ir_dec.insn; // Expanded instruction, including compressed immediates.
    case (immediate_kind(instruction))
      IMM_I: return {{20{word32[31]}}, word32[31:20]};
      IMM_S: return {{20{word32[31]}}, word32[31:25], word32[11:7]};
      IMM_B: return {{19{word32[31]}}, word32[31], word32[7],
                     word32[30:25], word32[11:8], 1'b0};
      IMM_U: return {word32[31:12], 12'b0};
      IMM_J: return {{11{word32[31]}}, word32[31], word32[19:12],
                     word32[20], word32[30:21], 1'b0};
      IMM_SHAMT: return {27'b0, word32[24:20]};
      IMM_ZIMM: return {27'b0, word32[19:15]};
      IMM_U12: return {20'b0, word32[31:20]};
      IMM_C20: return {word32[31], word32[31:12], 11'b0};
      default: return '0;
    endcase
  endfunction

  typedef struct packed {
    logic signed [31:0] minimum;
    logic signed [31:0] maximum;
    logic [4:0] shift;
    bit nonzero;
  } immediate_range_t;

  function automatic immediate_range_t immediate_range(isa_instr_e instruction);
    immediate_range_t result;
    result = '{-2048, 2047, 0, 0};
    case (immediate_kind(instruction))
      IMM_NONE: result = '{0, 0, 0, 0};
      IMM_B: result = '{-4096, 4094, 1, 0};
      IMM_U: result = '{32'h8000_0000, 32'h7fff_f000, 12, 0};
      IMM_J: result = '{-1048576, 1048574, 1, 0};
      IMM_SHAMT, IMM_ZIMM: result = '{0, 31, 0, 0};
      IMM_U12: result = '{0, 4095, 0, 0};
      IMM_C20: result = '{-1073741824, 1073739776, 11, 0};
      default: ;
    endcase
    case (instruction)
      ISA_C_ADDI4SPN, ISA_C_INCADDR4CSPN: result = '{4, 1020, 2, 1};
      ISA_C_LW, ISA_C_SW: result = '{0, 124, 2, 0};
      ISA_C_LWSP, ISA_C_SWSP: result = '{0, 252, 2, 0};
      ISA_C_CLC, ISA_C_CSC: result = '{0, 248, 3, 0};
      ISA_C_CLCSP, ISA_C_CSCSP: result = '{0, 504, 3, 0};
      ISA_C_ADDI: result = '{-32, 31, 0, 1};
      ISA_C_LI, ISA_C_ANDI: result = '{-32, 31, 0, 0};
      ISA_C_ADDI16SP, ISA_C_INCADDR16CSP: result = '{-512, 496, 4, 1};
      ISA_C_LUI: result = '{-131072, 126976, 12, 1};
      ISA_C_SLLI, ISA_C_SRLI, ISA_C_SRAI: result = '{1, 31, 0, 1};
      ISA_C_JAL, ISA_C_J: result = '{-2048, 2046, 1, 0};
      ISA_C_BEQZ, ISA_C_BNEZ: result = '{-256, 254, 1, 0};
      default: ;
    endcase
    return result;
  endfunction

  typedef enum int unsigned {
    IV_ZERO, IV_ONE, IV_MINUS_ONE, IV_MINIMUM, IV_MAXIMUM, IV_NEGATIVE, IV_POSITIVE
  } immediate_class_e;

  function automatic immediate_class_e immediate_class(isa_instr_e instruction,
                                                        logic signed [31:0] value);
    immediate_range_t limits;
    limits = immediate_range(instruction);
    if (value == 0) return IV_ZERO;
    if (value == 1) return IV_ONE;
    if (value == -1) return IV_MINUS_ONE;
    if (value == limits.minimum) return IV_MINIMUM;
    if (value == limits.maximum) return IV_MAXIMUM;
    return value < 0 ? IV_NEGATIVE : IV_POSITIVE;
  endfunction

  function automatic bit immediate_goal(isa_instr_e instruction, bit mode,
                                       immediate_class_e value);
    immediate_range_t limits;
    limits = immediate_range(instruction);
    if (!instruction_mode(instruction, mode) || immediate_kind(instruction) == IMM_NONE)
      return 1'b0;
    case (value)
      IV_ZERO: return !limits.nonzero;
      IV_ONE: return limits.shift == 0 && limits.minimum <= 1;
      IV_MINUS_ONE: return limits.shift == 0 && limits.minimum < 0;
      IV_MINIMUM: return !(limits.minimum inside {-1, 0, 1});
      IV_MAXIMUM: return !(limits.maximum inside {-1, 0, 1});
      IV_NEGATIVE: return limits.minimum < -2;
      IV_POSITIVE: return limits.maximum > 2;
      default: return 1'b0;
    endcase
  endfunction

  // ==========================================================================
  // FC_ISA_INSTR - architectural instruction coverage
  // ==========================================================================
  covergroup cg_isa_instr with function sample(instr_trace_t t, bit cheri_mode,
                                              bit cheri_active);
    option.per_instance = 1;
    option.name         = "FC_ISA_INSTR";

    // Use the instruction's saved mode, not the live pin at retirement.
    cp_cheri_active: coverpoint cheri_active {
      option.weight = 0;
      bins mode[] = {[0:kudu_top.CHERIoTEn]};
    }

    // ======================================================================
    // 6.1 RV32I base
    //
    // Bins are the ISA encodings themselves rather than a decoded enum, so the
    // coverage model does not inherit a bug from the DUT's decoder.
    // ======================================================================

    cp_rv32i_u_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins lui    = {32'b?????????????????????????0110111};
      wildcard bins auipc  = {32'b?????????????????????????0010111}
                             iff (!t.ir_dec.cheri_op.auipcc);
    }
    cp_rv32i_uj_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins jal    = {32'b?????????????????????????1101111};
    }
    cp_rv32i_sb_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins beq    = {32'b?????????????????000?????1100011};
      wildcard bins bne    = {32'b?????????????????001?????1100011};
      wildcard bins blt    = {32'b?????????????????100?????1100011};
      wildcard bins bge    = {32'b?????????????????101?????1100011};
      wildcard bins bltu   = {32'b?????????????????110?????1100011};
      wildcard bins bgeu   = {32'b?????????????????111?????1100011};
    }
    cp_rv32i_s_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins sb     = {32'b?????????????????000?????0100011};
      wildcard bins sh     = {32'b?????????????????001?????0100011};
      wildcard bins sw     = {32'b?????????????????010?????0100011};
    }
    cp_rv32i_i_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins jalr   = {32'b?????????????????000?????1100111};
      wildcard bins lb     = {32'b?????????????????000?????0000011};
      wildcard bins lh     = {32'b?????????????????001?????0000011};
      wildcard bins lw     = {32'b?????????????????010?????0000011};
      wildcard bins lbu    = {32'b?????????????????100?????0000011};
      wildcard bins lhu    = {32'b?????????????????101?????0000011};

      wildcard bins addi   = {32'b?????????????????000?????0010011};
      wildcard bins slti   = {32'b?????????????????010?????0010011};
      wildcard bins sltiu  = {32'b?????????????????011?????0010011};
      wildcard bins xori   = {32'b?????????????????100?????0010011};
      wildcard bins ori    = {32'b?????????????????110?????0010011};
      wildcard bins andi   = {32'b?????????????????111?????0010011};
      wildcard bins slli   = {32'b0000000??????????001?????0010011};
      wildcard bins srli   = {32'b0000000??????????101?????0010011};
      wildcard bins srai   = {32'b0100000??????????101?????0010011};

      wildcard bins fence  = {32'b?????????????????000?????0001111};
      wildcard bins fencei = {32'b?????????????????001?????0001111};
      bins ecall  = {32'h0000_0073};
      bins ebreak = {32'h0010_0073};
      bins mret   = {32'h3020_0073};
      bins dret   = {32'h7b20_0073};
      bins wfi    = {32'h1050_0073};
    }
    cp_rv32i_r_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins add    = {32'b0000000??????????000?????0110011};
      wildcard bins sub    = {32'b0100000??????????000?????0110011};
      wildcard bins sll    = {32'b0000000??????????001?????0110011};
      wildcard bins slt    = {32'b0000000??????????010?????0110011};
      wildcard bins sltu   = {32'b0000000??????????011?????0110011};
      wildcard bins xor_   = {32'b0000000??????????100?????0110011};
      wildcard bins srl    = {32'b0000000??????????101?????0110011};
      wildcard bins sra    = {32'b0100000??????????101?????0110011};
      wildcard bins or_    = {32'b0000000??????????110?????0110011};
      wildcard bins and_   = {32'b0000000??????????111?????0110011};
    }
    cp_rv32i_csr: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins csrrw  = {32'b?????????????????001?????1110011};
      wildcard bins csrrs  = {32'b?????????????????010?????1110011};
      wildcard bins csrrc  = {32'b?????????????????011?????1110011};
      wildcard bins csrrwi = {32'b?????????????????101?????1110011};
      wildcard bins csrrsi = {32'b?????????????????110?????1110011};
      wildcard bins csrrci = {32'b?????????????????111?????1110011};
    }

    // ======================================================================
    // 6.2 M, A and B extensions
    // ======================================================================
    cp_rv32m_r_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins mul    = {32'b0000001??????????000?????0110011};
      wildcard bins mulh   = {32'b0000001??????????001?????0110011};
      wildcard bins mulhsu = {32'b0000001??????????010?????0110011};
      wildcard bins mulhu  = {32'b0000001??????????011?????0110011};
      wildcard bins div    = {32'b0000001??????????100?????0110011};
      wildcard bins divu   = {32'b0000001??????????101?????0110011};
      wildcard bins rem    = {32'b0000001??????????110?????0110011};
      wildcard bins remu   = {32'b0000001??????????111?????0110011};
    }

    cp_rv32a_r_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      wildcard bins lr_w      = {32'b00010??00000?????010?????0101111};
      wildcard bins sc_w      = {32'b00011????????????010?????0101111};
      wildcard bins amoswap   = {32'b00001????????????010?????0101111};
      wildcard bins amoadd    = {32'b00000????????????010?????0101111};
      wildcard bins amoxor    = {32'b00100????????????010?????0101111};
      wildcard bins amoand    = {32'b01100????????????010?????0101111};
      wildcard bins amoor     = {32'b01000????????????010?????0101111};
      wildcard bins amomin    = {32'b10000????????????010?????0101111};
      wildcard bins amomax    = {32'b10100????????????010?????0101111};
      wildcard bins amominu   = {32'b11000????????????010?????0101111};
      wildcard bins amomaxu   = {32'b11100????????????010?????0101111};
    }

    // Zba / Zbb / Zbc / Zbs, matching the alu_op_e set the design implements
    // (super_pkg.sv:293-326).  An unhit bin here is a real ISA hole.
    cp_rv32b_r_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      // Zba
      wildcard bins sh1add  = {32'b0010000??????????010?????0110011};
      wildcard bins sh2add  = {32'b0010000??????????100?????0110011};
      wildcard bins sh3add  = {32'b0010000??????????110?????0110011};
      // Zbb logic-with-negate
      wildcard bins andn    = {32'b0100000??????????111?????0110011};
      wildcard bins orn     = {32'b0100000??????????110?????0110011};
      wildcard bins xnor_   = {32'b0100000??????????100?????0110011};
      // Zbb register extend
      wildcard bins zexth   = {32'b000010000000?????100?????0110011};
      // Zbb min/max
      wildcard bins min_    = {32'b0000101??????????100?????0110011};
      wildcard bins minu    = {32'b0000101??????????101?????0110011};
      wildcard bins max_    = {32'b0000101??????????110?????0110011};
      wildcard bins maxu    = {32'b0000101??????????111?????0110011};
      // Zbb rotate / byte ops
      wildcard bins rol_    = {32'b0110000??????????001?????0110011};
      wildcard bins ror_    = {32'b0110000??????????101?????0110011};
      // Zbc
      wildcard bins clmul   = {32'b0000101??????????001?????0110011};
      wildcard bins clmulr  = {32'b0000101??????????010?????0110011};
      wildcard bins clmulh  = {32'b0000101??????????011?????0110011};
      // Zbs
      wildcard bins bclr    = {32'b0100100??????????001?????0110011};
      wildcard bins bext    = {32'b0100100??????????101?????0110011};
      wildcard bins binv    = {32'b0110100??????????001?????0110011};
      wildcard bins bset    = {32'b0010100??????????001?????0110011};
    }
    cp_rv32b_i_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr) {
      // Zbb count / extend / rotate / byte ops
      wildcard bins clz     = {32'b011000000000?????001?????0010011};
      wildcard bins ctz     = {32'b011000000001?????001?????0010011};
      wildcard bins cpop    = {32'b011000000010?????001?????0010011};
      wildcard bins sextb   = {32'b011000000100?????001?????0010011};
      wildcard bins sexth   = {32'b011000000101?????001?????0010011};
      wildcard bins rori    = {32'b0110000??????????101?????0010011};
      wildcard bins orcb    = {32'b001010000111?????101?????0010011};
      wildcard bins rev8    = {32'b011010011000?????101?????0010011};
      // Zbs immediate
      wildcard bins bclri   = {32'b0100100??????????001?????0010011};
      wildcard bins bexti   = {32'b0100100??????????101?????0010011};
      wildcard bins binvi   = {32'b0110100??????????001?????0010011};
      wildcard bins bseti   = {32'b0010100??????????001?????0010011};
    }

    // ======================================================================
    // 6.3 Compressed encodings
    //
    // Sampled from the original 16-bit word, not the expanded 32-bit form, so
    // that a compressed encoding and its 32-bit equivalent are distinguished.
    // Constrained bins use finite ranges with item filters, not overlapping
    // wildcard patterns. HINTs (except canonical C.NOP), reserved encodings
    // and RV64/custom shift encodings do not count as these instructions.
    // ======================================================================
    cp_rv32c_ciw_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      bins c_addi4spn = {[16'h0000:16'h1fff]}
        with (item[1:0] == 2'b00 && item[12:5] != 0)
        iff (!t.ir_dec.cheri_op.cincaddrimm);
    }
    cp_rv32c_cl_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_lw       = {16'b010???????????00};
    }
    cp_rv32c_cs_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_sw       = {16'b110???????????00};
    }
    cp_rv32c_ci_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      bins          c_nop      = {16'h0001};
      bins c_addi = {[16'h0000:16'h1fff]}
        with (item[1:0] == 2'b01 && item[11:7] != 0 && {item[12], item[6:2]} != 0);
      bins c_li = {[16'h4000:16'h5fff]}
        with (item[1:0] == 2'b01 && item[11:7] != 0);
      bins c_addi16sp = {[16'h6000:16'h7fff]}
        with (item[1:0] == 2'b01 && item[11:7] == 2 && {item[12], item[6:2]} != 0)
        iff (!t.ir_dec.cheri_op.cincaddrimm);
      bins c_lui = {[16'h6000:16'h7fff]}
        with (item[1:0] == 2'b01 && item[11:7] != 0 && item[11:7] != 2 &&
              {item[12], item[6:2]} != 0);
      bins c_slli = {[16'h0000:16'h0fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0 && item[6:2] != 0);
      bins c_lwsp = {[16'h4000:16'h5fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0);
    }
    cp_rv32c_cb_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      bins c_srli = {[16'h8000:16'h83ff]}
        with (item[1:0] == 2'b01 && item[6:2] != 0);
      bins c_srai = {[16'h8400:16'h87ff]}
        with (item[1:0] == 2'b01 && item[6:2] != 0);
      wildcard bins c_andi     = {16'b100?10????????01};
      wildcard bins c_beqz     = {16'b110???????????01};
      wildcard bins c_bnez     = {16'b111???????????01};
    }
    cp_rv32c_ca_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_sub      = {16'b100011???00???01};
      wildcard bins c_xor      = {16'b100011???01???01};
      wildcard bins c_or       = {16'b100011???10???01};
      wildcard bins c_and      = {16'b100011???11???01};
    }
    cp_rv32c_cj_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_jal      = {16'b001???????????01};
      wildcard bins c_j        = {16'b101???????????01};
    }
    cp_rv32c_cr_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      bins c_jr = {[16'h8000:16'h8fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0 && item[6:2] == 0);
      bins c_mv = {[16'h8000:16'h8fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0 && item[6:2] != 0);
      bins          c_ebreak   = {16'h9002};
      bins c_jalr = {[16'h9000:16'h9fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0 && item[6:2] == 0);
      bins c_add = {[16'h9000:16'h9fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0 && item[6:2] != 0);
    }
    cp_rv32c_css_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_swsp     = {16'b110???????????10};
    }

    // ======================================================================
    // 6.4 CHERIoT-1.0 instructions
    //
    // Match retired encodings, using saved decode metadata only to qualify
    // CHERI legality / mode aliases. Mode is saved at enqueue, so a later
    // mode switch cannot reinterpret or suppress a queued instruction.
    // ======================================================================
    cp_cscrrw: coverpoint t.rvfi.insn iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins hit = {32'b0000001??????????000?????1011011};
    }
    cp_cheriot_r_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins csetbounds     = {32'b0001000??????????000?????1011011};
      wildcard bins csetboundsex   = {32'b0001001??????????000?????1011011};
      wildcard bins csetboundsrndn = {32'b0001010??????????000?????1011011};
      wildcard bins cseal         = {32'b0001011??????????000?????1011011};
      wildcard bins cunseal       = {32'b0001100??????????000?????1011011};
      wildcard bins candperm      = {32'b0001101??????????000?????1011011};
      wildcard bins csetaddr      = {32'b0010000??????????000?????1011011};
      wildcard bins cincaddr      = {32'b0010001??????????000?????1011011};
      wildcard bins csub          = {32'b0010100??????????000?????1011011};
      wildcard bins csethigh      = {32'b0010110??????????000?????1011011};
      wildcard bins ctestsub      = {32'b0100000??????????000?????1011011};
      wildcard bins cseteqx       = {32'b0100001??????????000?????1011011};
      // Unary operations use the R-format rs2 field as an operation selector.
      wildcard bins cgetperm      = {32'b111111100000?????000?????1011011};
      wildcard bins cgettype      = {32'b111111100001?????000?????1011011};
      wildcard bins cgetbase      = {32'b111111100010?????000?????1011011};
      wildcard bins cgethigh      = {32'b111111110111?????000?????1011011};
      wildcard bins cgettop       = {32'b111111111000?????000?????1011011};
      wildcard bins cgetlen       = {32'b111111100011?????000?????1011011};
      wildcard bins cgettag       = {32'b111111100100?????000?????1011011};
      wildcard bins crrl          = {32'b111111101000?????000?????1011011};
      wildcard bins cram          = {32'b111111101001?????000?????1011011};
      wildcard bins cgetaddr      = {32'b111111101111?????000?????1011011};
      wildcard bins cmove         = {32'b111111101010?????000?????1011011};
      wildcard bins ccleartag     = {32'b111111101011?????000?????1011011};
    }
    cp_cheriot_i_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins csetboundsimm = {32'b?????????????????010?????1011011};
      wildcard bins cincaddrimm   = {32'b?????????????????001?????1011011};
      wildcard bins clc           = {32'b?????????????????011?????0000011};
    }
    cp_cheriot_s_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins csc = {32'b?????????????????011?????0100011};
    }
    cp_cheriot_u_type: coverpoint t.rvfi.insn iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins auipcc = {32'b?????????????????????????0010111};
      wildcard bins auicgp = {32'b?????????????????????????1111011};
    }
    cp_cheriot_ciw_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                              (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      bins c_incaddr4cspn = {[16'h0000:16'h1fff]}
        with (item[1:0] == 2'b00 && item[12:5] != 0);
    }
    cp_cheriot_ci_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                             (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      bins c_incaddr16csp = {[16'h6000:16'h7fff]}
        with (item[1:0] == 2'b01 && item[11:7] == 2 && {item[12], item[6:2]} != 0);
      bins c_clcsp = {[16'h6000:16'h7fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0);
    }
    cp_cheriot_cl_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                             (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins c_clc = {16'b011???????????00};
    }
    cp_cheriot_cs_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                             (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins c_csc = {16'b111???????????00};
    }
    cp_cheriot_css_type: coverpoint t.rvfi.insn[15:0] iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                              (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins c_cscsp = {16'b111???????????10};
    }

    // Cross every instruction encoding with its saved operating mode.
    // Ignore impossible aliases statically; iff alone does not remove goals.
    x_rv32i_u_type_pmode: cross cp_rv32i_u_type, cp_cheri_active iff (!t.rvfi.intr) {
      ignore_bins cheri_alias = binsof(cp_rv32i_u_type.auipc) &&
                                binsof(cp_cheri_active) intersect {1};
    }
    x_rv32i_uj_type_pmode: cross cp_rv32i_uj_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32i_sb_type_pmode: cross cp_rv32i_sb_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32i_s_type_pmode: cross cp_rv32i_s_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32i_i_type_pmode: cross cp_rv32i_i_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32i_r_type_pmode: cross cp_rv32i_r_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32i_csr_pmode: cross cp_rv32i_csr, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32m_r_type_pmode: cross cp_rv32m_r_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32a_r_type_pmode: cross cp_rv32a_r_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32b_r_type_pmode: cross cp_rv32b_r_type, cp_cheri_active iff (!t.rvfi.intr) ;
    x_rv32b_i_type_pmode: cross cp_rv32b_i_type, cp_cheri_active iff (!t.rvfi.intr) ;

    x_rv32c_ciw_type_pmode: cross cp_rv32c_ciw_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      ignore_bins cheri_alias = binsof(cp_cheri_active) intersect {1};
    }
    x_rv32c_cl_type_pmode: cross cp_rv32c_cl_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;
    x_rv32c_cs_type_pmode: cross cp_rv32c_cs_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;
    x_rv32c_ci_type_pmode: cross cp_rv32c_ci_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) {
      ignore_bins cheri_alias = binsof(cp_rv32c_ci_type.c_addi16sp) &&
                                binsof(cp_cheri_active) intersect {1};
    }
    x_rv32c_cb_type_pmode: cross cp_rv32c_cb_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;
    x_rv32c_ca_type_pmode: cross cp_rv32c_ca_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;
    x_rv32c_cj_type_pmode: cross cp_rv32c_cj_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;
    x_rv32c_cr_type_pmode: cross cp_rv32c_cr_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;
    x_rv32c_css_type_pmode: cross cp_rv32c_css_type, cp_cheri_active iff (!t.rvfi.intr && t.rvfi.insn[1:0] != 2'b11) ;

    x_cscrrw_pmode: cross cp_cscrrw, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_r_type_pmode: cross cp_cheriot_r_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_i_type_pmode: cross cp_cheriot_i_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_s_type_pmode: cross cp_cheriot_s_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_u_type_pmode: cross cp_cheriot_u_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_ciw_type_pmode: cross cp_cheriot_ciw_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_ci_type_pmode: cross cp_cheriot_ci_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_cl_type_pmode: cross cp_cheriot_cl_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_cs_type_pmode: cross cp_cheriot_cs_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_css_type_pmode: cross cp_cheriot_css_type, cp_cheri_active iff (!t.rvfi.intr && cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }

    // ======================================================================
    // 6.5 Architectural operands and results
    // ======================================================================
    // All 32 architectural registers must be written and read.  x0 is split
    // out because it is the one register with defined special behaviour.
    cp_rd: coverpoint t.rvfi.rd_addr iff (|t.rvfi.rd_wdata || t.rvfi.rd_addr != 5'd0) {
      bins x0     = {5'd0};
      bins reg_[] = {[1:31]};
    }

    // Value classes on the architectural operands: zero, all-ones, the sign
    // boundary and the two extremes are where ALU corner cases live.
    cp_rd_class:  coverpoint fcov_vclass(t.rvfi.rd_wdata[31:0]);

    // The capability tag on an architectural register write.
    cp_rd_tag: coverpoint t.rvfi.rd_wdata[$bits(t.rvfi.rd_wdata)-1] iff (cheri_mode) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      bins no_tag   = {1'b0};
      bins has_tag  = {1'b1};
    }

    cp_mem_rmask: coverpoint t.rvfi.mem_rmask {
      bins none    = {4'b0000};
      bins byte_[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
      bins half_[] = {4'b0011, 4'b1100};
      bins word_   = {4'b1111};
      bins other   = default;
    }
    cp_mem_wmask: coverpoint t.rvfi.mem_wmask {
      bins none    = {4'b0000};
      bins byte_[] = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
      bins half_[] = {4'b0011, 4'b1100};
      bins word_   = {4'b1111};
      bins other   = default;
    }
    cp_mem_is_cap: coverpoint t.rvfi.mem_is_cap
      iff (cheri_mode && (|t.rvfi.mem_rmask || |t.rvfi.mem_wmask)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
    }
    cp_mem_align:  coverpoint t.rvfi.mem_addr[1:0] iff (|t.rvfi.mem_rmask || |t.rvfi.mem_wmask) {
      bins a[] = {[0:3]};
    }

    // pc_wdata != pc_rdata + size means the instruction redirected control
    // flow; sequential and taken must both be seen for every branch.
    cp_is_comp: coverpoint t.ir_dec.is_comp;
    cp_taken:   coverpoint (t.rvfi.pc_wdata !=
                            (t.rvfi.pc_rdata + (t.ir_dec.is_comp ? 32'd2 : 32'd4)))
                iff (t.ir_dec.is_branch || t.ir_dec.is_jal || t.ir_dec.is_jalr) {
      bins sequential = {1'b0};
      bins redirected = {1'b1};
    }
    // A branch to a misaligned target is the architectural corner that must
    // raise an instruction-address-misaligned fault.
    cp_target_align: coverpoint t.rvfi.pc_wdata[1:0] {
      bins aligned4 = {2'b00};
      bins aligned2 = {2'b10};
      bins odd      = {2'b01, 2'b11};
    }

    cp_mode: coverpoint t.rvfi.mode { bins m[] = {[0:3]}; }
    cp_intr: coverpoint t.rvfi.intr { bins hit = {1'b1}; }
    cp_trap: coverpoint t.rvfi.trap;
  endgroup

  cg_isa_instr u_cg_isa_instr = new();

  // Operand axes follow the per-instruction cross approach used by Ibex.
  // Helper points have zero weight: only instruction-qualified crosses are goals.
  covergroup cg_isa_operands with function sample(
      instr_trace_t t, isa_instr_e instruction, bit mode, logic [31:0] immediate,
      mem_cap_t cs1, mem_cap_t cs2, mem_cap_t cd);
    option.per_instance = 1;
    option.name = "FC_ISA_OPERANDS";

    cp_instruction: coverpoint instruction {
      option.weight = 0;
      ignore_bins unknown = {ISA_UNKNOWN};
    }
    cp_pmode: coverpoint mode {
      option.weight = 0;
      bins mode[] = {[0:kudu_top.CHERIoTEn]};
    }
    cp_rs1_addr: coverpoint t.rvfi.rs1_addr iff (source_available(t, instruction, 0)) {
      option.weight = 0;
      bins registers[] = {[0:31]};
    }
    cp_rs2_addr: coverpoint t.rvfi.rs2_addr iff (source_available(t, instruction, 1)) {
      option.weight = 0;
      bins registers[] = {[0:31]};
    }
    cp_rs1_data: coverpoint operand_class(t.rvfi.rs1_rdata[31:0])
        iff (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0)) { option.weight = 0; }
    cp_rs2_data: coverpoint operand_class(t.rvfi.rs2_rdata[31:0])
        iff (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1)) { option.weight = 0; }
    cp_rs1_size: coverpoint operand_size(t.rvfi.rs1_rdata[31:0])
        iff (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins bits[] = {[0:32]};
    }
    cp_rs2_size: coverpoint operand_size(t.rvfi.rs2_rdata[31:0])
        iff (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins bits[] = {[0:32]};
    }
    cp_immediate: coverpoint immediate_class(instruction, immediate)
        iff ((!t.rvfi.trap || t.is_ex) && immediate_kind(instruction) != IMM_NONE) { option.weight = 0; }

    // RVFI stores reg2mcap() output, not the internal register capability layout.
    cp_cs1_tag: coverpoint cs1.valid iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins tag[] = {0, 1};
    }
    cp_cs1_reserved: coverpoint cs1.rsvd iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins value[] = {0, 1};
    }
    cp_cs1_cperms: coverpoint cs1.cperms iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins permissions[] = {[0:63]};
    }
    cp_cs1_otype: coverpoint cs1.otype iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins unsealed = {0};
      bins sentry[] = {[1:5]};
      bins sealed[] = {[6:7]};
    }
    cp_cs1_cexp: coverpoint cs1.cexp iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins exponent[] = {[0:31]};
    }
    cp_cs1_base: coverpoint cs1.base9 iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:254]};
      bins boundary[] = {255, 256};
      bins high = {[257:510]};
      bins maximum = {511};
    }
    cp_cs1_top: coverpoint cs1.top8 iff (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:126]};
      bins boundary[] = {127, 128};
      bins high = {[129:254]};
      bins maximum = {255};
    }
    cp_cs2_tag: coverpoint cs2.valid iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins tag[] = {0, 1};
    }
    cp_cs2_reserved: coverpoint cs2.rsvd iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins value[] = {0, 1};
    }
    cp_cs2_cperms: coverpoint cs2.cperms iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins permissions[] = {[0:63]};
    }
    cp_cs2_otype: coverpoint cs2.otype iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins unsealed = {0};
      bins sentry[] = {[1:5]};
      bins sealed[] = {[6:7]};
    }
    cp_cs2_cexp: coverpoint cs2.cexp iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins exponent[] = {[0:31]};
    }
    cp_cs2_base: coverpoint cs2.base9 iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:254]};
      bins boundary[] = {255, 256};
      bins high = {[257:510]};
      bins maximum = {511};
    }
    cp_cs2_top: coverpoint cs2.top8 iff (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) {
      option.weight = 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:126]};
      bins boundary[] = {127, 128};
      bins high = {[129:254]};
      bins maximum = {255};
    }

    cp_cd_tag: coverpoint cd.valid iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins tag[] = {0, 1};
    }
    cp_cd_reserved: coverpoint cd.rsvd iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins value[] = {0, 1};
    }
    cp_cd_cperms: coverpoint cd.cperms iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins permissions[] = {[0:63]};
    }
    cp_cd_otype: coverpoint cd.otype iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins unsealed = {0};
      bins sentry[] = {[1:5]};
      bins sealed[] = {[6:7]};
    }
    cp_cd_cexp: coverpoint cd.cexp iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins exponent[] = {[0:31]};
    }
    cp_cd_base: coverpoint cd.base9 iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:254]};
      bins boundary[] = {255, 256};
      bins high = {[257:510]};
      bins maximum = {511};
    }
    cp_cd_top: coverpoint cd.top8 iff (destination_available(t, instruction, mode)) {
      option.weight = 0;
      bins zero = {0};
      bins one = {1};
      bins low = {[2:126]};
      bins boundary[] = {127, 128};
      bins high = {[129:254]};
      bins maximum = {255};
    }

    x_instruction_pmode: cross cp_instruction, cp_pmode {
      ignore_bins unused = x_instruction_pmode with
        (!instruction_mode(isa_instr_e'(cp_instruction), cp_pmode));
    }

    // BEGIN GENERATED FAMILY CROSSES

    // Regenerate with fcov/generate_isa_operand_crosses.py --write.

    // ARITHMETIC: only actual source/destination roles contribute goals.

    x_arithmetic_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_arithmetic_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_arithmetic_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_arithmetic_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_arithmetic_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_arithmetic_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO));
    }

    x_arithmetic_rs2_size: cross cp_instruction, cp_rs2_size
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_arithmetic_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_arithmetic_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 0) && source_available(t, instruction, 1))) {
      ignore_bins unused = x_arithmetic_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr));
    }

    x_arithmetic_source_data: cross cp_instruction, cp_rs1_data, cp_rs2_data
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0) && source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_arithmetic_source_data with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_arithmetic_immediate: cross cp_instruction, cp_immediate
        iff (operand_family(instruction) == OF_ARITHMETIC && (!t.rvfi.trap || t.is_ex)) {
      ignore_bins unused = x_arithmetic_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_arithmetic_rs1_immediate: cross cp_instruction, cp_rs1_data, cp_immediate
        iff (operand_family(instruction) == OF_ARITHMETIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_arithmetic_rs1_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ARITHMETIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    // MULDIV: only actual source/destination roles contribute goals.

    x_muldiv_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_MULDIV && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_muldiv_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MULDIV ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_muldiv_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_MULDIV && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_muldiv_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MULDIV ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_muldiv_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data
        iff (operand_family(instruction) == OF_MULDIV && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_muldiv_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MULDIV ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO));
    }

    x_muldiv_rs2_size: cross cp_instruction, cp_rs2_size
        iff (operand_family(instruction) == OF_MULDIV && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_muldiv_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MULDIV ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_muldiv_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr
        iff (operand_family(instruction) == OF_MULDIV && (source_available(t, instruction, 0) && source_available(t, instruction, 1))) {
      ignore_bins unused = x_muldiv_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MULDIV ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr));
    }

    x_muldiv_source_data: cross cp_instruction, cp_rs1_data, cp_rs2_data
        iff (operand_family(instruction) == OF_MULDIV && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0) && source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_muldiv_source_data with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MULDIV ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    // BITMANIP: only actual source/destination roles contribute goals.

    x_bitmanip_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_bitmanip_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_bitmanip_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_bitmanip_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_bitmanip_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_bitmanip_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO));
    }

    x_bitmanip_rs2_size: cross cp_instruction, cp_rs2_size
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_bitmanip_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_bitmanip_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 0) && source_available(t, instruction, 1))) {
      ignore_bins unused = x_bitmanip_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr));
    }

    x_bitmanip_source_data: cross cp_instruction, cp_rs1_data, cp_rs2_data
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0) && source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_bitmanip_source_data with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_bitmanip_immediate: cross cp_instruction, cp_immediate
        iff (operand_family(instruction) == OF_BITMANIP && (!t.rvfi.trap || t.is_ex)) {
      ignore_bins unused = x_bitmanip_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_bitmanip_rs1_immediate: cross cp_instruction, cp_rs1_data, cp_immediate
        iff (operand_family(instruction) == OF_BITMANIP && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_bitmanip_rs1_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_BITMANIP ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    // CONTROL: only actual source/destination roles contribute goals.

    x_control_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_control_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_control_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_control_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_control_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO));
    }

    x_control_rs2_size: cross cp_instruction, cp_rs2_size
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_control_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_control_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && source_available(t, instruction, 1))) {
      ignore_bins unused = x_control_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr));
    }

    x_control_source_data: cross cp_instruction, cp_rs1_data, cp_rs2_data
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0) && source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_control_source_data with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_control_immediate: cross cp_instruction, cp_immediate
        iff (operand_family(instruction) == OF_CONTROL && (!t.rvfi.trap || t.is_ex)) {
      ignore_bins unused = x_control_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_control_rs1_immediate: cross cp_instruction, cp_rs1_data, cp_immediate
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_control_rs1_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_control_rs2_immediate: cross cp_instruction, cp_rs2_data, cp_immediate
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_control_rs2_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_control_cs1_address: cross cp_instruction, cp_rs1_addr, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_address with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !source_register(isa_instr_e'(cp_instruction), 1, 0, cp_rs1_addr) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         (cp_rs1_addr == 0 && cp_cs1_tag != 0));
    }

    x_control_cs1_cd_tag: cross cp_instruction, cp_cs1_tag, cp_cd_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_tag with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_TAG, cp_cs1_tag, cp_cd_tag) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_reserved: cross cp_instruction, cp_cs1_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cd_reserved: cross cp_instruction, cp_cs1_reserved, cp_cd_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_RESERVED, cp_cs1_reserved, cp_cd_reserved) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cperms: cross cp_instruction, cp_cs1_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cd_cperms: cross cp_instruction, cp_cs1_cperms, cp_cd_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_CPERMS, cp_cs1_cperms, cp_cd_cperms) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_otype: cross cp_instruction, cp_cs1_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cd_otype: cross cp_instruction, cp_cs1_otype, cp_cd_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_OTYPE, cp_cs1_otype, cp_cd_otype) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cexp: cross cp_instruction, cp_cs1_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cd_cexp: cross cp_instruction, cp_cs1_cexp, cp_cd_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_CEXP, cp_cs1_cexp, cp_cd_cexp) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_base: cross cp_instruction, cp_cs1_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cd_base: cross cp_instruction, cp_cs1_base, cp_cd_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_BASE, cp_cs1_base, cp_cd_base) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_top: cross cp_instruction, cp_cs1_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cs1_cd_top: cross cp_instruction, cp_cs1_top, cp_cd_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_CONTROL && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cs1_cd_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_TOP, cp_cs1_top, cp_cd_top) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_control_cd_no_cs1_tag: cross cp_instruction, cp_cd_tag
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_tag with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_TAG, cp_cd_tag) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_control_cd_no_cs1_reserved: cross cp_instruction, cp_cd_reserved
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_RESERVED, cp_cd_reserved) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_control_cd_no_cs1_cperms: cross cp_instruction, cp_cd_cperms
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_CPERMS, cp_cd_cperms) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_control_cd_no_cs1_otype: cross cp_instruction, cp_cd_otype
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_OTYPE, cp_cd_otype) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_control_cd_no_cs1_cexp: cross cp_instruction, cp_cd_cexp
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_CEXP, cp_cd_cexp) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_control_cd_no_cs1_base: cross cp_instruction, cp_cd_base
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_BASE, cp_cd_base) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_control_cd_no_cs1_top: cross cp_instruction, cp_cd_top
        iff (operand_family(instruction) == OF_CONTROL && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_control_cd_no_cs1_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CONTROL ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_TOP, cp_cd_top) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    // MEMORY: only actual source/destination roles contribute goals.

    x_memory_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_memory_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_memory_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_memory_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_memory_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_memory_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO));
    }

    x_memory_rs2_size: cross cp_instruction, cp_rs2_size
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_memory_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_memory_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && source_available(t, instruction, 1))) {
      ignore_bins unused = x_memory_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr));
    }

    x_memory_source_data: cross cp_instruction, cp_rs1_data, cp_rs2_data
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0) && source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_memory_source_data with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_memory_immediate: cross cp_instruction, cp_immediate
        iff (operand_family(instruction) == OF_MEMORY && (!t.rvfi.trap || t.is_ex)) {
      ignore_bins unused = x_memory_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_memory_rs1_immediate: cross cp_instruction, cp_rs1_data, cp_immediate
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_memory_rs1_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_memory_rs2_immediate: cross cp_instruction, cp_rs2_data, cp_immediate
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_memory_rs2_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    x_memory_cs1_address: cross cp_instruction, cp_rs1_addr, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_address with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !source_register(isa_instr_e'(cp_instruction), 1, 0, cp_rs1_addr) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         (cp_rs1_addr == 0 && cp_cs1_tag != 0));
    }

    x_memory_cs1_reserved: cross cp_instruction, cp_cs1_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_memory_cs1_cperms: cross cp_instruction, cp_cs1_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_memory_cs1_otype: cross cp_instruction, cp_cs1_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_memory_cs1_cexp: cross cp_instruction, cp_cs1_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_memory_cs1_base: cross cp_instruction, cp_cs1_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_memory_cs1_top: cross cp_instruction, cp_cs1_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_MEMORY && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_memory_cs1_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_MEMORY ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    // ATOMIC: only actual source/destination roles contribute goals.

    x_atomic_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_atomic_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_atomic_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_atomic_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_atomic_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_atomic_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO));
    }

    x_atomic_rs2_size: cross cp_instruction, cp_rs2_size
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_atomic_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_atomic_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && source_available(t, instruction, 1))) {
      ignore_bins unused = x_atomic_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr));
    }

    x_atomic_source_data: cross cp_instruction, cp_rs1_data, cp_rs2_data
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0) && source_available(t, instruction, 1) && !capability_source(instruction, mode, 1))) {
      ignore_bins unused = x_atomic_source_data with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1));
    }

    x_atomic_cs1_address: cross cp_instruction, cp_rs1_addr, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_address with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !source_register(isa_instr_e'(cp_instruction), 1, 0, cp_rs1_addr) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         (cp_rs1_addr == 0 && cp_cs1_tag != 0));
    }

    x_atomic_cs1_reserved: cross cp_instruction, cp_cs1_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_atomic_cs1_cperms: cross cp_instruction, cp_cs1_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_atomic_cs1_otype: cross cp_instruction, cp_cs1_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_atomic_cs1_cexp: cross cp_instruction, cp_cs1_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_atomic_cs1_base: cross cp_instruction, cp_cs1_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_atomic_cs1_top: cross cp_instruction, cp_cs1_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_ATOMIC && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_atomic_cs1_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_ATOMIC ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    // SYSTEM: only actual source/destination roles contribute goals.

    x_system_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_SYSTEM && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_system_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_SYSTEM ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_system_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_SYSTEM && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      ignore_bins unused = x_system_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_SYSTEM ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_system_immediate: cross cp_instruction, cp_immediate
        iff (operand_family(instruction) == OF_SYSTEM && (!t.rvfi.trap || t.is_ex)) {
      ignore_bins unused = x_system_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_SYSTEM ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))));
    }

    // CHERI: only actual source/destination roles contribute goals.

    x_cheri_rs1: cross cp_instruction, cp_rs1_addr, cp_rs1_data
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_rs1 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         (cp_rs1_addr == 0 && cp_rs1_data != OP_ZERO));
    }

    x_cheri_rs1_size: cross cp_instruction, cp_rs1_size
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && !capability_source(instruction, mode, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_rs1_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_rs2: cross cp_instruction, cp_rs2_addr, cp_rs2_data, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_rs2 with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !integer_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         (cp_rs2_addr == 0 && cp_rs2_data != OP_ZERO) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_rs2_size: cross cp_instruction, cp_rs2_size, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && !capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_rs2_size with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !integer_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_source_addresses: cross cp_instruction, cp_rs1_addr, cp_rs2_addr, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && source_available(t, instruction, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_source_addresses with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_register_goal(isa_instr_e'(cp_instruction), 0, cp_rs1_addr) ||
         !source_register_goal(isa_instr_e'(cp_instruction), 1, cp_rs2_addr) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         (cp_rs1_addr == 0 && cp_cs1_tag != 0));
    }

    x_cheri_immediate: cross cp_instruction, cp_immediate, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (!t.rvfi.trap || t.is_ex) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_pcc_immediate: cross cp_instruction, cp_immediate
        iff (operand_family(instruction) == OF_CHERI && (!t.rvfi.trap || t.is_ex)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_pcc_immediate with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !(immediate_goal(isa_instr_e'(cp_instruction), 0, immediate_class_e'(cp_immediate)) || (kudu_top.CHERIoTEn && immediate_goal(isa_instr_e'(cp_instruction), 1, immediate_class_e'(cp_immediate)))) ||
         isa_instr_e'(cp_instruction) != ISA_AUIPCC);
    }

    x_cheri_cs1_address: cross cp_instruction, cp_rs1_addr, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_address with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !source_register(isa_instr_e'(cp_instruction), 1, 0, cp_rs1_addr) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         (cp_rs1_addr == 0 && cp_cs1_tag != 0));
    }

    x_cheri_cs1_cd_tag: cross cp_instruction, cp_cs1_tag, cp_cd_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_tag with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_TAG, cp_cs1_tag, cp_cd_tag) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_reserved: cross cp_instruction, cp_cs1_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cd_reserved: cross cp_instruction, cp_cs1_reserved, cp_cd_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_RESERVED, cp_cs1_reserved, cp_cd_reserved) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cperms: cross cp_instruction, cp_cs1_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cd_cperms: cross cp_instruction, cp_cs1_cperms, cp_cd_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_CPERMS, cp_cs1_cperms, cp_cd_cperms) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_otype: cross cp_instruction, cp_cs1_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cd_otype: cross cp_instruction, cp_cs1_otype, cp_cd_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_OTYPE, cp_cs1_otype, cp_cd_otype) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cexp: cross cp_instruction, cp_cs1_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cd_cexp: cross cp_instruction, cp_cs1_cexp, cp_cd_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_CEXP, cp_cs1_cexp, cp_cd_cexp) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_base: cross cp_instruction, cp_cs1_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cd_base: cross cp_instruction, cp_cs1_base, cp_cd_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_BASE, cp_cs1_base, cp_cd_base) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_top: cross cp_instruction, cp_cs1_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs1_cd_top: cross cp_instruction, cp_cs1_top, cp_cd_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 0) && capability_source(instruction, mode, 0) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs1_cd_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_TOP, cp_cs1_top, cp_cd_top) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_address: cross cp_instruction, cp_rs2_addr, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_address with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !source_register(isa_instr_e'(cp_instruction), 1, 1, cp_rs2_addr) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_tag: cross cp_instruction, cp_cs2_tag, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_tag with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_tag: cross cp_instruction, cp_cs2_tag, cp_cd_tag, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_tag with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_TAG, cp_cs2_tag, cp_cd_tag) ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 0, CF_TAG, cp_cs1_tag, cp_cd_tag) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_reserved: cross cp_instruction, cp_cs2_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_reserved: cross cp_instruction, cp_cs2_reserved, cp_cd_reserved, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_RESERVED, cp_cs2_reserved, cp_cd_reserved) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cperms: cross cp_instruction, cp_cs2_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_cperms: cross cp_instruction, cp_cs2_cperms, cp_cd_cperms, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_CPERMS, cp_cs2_cperms, cp_cd_cperms) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_otype: cross cp_instruction, cp_cs2_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_otype: cross cp_instruction, cp_cs2_otype, cp_cd_otype, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_OTYPE, cp_cs2_otype, cp_cd_otype) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cexp: cross cp_instruction, cp_cs2_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_cexp: cross cp_instruction, cp_cs2_cexp, cp_cd_cexp, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_CEXP, cp_cs2_cexp, cp_cd_cexp) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_base: cross cp_instruction, cp_cs2_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_base: cross cp_instruction, cp_cs2_base, cp_cd_base, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_BASE, cp_cs2_base, cp_cd_base) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_top: cross cp_instruction, cp_cs2_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 1) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cs2_cd_top: cross cp_instruction, cp_cs2_top, cp_cd_top, cp_cs1_tag
        iff (operand_family(instruction) == OF_CHERI && (source_available(t, instruction, 1) && capability_source(instruction, mode, 1) && destination_available(t, instruction, mode)) && source_available(t, instruction, 0) && capability_source(instruction, mode, 0)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cs2_cd_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !source_destination_goal(isa_instr_e'(cp_instruction), 1, CF_TOP, cp_cs2_top, cp_cd_top) ||
         !capability_source_goal(isa_instr_e'(cp_instruction), 0));
    }

    x_cheri_cd_no_cs1_tag: cross cp_instruction, cp_cd_tag
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_tag with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_TAG, cp_cd_tag) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_cheri_cd_no_cs1_reserved: cross cp_instruction, cp_cd_reserved
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_reserved with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_RESERVED, cp_cd_reserved) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_cheri_cd_no_cs1_cperms: cross cp_instruction, cp_cd_cperms
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_cperms with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_CPERMS, cp_cd_cperms) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_cheri_cd_no_cs1_otype: cross cp_instruction, cp_cd_otype
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_otype with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_OTYPE, cp_cd_otype) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_cheri_cd_no_cs1_cexp: cross cp_instruction, cp_cd_cexp
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_cexp with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_CEXP, cp_cd_cexp) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_cheri_cd_no_cs1_base: cross cp_instruction, cp_cd_base
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_base with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_BASE, cp_cd_base) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    x_cheri_cd_no_cs1_top: cross cp_instruction, cp_cd_top
        iff (operand_family(instruction) == OF_CHERI && (destination_available(t, instruction, mode) && !source_available(t, instruction, 0))) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins unused = x_cheri_cd_no_cs1_top with
        (operand_family(isa_instr_e'(cp_instruction)) != OF_CHERI ||
         !destination_field_goal(isa_instr_e'(cp_instruction), CF_TOP, cp_cd_top) ||
         (uses_source(isa_instr_e'(cp_instruction), 0) && isa_instr_e'(cp_instruction) != ISA_CSCRRW));
    }

    // END GENERATED FAMILY CROSSES
  endgroup

  cg_isa_operands u_cg_isa_operands = new();


  // --------------------------------------------------------------------------
  // Retire tap.
  //
  // Mirror both tracer output paths. With temporal safety enabled, final_fifo
  // supplies the post-revocation CD tag. AMOs are emitted separately.
  // --------------------------------------------------------------------------
  task automatic sample_entry(instr_trace_t t, bit saved_cheri_mode);
    isa_instr_e instruction;
    bit mode;
    if (!t.rvfi.valid) return;
    mode = kudu_top.CHERIoTEn && saved_cheri_mode;
    u_cg_isa_instr.sample(t, mode, mode);
    instruction = instruction_id(t, mode);
    // Operand and destination availability are qualified inside the group;
    // instruction/mode coverage also includes recognized issue-side traps.
    if (!t.rvfi.intr && instruction != ISA_UNKNOWN)
      u_cg_isa_operands.sample(t, instruction, mode, immediate_value(t, instruction),
                              mem_cap_t'(t.rvfi.rs1_rdata),
                              mem_cap_t'(t.rvfi.rs2_rdata),
                              mem_cap_t'(t.rvfi.rd_wdata));
  endtask

  always_ff @(posedge clk_i) begin
    if (rst_ni) begin
      if (!tracer.tsafe_en_i) begin
        for (int unsigned i = 32'(rd_ptr); i != 32'(rd_ptr_nxt); i = (i + 1) % 64) begin
          automatic instr_trace_t t = instr_trace_t'(instr_trace_fifo[i]);
          if (!t.is_amo)
            sample_entry(tracer.fill_cmt_info(t, tracer.is_cmt0[i], 1'b0),
                         trace_cheri_mode_q[i]);
        end
      end else begin
        automatic bit stopped = 0;
        automatic bit trvk_consumed = 0;
        for (int unsigned i = 32'(tracer.final_rd_ptr);
             i != 32'(tracer.final_wr_ptr); i = (i + 1) % 64) begin
          if (!stopped) begin
            automatic instr_trace_t t = tracer.final_fifo[i];
            automatic bit good_clc = t.ir_dec.cheri_op.clc && !t.rvfi.trap;
            if (good_clc && (!tracer.trvk_en || trvk_consumed)) begin
              stopped = 1;
            end else begin
              if (good_clc) begin
                t.rvfi.rd_wdata[MemW-1] &= ~tracer.trvk_clrtag;
                trvk_consumed = 1;
              end
              sample_entry(t, final_cheri_mode_q[i]);
            end
          end
        end
      end
    end
    if (rst_ni && amo_retire) begin
      sample_entry(tracer.fill_cmt_info(instr_trace_t'(amo_instr_q), 1'b1,
                                       tracer.amo_state == tracer.AMO_T_WAIT1),
                   amo_cheri_mode_q);
    end
  end

`endif  // KUDU_FCOV_OFF

endmodule
