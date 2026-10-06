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
  logic amo_cheri_mode_q;

  // instr_trace_t has no mode field. Keep a sideband at the tracer's enqueue
  // boundary, using its pointers/enables rather than reconstructing retirement.
  // Saved decode below still determines aliases expanded before this boundary.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      trace_cheri_mode_q <= '0;
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
    end
  end

  // These bits were saved with the instruction, not sampled from live pmode
  // at retirement. In RV32 mode the decoder marks CHERI-only opcodes illegal;
  // the compressed expander and AUIPC decode select the mode aliases earlier.
  function automatic bit has_legal_cheri_op(ir_dec_t d);
    return (|d.cheri_op) && !d.errs.illegal_insn && !d.errs.illegal_c_insn;
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

    cp_rv32i_u_type: coverpoint t.rvfi.insn {
      wildcard bins lui    = {32'b?????????????????????????0110111};
      wildcard bins auipc  = {32'b?????????????????????????0010111}
                             iff (!t.ir_dec.cheri_op.auipcc);
    }
    cp_rv32i_uj_type: coverpoint t.rvfi.insn {
      wildcard bins jal    = {32'b?????????????????????????1101111};
    }
    cp_rv32i_sb_type: coverpoint t.rvfi.insn {
      wildcard bins beq    = {32'b?????????????????000?????1100011};
      wildcard bins bne    = {32'b?????????????????001?????1100011};
      wildcard bins blt    = {32'b?????????????????100?????1100011};
      wildcard bins bge    = {32'b?????????????????101?????1100011};
      wildcard bins bltu   = {32'b?????????????????110?????1100011};
      wildcard bins bgeu   = {32'b?????????????????111?????1100011};
    }
    cp_rv32i_s_type: coverpoint t.rvfi.insn {
      wildcard bins sb     = {32'b?????????????????000?????0100011};
      wildcard bins sh     = {32'b?????????????????001?????0100011};
      wildcard bins sw     = {32'b?????????????????010?????0100011};
    }
    cp_rv32i_i_type: coverpoint t.rvfi.insn {
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
    cp_rv32i_r_type: coverpoint t.rvfi.insn {
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
    cp_rv32i_csr: coverpoint t.rvfi.insn {
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
    cp_rv32m_r_type: coverpoint t.rvfi.insn {
      wildcard bins mul    = {32'b0000001??????????000?????0110011};
      wildcard bins mulh   = {32'b0000001??????????001?????0110011};
      wildcard bins mulhsu = {32'b0000001??????????010?????0110011};
      wildcard bins mulhu  = {32'b0000001??????????011?????0110011};
      wildcard bins div    = {32'b0000001??????????100?????0110011};
      wildcard bins divu   = {32'b0000001??????????101?????0110011};
      wildcard bins rem    = {32'b0000001??????????110?????0110011};
      wildcard bins remu   = {32'b0000001??????????111?????0110011};
    }

    cp_rv32a_r_type: coverpoint t.rvfi.insn {
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
    cp_rv32b_r_type: coverpoint t.rvfi.insn {
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
    cp_rv32b_i_type: coverpoint t.rvfi.insn {
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
    cp_rv32c_ciw_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      bins c_addi4spn = {[16'h0000:16'h1fff]}
        with (item[1:0] == 2'b00 && item[12:5] != 0)
        iff (!t.ir_dec.cheri_op.cincaddrimm);
    }
    cp_rv32c_cl_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_lw       = {16'b010???????????00};
    }
    cp_rv32c_cs_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_sw       = {16'b110???????????00};
    }
    cp_rv32c_ci_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
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
    cp_rv32c_cb_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      bins c_srli = {[16'h8000:16'h83ff]}
        with (item[1:0] == 2'b01 && item[6:2] != 0);
      bins c_srai = {[16'h8400:16'h87ff]}
        with (item[1:0] == 2'b01 && item[6:2] != 0);
      wildcard bins c_andi     = {16'b100?10????????01};
      wildcard bins c_beqz     = {16'b110???????????01};
      wildcard bins c_bnez     = {16'b111???????????01};
    }
    cp_rv32c_ca_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_sub      = {16'b100011???00???01};
      wildcard bins c_xor      = {16'b100011???01???01};
      wildcard bins c_or       = {16'b100011???10???01};
      wildcard bins c_and      = {16'b100011???11???01};
    }
    cp_rv32c_cj_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_jal      = {16'b001???????????01};
      wildcard bins c_j        = {16'b101???????????01};
    }
    cp_rv32c_cr_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
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
    cp_rv32c_css_type: coverpoint t.rvfi.insn[15:0] iff (t.rvfi.insn[1:0] != 2'b11) {
      wildcard bins c_swsp     = {16'b110???????????10};
    }

    // ======================================================================
    // 6.4 CHERIoT-1.0 instructions
    //
    // Match retired encodings, using saved decode metadata only to qualify
    // CHERI legality / mode aliases. The sample's mode requires both CHERI
    // active now and saved enqueue provenance; current pmode alone must not
    // reinterpret an older RV32 entry as CHERI.
    // ======================================================================
    cp_cscrrw: coverpoint t.rvfi.insn iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins hit = {32'b0000001??????????000?????1011011};
    }
    cp_cheriot_r_type: coverpoint t.rvfi.insn iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
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
    cp_cheriot_i_type: coverpoint t.rvfi.insn iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins csetboundsimm = {32'b?????????????????010?????1011011};
      wildcard bins cincaddrimm   = {32'b?????????????????001?????1011011};
      wildcard bins clc           = {32'b?????????????????011?????0000011};
    }
    cp_cheriot_s_type: coverpoint t.rvfi.insn iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins csc = {32'b?????????????????011?????0100011};
    }
    cp_cheriot_u_type: coverpoint t.rvfi.insn iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins auipcc = {32'b?????????????????????????0010111};
      wildcard bins auicgp = {32'b?????????????????????????1111011};
    }
    cp_cheriot_ciw_type: coverpoint t.rvfi.insn[15:0]
                         iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                              (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      bins c_incaddr4cspn = {[16'h0000:16'h1fff]}
        with (item[1:0] == 2'b00 && item[12:5] != 0);
    }
    cp_cheriot_ci_type: coverpoint t.rvfi.insn[15:0]
                        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                             (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      bins c_incaddr16csp = {[16'h6000:16'h7fff]}
        with (item[1:0] == 2'b01 && item[11:7] == 2 && {item[12], item[6:2]} != 0);
      bins c_clcsp = {[16'h6000:16'h7fff]}
        with (item[1:0] == 2'b10 && item[11:7] != 0);
    }
    cp_cheriot_cl_type: coverpoint t.rvfi.insn[15:0]
                        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                             (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins c_clc = {16'b011???????????00};
    }
    cp_cheriot_cs_type: coverpoint t.rvfi.insn[15:0]
                        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                             (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins c_csc = {16'b111???????????00};
    }
    cp_cheriot_css_type: coverpoint t.rvfi.insn[15:0]
                         iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
                              (t.rvfi.insn[1:0] != 2'b11)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      wildcard bins c_cscsp = {16'b111???????????10};
    }

    // Cross every instruction encoding with its saved operating mode.
    // Ignore impossible aliases statically; iff alone does not remove goals.
    x_rv32i_u_type_pmode: cross cp_rv32i_u_type, cp_cheri_active {
      ignore_bins cheri_alias = binsof(cp_rv32i_u_type.auipc) &&
                                binsof(cp_cheri_active) intersect {1};
    }
    x_rv32i_uj_type_pmode: cross cp_rv32i_uj_type, cp_cheri_active;
    x_rv32i_sb_type_pmode: cross cp_rv32i_sb_type, cp_cheri_active;
    x_rv32i_s_type_pmode: cross cp_rv32i_s_type, cp_cheri_active;
    x_rv32i_i_type_pmode: cross cp_rv32i_i_type, cp_cheri_active;
    x_rv32i_r_type_pmode: cross cp_rv32i_r_type, cp_cheri_active;
    x_rv32i_csr_pmode: cross cp_rv32i_csr, cp_cheri_active;
    x_rv32m_r_type_pmode: cross cp_rv32m_r_type, cp_cheri_active;
    x_rv32a_r_type_pmode: cross cp_rv32a_r_type, cp_cheri_active;
    x_rv32b_r_type_pmode: cross cp_rv32b_r_type, cp_cheri_active;
    x_rv32b_i_type_pmode: cross cp_rv32b_i_type, cp_cheri_active;

    x_rv32c_ciw_type_pmode: cross cp_rv32c_ciw_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11) {
      ignore_bins cheri_alias = binsof(cp_cheri_active) intersect {1};
    }
    x_rv32c_cl_type_pmode: cross cp_rv32c_cl_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);
    x_rv32c_cs_type_pmode: cross cp_rv32c_cs_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);
    x_rv32c_ci_type_pmode: cross cp_rv32c_ci_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11) {
      ignore_bins cheri_alias = binsof(cp_rv32c_ci_type.c_addi16sp) &&
                                binsof(cp_cheri_active) intersect {1};
    }
    x_rv32c_cb_type_pmode: cross cp_rv32c_cb_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);
    x_rv32c_ca_type_pmode: cross cp_rv32c_ca_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);
    x_rv32c_cj_type_pmode: cross cp_rv32c_cj_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);
    x_rv32c_cr_type_pmode: cross cp_rv32c_cr_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);
    x_rv32c_css_type_pmode: cross cp_rv32c_css_type, cp_cheri_active
        iff (t.rvfi.insn[1:0] != 2'b11);

    x_cscrrw_pmode: cross cp_cscrrw, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_r_type_pmode: cross cp_cheriot_r_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_i_type_pmode: cross cp_cheriot_i_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_s_type_pmode: cross cp_cheriot_s_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_u_type_pmode: cross cp_cheriot_u_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec)) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_ciw_type_pmode: cross cp_cheriot_ciw_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_ci_type_pmode: cross cp_cheriot_ci_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_cl_type_pmode: cross cp_cheriot_cl_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_cs_type_pmode: cross cp_cheriot_cs_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
             t.rvfi.insn[1:0] != 2'b11) {
      option.weight = kudu_top.CHERIoTEn ? 1 : 0;
      ignore_bins rv32_mode = binsof(cp_cheri_active) intersect {0};
    }
    x_cheriot_css_type_pmode: cross cp_cheriot_css_type, cp_cheri_active
        iff (cheri_mode && has_legal_cheri_op(t.ir_dec) &&
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
    cp_rs1: coverpoint t.rvfi.rs1_addr {
      bins x0     = {5'd0};
      bins reg_[] = {[1:31]};
    }
    cp_rs2: coverpoint t.rvfi.rs2_addr {
      bins x0     = {5'd0};
      bins reg_[] = {[1:31]};
    }

    // Value classes on the architectural operands: zero, all-ones, the sign
    // boundary and the two extremes are where ALU corner cases live.
    cp_rs1_class: coverpoint fcov_vclass(t.rvfi.rs1_rdata[31:0]);
    cp_rs2_class: coverpoint fcov_vclass(t.rvfi.rs2_rdata[31:0]);
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

  // --------------------------------------------------------------------------
  // Retire tap.
  //
  // This mirrors tracer.sv:456-469: the instructions retiring this cycle are
  // instr_trace_fifo[rd_ptr .. rd_ptr_nxt), excluding AMOs which the tracer
  // emits separately.  A commit error resets both pointers, so the retire set
  // is naturally empty in that cycle.
  // --------------------------------------------------------------------------
  task automatic sample_entry(instr_trace_t t, bit saved_cheri_mode);
    u_cg_isa_instr.sample(t, cheri_cov_en && saved_cheri_mode, saved_cheri_mode);
  endtask

  always_ff @(posedge clk_i) begin
    if (rst_ni && !(|cmt_instr_err)) begin
      for (int unsigned i = 32'(rd_ptr); i != 32'(rd_ptr_nxt); i = (i + 1) % 64) begin
        automatic instr_trace_t t = instr_trace_t'(instr_trace_fifo[i]);
        if (!t.is_amo) sample_entry(t, trace_cheri_mode_q[i]);
      end
    end
    if (rst_ni && amo_retire) begin
      sample_entry(instr_trace_t'(amo_instr_q), amo_cheri_mode_q);
    end
  end

`endif  // KUDU_FCOV_OFF

endmodule
