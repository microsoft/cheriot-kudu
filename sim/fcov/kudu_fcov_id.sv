// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_ID -- instruction register stage: FIFO handshakes, compressed decode,
// full decode, register read, revocation and breakpoint matching.
// Bound to rtl/ir_stage.sv.
//
// See doc/functional_coverage_plan.md section 9.

module kudu_fcov_id
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter bit [1:0] StageBypass = 2'b00,
  parameter bit       CHERIoTEn  = 1'b0,
  parameter bit       PredictRA  = 1'b0
) (
  input logic       clk_i,
  input logic       rst_ni,

  // --- upstream / downstream handshakes -------------------------------------
  input logic [1:0] us_valid_i,
  input logic [1:0] ir_rdy_o,
  input logic [1:0] ir_valid_o,
  input logic [1:0] ds_rdy_i,
  input logic [1:0] s0_rd_valid,
  input logic [1:0] s0_rd_rdy,
  input logic [1:0] s1_wr_valid,
  input logic [1:0] s1_wr_rdy,

  // --- flush / hold ----------------------------------------------------------
  input logic       ir_flush_i,
  input logic       ir_flush_s0_i,
  input logic       flush_s0,
  input logic       ir_hold_i,
  input logic       ira_is0_o,

  // --- decode ----------------------------------------------------------------
  input ir_reg_t    cdec_out0,
  input ir_reg_t    cdec_out1,
  input ir_dec_t    dec_out0,
  input ir_dec_t    dec_out1,
  input ir_dec_t    ira_dec_o,
  input ir_dec_t    irb_dec_o,

  // --- register file write ports (snooped for the reservation logic) --------
  input logic [4:0] rf_waddr0_i,
  input logic [4:0] rf_waddr1_i,
  input logic [4:0] rf_waddr2_i,
  input logic       rf_we0_i,
  input logic       rf_we1_i,
  input logic       rf_we2_i,

  // --- revocation and breakpoints -------------------------------------------
  input logic       trvk_en_i,
  input logic       trvk_clrtag_i,
  input logic [4:0] trvk_addr_i,
  input logic [1:0] brkpt_match,
  input logic       debug_mode_i,
  input logic       cheri_pmode_i,
  input logic       cjalr_pcc_set_o
);

`ifndef KUDU_FCOV_OFF

  kudu_instr_cat_e cat0, cat1;
  fcov_err_kind_e  err0, err1;
  logic cheri_active;
  assign cheri_active = CHERIoTEn && cheri_pmode_i;

  // Categories are derived from the decoder output, not re-decoded from the
  // instruction word, so a decoder bug shows up as a category mismatch rather
  // than being masked by an independent decode in the coverage model.
  assign cat0 = fcov_instr_cat(ira_dec_o);
  assign cat1 = fcov_instr_cat(irb_dec_o);
  assign err0 = fcov_err_kind(ira_dec_o.errs);
  assign err1 = fcov_err_kind(irb_dec_o.errs);

  // KUDU-006: encodings next to the Zbb single-operand instructions that the
  // ratified spec leaves reserved. Each one must decode as illegal.
  typedef enum logic [2:0] {
    NM_NONE, NM_GREV_R, NM_GORC_R, NM_ZEXTH_RS2, NM_REV8_IMM, NM_ORCB_IMM, NM_UNARY_IMM
  } fcov_b_near_miss_e;

  function automatic fcov_b_near_miss_e fcov_b_near_miss(logic [31:0] insn);
    logic [6:0] opcode, funct7;
    logic [2:0] funct3;
    logic [4:0] rs2;
    opcode = insn[6:0];
    funct3 = insn[14:12];
    funct7 = insn[31:25];
    rs2    = insn[24:20];
    if (opcode == 7'h33 && funct3 == 3'd5 && funct7 == 7'h34) return NM_GREV_R;
    if (opcode == 7'h33 && funct3 == 3'd5 && funct7 == 7'h14) return NM_GORC_R;
    if (opcode == 7'h33 && funct3 == 3'd4 && funct7 == 7'h04 && rs2 != 5'd0) return NM_ZEXTH_RS2;
    if (opcode == 7'h13 && funct3 == 3'd5 && funct7 == 7'h34 && rs2 != 5'd24) return NM_REV8_IMM;
    if (opcode == 7'h13 && funct3 == 3'd5 && funct7 == 7'h14 && rs2 != 5'd7) return NM_ORCB_IMM;
    if (opcode == 7'h13 && funct3 == 3'd1 && funct7 == 7'h30 &&
        !(rs2 inside {5'd0, 5'd1, 5'd2, 5'd4, 5'd5})) return NM_UNARY_IMM;
    return NM_NONE;
  endfunction

  // ira/irb are physical slots; ir_valid_o[0] qualifies whichever one is ir0.
  ir_dec_t           nm_dec0;
  fcov_b_near_miss_e b_near_miss0;
  assign nm_dec0 = ira_is0_o ? ira_dec_o : irb_dec_o;
  assign b_near_miss0 = nm_dec0.is_comp ? NM_NONE : fcov_b_near_miss(nm_dec0.insn);

  localparam bit CjalrPredictEn = PredictRA && CHERIoTEn && !StageBypass[1];
  logic [1:0] cjalr_predict_ok;
  if (CjalrPredictEn) begin : gen_cjalr_prediction
    assign cjalr_predict_ok = ir_stage.gen_stage1.cjalr_predict_ok;
  end else begin : gen_no_cjalr_prediction
    assign cjalr_predict_ok = '0;
  end

  // Observe storage, not rd_valid: the dual FIFO can present unstored input
  // through its read mux. The final two-entry stage exists in either layout.
  logic [1:0] s0_stored;
  logic [1:0] s0_read_source;
  logic final_fifo_full, final_fifo_exchange;
  if (StageBypass[1]) begin : gen_fifo_direct
    assign s0_stored = ir_stage.gen_stage0_direct.s0_fifo.have2 ? 2'd3 :
                       ir_stage.gen_stage0_direct.s0_fifo.have1 ? 2'd1 : 2'd0;
    assign s0_read_source = 2'd0;
    assign final_fifo_full = ir_stage.gen_stage0_direct.s0_fifo.have2;
    assign final_fifo_exchange =
        ir_stage.gen_stage0_direct.s0_fifo.wr_data_en[0] &&
        (|(s0_rd_valid & s0_rd_rdy));
  end else begin : gen_fifo_buffered
    assign s0_stored = !ir_stage.gen_stage0_buffer.s0_fifo.fill_status_q[0] ? 2'd0 :
                       !ir_stage.gen_stage0_buffer.s0_fifo.fill_status_q[1] ? 2'd1 :
                       !ir_stage.gen_stage0_buffer.s0_fifo.room_status_q[0] ? 2'd3 : 2'd2;
    // 1/2: one/two input words read from empty; 3: stored head + input tail.
    assign s0_read_source = !StageBypass[0] ? 2'd0 :
        !ir_stage.gen_stage0_buffer.s0_fifo.fill_status_q[0] ?
          ((s0_rd_valid[1] && s0_rd_rdy[1]) ? 2'd2 : 2'd1) :
        (!ir_stage.gen_stage0_buffer.s0_fifo.fill_status_q[1] &&
         s0_rd_valid[1] && s0_rd_rdy[1]) ? 2'd3 : 2'd0;
    assign final_fifo_full = ir_stage.gen_stage1.s1_fifo.have2;
    assign final_fifo_exchange = ir_stage.gen_stage1.s1_fifo.wr_data_en[0] &&
                                 (|(ir_valid_o & ds_rdy_i));
  end

  // ==========================================================================
  // FC_MA_ID - decode / instruction register stage
  // ==========================================================================
  covergroup cg_ma_id @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_ID";

    // ======================================================================
    // 9.1 Stage handshakes
    // ======================================================================

    cp_us_valid: coverpoint us_valid_i {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }
    cp_ir_rdy: coverpoint ir_rdy_o {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }
    cp_ir_valid: coverpoint ir_valid_o {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }
    cp_ds_rdy: coverpoint ds_rdy_i {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};
    }

    cp_s0_rd:  coverpoint s0_rd_valid  { bins v[] = {2'b00, 2'b01, 2'b11}; }
    cp_s0_rdy: coverpoint s0_rd_rdy    { bins v[] = {2'b00, 2'b01, 2'b11}; }
    // These taps are undriven when ir_stage.gen_no_stage1 is selected.
    cp_s1_wr: coverpoint s1_wr_valid iff (!StageBypass[1]) {
      option.weight = StageBypass[1] ? 0 : 1;
      bins v[] = {2'b00, 2'b01, 2'b11};
    }
    cp_s1_rdy: coverpoint s1_wr_rdy iff (!StageBypass[1]) {
      option.weight = StageBypass[1] ? 0 : 1;
      bins v[] = {2'b00, 2'b01, 2'b11};
    }

    cp_s0_stored: coverpoint s0_stored {
      bins level[] = {[0:3]}
        with (item != 2 || (!StageBypass[1] && ir_stage.S0FifoDepth > 2));
    }
    cp_s0_read_source: coverpoint s0_read_source
        iff (s0_rd_valid[0] && s0_rd_rdy[0] &&
             !(StageBypass[1] ? ir_flush_i : flush_s0)) {
      bins source[] = {[0:3]} with (item == 0 || StageBypass == 2'b01);
    }
    cp_final_fifo_full_exchange: coverpoint final_fifo_exchange
        iff (final_fifo_full && !ir_flush_i) {
      bins no_replacement = {0};
      bins read_and_replace = {1};
    }

    // Upstream has instructions, the stage cannot take them.
    cp_us_backpressure: coverpoint (us_valid_i[0] & ~ir_rdy_o[0]) {
      bins stalled = {1'b1};
    }
    // The stage has instructions, downstream cannot take them.
    cp_ds_backpressure: coverpoint (ir_valid_o[0] & ~ds_rdy_i[0]) {
      bins stalled = {1'b1};
    }
    // Only one of two available instructions accepted downstream: the pair is
    // split across cycles and the second one has to be re-presented as slot 0.
    cp_partial_accept: coverpoint (&ir_valid_o & (ds_rdy_i == 2'b01)) {
      bins split = {1'b1};
    }

    cp_flush:      coverpoint {ir_flush_s0_i, ir_flush_i} {
      bins none     = {2'b00};
      bins full     = {2'b01};
      bins stage0   = {2'b10};
      bins both     = {2'b11};
    }
    cp_flush_s0:   coverpoint flush_s0 { bins hit = {1'b1}; }
    cp_hold:       coverpoint ir_hold_i { bins hit = {1'b1}; }

    // The dual FIFO alternates which physical memory holds the older
    // instruction; both polarities must be seen or half the read mux is dead.
    cp_ira_is0:      coverpoint ira_is0_o;

    // ======================================================================
    // 9.2 Decode
    // ======================================================================
    // Categories at the decode output.  This is microarchitectural coverage of
    // the decoder, not ISA coverage: FC_ISA_INSTR covers the architectural side
    // at retire.  Both are needed -- an instruction can decode correctly here
    // and still never retire.
    cp_cat0: coverpoint cat0
        iff (ir_valid_o[0] && (cheri_active || !fcov_is_cheri_category(cat0)));
    cp_cat1: coverpoint cat1
        iff (ir_valid_o[1] && (cheri_active || !fcov_is_cheri_category(cat1)));

    // These are 3-bit categories, not the raw 5-bit ir_errs_t masks.
    // Simultaneous RTL errors map to ERR_MULTIPLE; only encoding 7 is reserved.
    // Pack the enum as bits so VCS can bin an encoding outside its named values.
    cp_err0: coverpoint {err0} iff (ir_valid_o[0]) {
      bins none = {ERR_NONE};
      bins permission = {ERR_PERM_VIO} iff (cheri_active);
      bins bounds = {ERR_BOUND_VIO} iff (cheri_active);
      bins illegal_instruction = {ERR_ILLEGAL_INSN};
      bins illegal_compressed = {ERR_ILLEGAL_C_INSN};
      bins fetch = {ERR_FETCH};
      bins multiple = {ERR_MULTIPLE};
      illegal_bins reserved = {3'b111};
    }
    // Sampled only when the decoder flags the encoding illegal, so each bin is
    // a reserved encoding that was rejected. AssertBNearMissIllegal checks it.
    cp_b_near_miss0: coverpoint b_near_miss0
        iff (ir_valid_o[0] && nm_dec0.errs.illegal_insn) {
      bins grev_r     = {NM_GREV_R};
      bins gorc_r     = {NM_GORC_R};
      bins zexth_rs2  = {NM_ZEXTH_RS2};
      bins rev8_imm   = {NM_REV8_IMM};
      bins orcb_imm   = {NM_ORCB_IMM};
      bins unary_imm  = {NM_UNARY_IMM};
    }
    cp_err1: coverpoint {err1} iff (ir_valid_o[1]) {
      bins none = {ERR_NONE};
      bins permission = {ERR_PERM_VIO} iff (cheri_active);
      bins bounds = {ERR_BOUND_VIO} iff (cheri_active);
      bins illegal_instruction = {ERR_ILLEGAL_INSN};
      bins illegal_compressed = {ERR_ILLEGAL_C_INSN};
      bins fetch = {ERR_FETCH};
      bins multiple = {ERR_MULTIPLE};
      illegal_bins reserved = {3'b111};
    }

    cp_pl_type0: coverpoint ira_dec_o.pl_type iff (ir_valid_o[0]) {
      bins local_ = {PL_LOCAL};
      bins alu    = {PL_ALU};
      bins ls     = {PL_LS};
      bins mult   = {PL_MULT};
      bins jal    = {PL_JAL};
      bins jalr   = {PL_JALR};
    }
    cp_pl_type1: coverpoint irb_dec_o.pl_type iff (ir_valid_o[1]) {
      bins local_ = {PL_LOCAL};
      bins alu    = {PL_ALU};
      bins ls     = {PL_LS};
      bins mult   = {PL_MULT};
      bins jal    = {PL_JAL};
      bins jalr   = {PL_JALR};
    }

    cp_is_comp0: coverpoint ira_dec_o.is_comp iff (ir_valid_o[0]);
    cp_is_comp1: coverpoint irb_dec_o.is_comp iff (ir_valid_o[1]);

    // The compressed decoder runs ahead of the main decoder; an illegal 16-bit
    // encoding has to survive into the decode output as illegal_c_insn.
    cp_illegal_c0: coverpoint cdec_out0.errs.illegal_c_insn { bins hit = {1'b1}; }
    cp_illegal_c1: coverpoint cdec_out1.errs.illegal_c_insn { bins hit = {1'b1}; }

    cp_rf_ren0: coverpoint dec_out0.rf_ren iff (ir_valid_o[0]) {
      bins none = {2'b00};
      bins rs1  = {2'b01};
      illegal_bins rs2 = {2'b10};
      bins both = {2'b11};
    }
    cp_rf_ren1: coverpoint dec_out1.rf_ren iff (ir_valid_o[1]) {
      bins none = {2'b00};
      bins rs1  = {2'b01};
      illegal_bins rs2 = {2'b10};
      bins both = {2'b11};
    }

    cp_rs1_0: coverpoint ira_dec_o.rs1 iff (ir_valid_o[0] && ira_dec_o.rf_ren[0]) {
      bins reg_[] = {[5'd0:5'd31]};
    }
    cp_rs2_0: coverpoint ira_dec_o.rs2 iff (ir_valid_o[0] && ira_dec_o.rf_ren[1]) {
      bins reg_[] = {[5'd0:5'd31]};
    }
    cp_rs1_1: coverpoint irb_dec_o.rs1 iff (ir_valid_o[1] && irb_dec_o.rf_ren[0]) {
      bins reg_[] = {[5'd0:5'd31]};
    }
    cp_rs2_1: coverpoint irb_dec_o.rs2 iff (ir_valid_o[1] && irb_dec_o.rf_ren[1]) {
      bins reg_[] = {[5'd0:5'd31]};
    }

    cp_cjalr_rs1_0: coverpoint (ira_dec_o.rs1 == 5'd1)
        iff (CHERIoTEn && cheri_pmode_i && ir_valid_o[0] &&
             ira_dec_o.is_jalr && ira_dec_o.rf_ren[0]) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins ra = {1'b1};
      bins other = {1'b0};
    }
    cp_cjalr_rs1_1: coverpoint (irb_dec_o.rs1 == 5'd1)
        iff (CHERIoTEn && cheri_pmode_i && ir_valid_o[1] &&
             irb_dec_o.is_jalr && irb_dec_o.rf_ren[0]) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins ra = {1'b1};
      bins other = {1'b0};
    }

    cp_rf_waddr0: coverpoint rf_waddr0_i iff (rf_we0_i) {
      bins reg_[] = {[5'd0:5'd31]};
    }
    cp_rf_waddr1: coverpoint rf_waddr1_i iff (rf_we1_i) {
      bins reg_[] = {[5'd0:5'd31]};
    }
    cp_rf_waddr2: coverpoint rf_waddr2_i iff (rf_we2_i) {
      bins reg_[] = {[5'd0:5'd31]};
    }

    x_cp_rs1_0_w0: cross cp_rs1_0, cp_rf_waddr0;
    x_cp_rs2_0_w0: cross cp_rs2_0, cp_rf_waddr0;
    x_cp_rs1_0_w1: cross cp_rs1_0, cp_rf_waddr1;
    x_cp_rs2_0_w1: cross cp_rs2_0, cp_rf_waddr1;
    x_cp_rs1_0_w2: cross cp_rs1_0, cp_rf_waddr2;
    x_cp_rs2_0_w2: cross cp_rs2_0, cp_rf_waddr2;

    x_cp_rs1_1_w0: cross cp_rs1_1, cp_rf_waddr0;
    x_cp_rs2_1_w0: cross cp_rs2_1, cp_rf_waddr0;
    x_cp_rs1_1_w1: cross cp_rs1_1, cp_rf_waddr1;
    x_cp_rs2_1_w1: cross cp_rs2_1, cp_rf_waddr1;
    x_cp_rs1_1_w2: cross cp_rs1_1, cp_rf_waddr2;
    x_cp_rs2_1_w2: cross cp_rs2_1, cp_rf_waddr2;


    // sysctl.valid is the OR of seven decode terms and csrw is one of them, so
    // it has to be sampled here too: a CSR write to mstatus/mie raises valid
    // with all six of the other bits clear, which is not an illegal encoding.
    // The terms come from mutually exclusive opcodes -- fence.i is MISC_MEM
    // funct3==1, ecall/ebreak/mret/dret/wfi are SYSTEM funct3==0 decoded by a
    // unique case on instr[31:20], and csrw is SYSTEM funct3!=0 -- so exactly
    // one bit is set whenever valid is high (see rtl/ir_decoder.sv:127-137).
    cp_sysctl0: coverpoint {ira_dec_o.sysctl.csrw,   ira_dec_o.sysctl.fencei,
                            ira_dec_o.sysctl.ebrk,   ira_dec_o.sysctl.ecall,
                            ira_dec_o.sysctl.wfi,    ira_dec_o.sysctl.dret,
                            ira_dec_o.sysctl.mret}
                iff (ir_valid_o[0] & ira_dec_o.sysctl.valid) {
      bins mret   = {7'b0000001};
      bins dret   = {7'b0000010};
      bins wfi    = {7'b0000100};
      bins ecall  = {7'b0001000};
      bins ebreak = {7'b0010000};
      bins fencei = {7'b0100000};
      bins csrw   = {7'b1000000};
      illegal_bins multiple = {[7'd0:7'd127]} with ($countones(item) != 1);
    }

    cp_is_cheri0: coverpoint ira_dec_o.rs_cheri iff (cheri_active && ir_valid_o[0]) {
      option.weight = CHERIoTEn ? 1 : 0;
    }
    cp_is_cmplx0: coverpoint ira_dec_o.is_cmplx iff (ir_valid_o[0]);
    cp_is_brkpt0: coverpoint ira_dec_o.is_brkpt iff (ir_valid_o[0]);
    cp_is_csr0:   coverpoint ira_dec_o.is_csr   iff (ir_valid_o[0]);

    // The alt (shadow-fetch) tag travels with the instruction through decode.
    cp_alt_valid0: coverpoint ira_dec_o.alt_valid iff (ir_valid_o[0]);
    cp_alt_id0:    coverpoint ira_dec_o.alt_id iff (ir_valid_o[0] & ira_dec_o.alt_valid) {
      bins id[] = {[0:1]};
    }

    cp_ptaken0: coverpoint ira_dec_o.ptaken iff (ir_valid_o[0]);
    cp_ptaken1: coverpoint irb_dec_o.ptaken iff (ir_valid_o[1]);

    // ======================================================================
    // 9.3 Revocation, breakpoints and CHERI serialisation
    // ======================================================================
    cp_trvk_en: coverpoint trvk_en_i iff (cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins hit = {1'b1};
    }
    // A revocation that actually clears a tag, versus one that finds the
    // capability still valid.  Only the first has an architectural effect.
    cp_trvk_clrtag: coverpoint trvk_clrtag_i iff (cheri_active && trvk_en_i) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins kept    = {1'b0};
      bins cleared = {1'b1};
    }
    cp_trvk_addr: coverpoint trvk_addr_i iff (cheri_active && trvk_en_i) {
      option.weight = CHERIoTEn ? 1 : 0;
      bins reg_[] = {[1:15]};
      bins x0     = {5'd0};
    }

    x_cp_trvk_rs1_0: cross cp_rs1_0, cp_trvk_addr iff (cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      ignore_bins rs1_above_15 = binsof(cp_rs1_0) intersect {[5'd16:5'd31]};
    }
    x_cp_trvk_rs2_0: cross cp_rs2_0, cp_trvk_addr iff (cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      ignore_bins rs2_above_15 = binsof(cp_rs2_0) intersect {[5'd16:5'd31]};
    }

    x_cp_trvk_rs1_1: cross cp_rs1_1, cp_trvk_addr iff (cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      ignore_bins rs1_above_15 = binsof(cp_rs1_1) intersect {[5'd16:5'd31]};
    }
    x_cp_trvk_rs2_1: cross cp_rs2_1, cp_trvk_addr iff (cheri_active) {
      option.weight = CHERIoTEn ? 1 : 0;
      ignore_bins rs2_above_15 = binsof(cp_rs2_1) intersect {[5'd16:5'd31]};
    }

    cp_brkpt_match: coverpoint brkpt_match {
      bins none  = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }

    // Every CHERI enforcement path in the core is disabled in debug mode
    // (finding F-08), so debug mode has to be covered on both sides of the
    // check or the disable itself is never exercised.
    cp_debug_mode:   coverpoint debug_mode_i;
    cp_cheri_pmode: coverpoint cheri_pmode_i iff (CHERIoTEn) {
      option.weight = CHERIoTEn ? 1 : 0;
    }

    // Prediction flags are physical decoder slots; only slots written into
    // stage 1 count. Two predicted CJALRs can be decoded together, but
    // s1_wr_valid blocks slot 1 behind a slot-0 CJALR (ir_stage.sv).
    cp_cjalr_predict_ok: coverpoint (cjalr_predict_ok & s1_wr_valid)
        iff (CjalrPredictEn && cheri_active && (|s0_rd_valid)) {
      option.weight = CjalrPredictEn ? 1 : 0;
      bins none = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      illegal_bins both = {2'b11};
    }

    // Only gen_stage1 drives this output, and prediction needs CHERI + RA.
    cp_cjalr_pcc_set: coverpoint cjalr_pcc_set_o
        iff (CjalrPredictEn && cheri_active) {
      option.weight = CjalrPredictEn ? 1 : 0;
      bins no_update = {1'b0};
      bins hit = {1'b1};
    }

    cp_rf_we: coverpoint {rf_we2_i, rf_we1_i, rf_we0_i} {
      bins none = {3'b000};
      bins p0   = {3'b001};
      bins p1   = {3'b010};
      bins p2   = {3'b100};
      bins multi = default;
    }
  endgroup

  cg_ma_id u_cg_ma_id = new();

  for (genvar i = 0; i < 2; i++) begin : gen_decoder
    localparam string DecoderName = i == 0 ? "ir0_decoder" : "ir1_decoder";
    logic decode_valid, sample_checks;
    logic hdrm_ge4, hdrm_ge2, hdrm_ok, base_ok, allow_all;
    logic cheri_perm_vio, cheri_bound_vio;
    logic fetch_err, ferr2w, is_comp;

    // Buffered inputs are age ordered. With stage 1 bypassed the decoders
    // instead see physical mema/memb, so validity must follow that mapping.
    assign decode_valid = StageBypass[1] && !ira_is0_o ?
                          s0_rd_valid[1-i] : s0_rd_valid[i];
    assign sample_checks = decode_valid && cheri_active &&
                           !(StageBypass[1] ? ir_flush_i : flush_s0);
    if (i == 0) begin : gen_tap0
      assign hdrm_ge4 = ir_stage.ir0_decoder_i.hdrm_ge4;
      assign hdrm_ge2 = ir_stage.ir0_decoder_i.hdrm_ge2;
      assign hdrm_ok = ir_stage.ir0_decoder_i.hdrm_ok;
      assign base_ok = ir_stage.ir0_decoder_i.base_ok;
      assign allow_all = ir_stage.ir0_decoder_i.allow_all;
      assign cheri_perm_vio = ir_stage.ir0_decoder_i.cheri_perm_vio;
      assign cheri_bound_vio = ir_stage.ir0_decoder_i.cheri_bound_vio;
      assign fetch_err = ir_stage.ir0_decoder_i.ir_reg_i.errs.fetch_err;
      assign ferr2w = ir_stage.ir0_decoder_i.ir_reg_i.ferr2w;
      assign is_comp = ir_stage.ir0_decoder_i.ir_reg_i.is_comp;
    end else begin : gen_tap1
      assign hdrm_ge4 = ir_stage.ir1_decoder_i.hdrm_ge4;
      assign hdrm_ge2 = ir_stage.ir1_decoder_i.hdrm_ge2;
      assign hdrm_ok = ir_stage.ir1_decoder_i.hdrm_ok;
      assign base_ok = ir_stage.ir1_decoder_i.base_ok;
      assign allow_all = ir_stage.ir1_decoder_i.allow_all;
      assign cheri_perm_vio = ir_stage.ir1_decoder_i.cheri_perm_vio;
      assign cheri_bound_vio = ir_stage.ir1_decoder_i.cheri_bound_vio;
      assign fetch_err = ir_stage.ir1_decoder_i.ir_reg_i.errs.fetch_err;
      assign ferr2w = ir_stage.ir1_decoder_i.ir_reg_i.ferr2w;
      assign is_comp = ir_stage.ir1_decoder_i.ir_reg_i.is_comp;
    end

    covergroup cg_ir_decoder @(posedge clk_i iff (rst_ni && sample_checks));
      option.per_instance = 1;
      option.name = {"FC_MA_ID.", DecoderName};
      option.weight = CHERIoTEn ? 1 : 0;
      cp_hdrm_ge4: coverpoint hdrm_ge4 iff (!debug_mode_i) { bins zero = {0}; bins one = {1}; }
      cp_hdrm_ge2: coverpoint hdrm_ge2 iff (!debug_mode_i) { bins zero = {0}; bins one = {1}; }
      cp_hdrm_ok: coverpoint hdrm_ok iff (!debug_mode_i) { bins zero = {0}; bins one = {1}; }
      cp_base_ok: coverpoint base_ok iff (!debug_mode_i) { bins zero = {0}; bins one = {1}; }
      cp_allow_all: coverpoint allow_all iff (!debug_mode_i) { bins zero = {0}; bins one = {1}; }
      cp_cheri_perm_vio: coverpoint cheri_perm_vio { bins zero = {0}; bins one = {1}; }
      cp_cheri_bound_vio: coverpoint cheri_bound_vio { bins zero = {0}; bins one = {1}; }
      cp_debug_mode: coverpoint debug_mode_i { bins normal = {0}; bins debug = {1}; }

      x_perm_vio_debug: cross cp_cheri_perm_vio, cp_debug_mode {
        ignore_bins suppressed_in_debug = binsof(cp_cheri_perm_vio.one) &&
                                          binsof(cp_debug_mode.debug);
      }
      x_bound_vio_debug: cross cp_cheri_bound_vio, cp_debug_mode {
        ignore_bins suppressed_in_debug = binsof(cp_cheri_bound_vio.one) &&
                                          binsof(cp_debug_mode.debug);
      }

      // KUDU-070: a fetch bus error near the PCC top. The 2- or 4-byte headroom
      // check is chosen by is_comp, which comes from the errored data. Goal:
      // headroom 2-3 bytes x error on the first word x each decoded length.
      cp_hdrm_win: coverpoint {hdrm_ge4, hdrm_ge2} iff (!debug_mode_i && fetch_err) {
        bins b2_3 = {2'b01};
        bins ge4  = {2'b11};
      }
      cp_ferr_word: coverpoint ferr2w iff (!debug_mode_i && fetch_err) {
        bins first  = {1'b0};
        bins second = {1'b1};
      }
      cp_ferr_is_comp: coverpoint is_comp iff (!debug_mode_i && fetch_err) {
        bins c32 = {1'b0};
        bins c16 = {1'b1};
      }
      x_hdrm_fetch_err: cross cp_hdrm_win, cp_ferr_word, cp_ferr_is_comp
          iff (!debug_mode_i && fetch_err) {
        // Only a 32-bit instruction straddles two fetch words.
        ignore_bins c16_no_second = binsof(cp_ferr_word.second) && binsof(cp_ferr_is_comp.c16);
      }
    endgroup
    cg_ir_decoder u_cg_ir_decoder = new();

    AssertDebugSuppressesCheriErrors: assert property (
      @(posedge clk_i) disable iff (!rst_ni)
      (sample_checks && debug_mode_i) |-> !(cheri_perm_vio || cheri_bound_vio))
      else $error("FCOV: decoder %0d reports a CHERI error in debug mode", i);
  end

  // ==========================================================================
  // Structural assertions backing the illegal_bins above.
  // ==========================================================================
  AssertCjalrPredictOneHot: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (CjalrPredictEn && cheri_active && (|s0_rd_valid)) |->
      $onehot0(cjalr_predict_ok & s1_wr_valid))
    else $error("FCOV: both slots written to IR stage 1 predict CJALR");

  AssertBNearMissIllegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (ir_valid_o[0] && b_near_miss0 != NM_NONE) |-> nm_dec0.errs.illegal_insn)
    else $error("FCOV: reserved encoding 0x%08x decoded as legal (KUDU-006)",
                nm_dec0.insn);

  AssertErr0Encoding: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    ir_valid_o[0] |-> (err0 inside {[ERR_NONE:ERR_MULTIPLE]}))
    else $error("FCOV: reserved error-category encoding in cp_err0");

  AssertRfRen0Legal: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    ir_valid_o[0] |-> (dec_out0.rf_ren != 2'b10))
    else $error("FCOV: rs2-only read enable in cp_rf_ren0");

  AssertRfRen1Legal: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    ir_valid_o[1] |-> (dec_out1.rf_ren != 2'b10))
    else $error("FCOV: rs2-only read enable in cp_rf_ren1");

  AssertErr1Encoding: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    ir_valid_o[1] |-> (err1 inside {[ERR_NONE:ERR_MULTIPLE]}))
    else $error("FCOV: reserved error-category encoding in cp_err1");

  AssertIrValidLegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni) ir_valid_o[1] |-> ir_valid_o[0])
    else $error("FCOV: ir_valid_o == 2'b10");

  AssertUsValidLegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni) us_valid_i[1] |-> us_valid_i[0])
    else $error("FCOV: us_valid_i == 2'b10");

  AssertOneSysctl: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (ir_valid_o[0] && ira_dec_o.sysctl.valid) |->
      $onehot({ira_dec_o.sysctl.csrw,   ira_dec_o.sysctl.fencei,
               ira_dec_o.sysctl.ebrk,   ira_dec_o.sysctl.ecall,
               ira_dec_o.sysctl.wfi,    ira_dec_o.sysctl.dret,
               ira_dec_o.sysctl.mret}))
    else $error("FCOV: more than one sysctl bit decoded for one instruction");

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// kudu_sva_id -- formal-oriented SVA checkers for the IR / decode stage.
// Bound to rtl/ir_stage.sv as u_fcov_sva_id (see kudu_fcov_bind.sv, FC_MA_ID).
//
// The decoder checks compare ir_decoder against small reference decodes
// written from the RISC-V / CHERIoT encodings (not from the RTL case tree).
// Stage-1 FIFO and RA-prediction checks are generate-guarded on StageBypass /
// PredictRA, so only the hierarchy that exists in a configuration is named.
// ============================================================================
module kudu_sva_id
  import super_pkg::*;
  import cheri_pkg::*;
#(
  parameter bit [1:0] StageBypass = 2'b00,
  parameter bit       CHERIoTEn   = 1'b0,
  parameter bit       PredictRA   = 1'b0,
  parameter bit       RV32M       = 1'b1,
  parameter bit       RV32B       = 1'b1,
  parameter bit       RV32A       = 1'b1
) (
  input logic            clk_i,
  input logic            rst_ni,
  input logic            cheri_pmode,
  input logic            debug_mode_i,
  input pcc_cap_t        pcc_cap_i,

  input logic [1:0]      us_valid_i,
  input logic [1:0]      ir_rdy_o,
  input logic [1:0]      ir_valid_o,
  input logic [1:0]      ds_rdy_i,
  input logic            ira_is0_o,
  input ir_dec_t         ira_dec_o,
  input ir_dec_t         irb_dec_o,
  input logic            ir_flush_i,
  input logic            flush_s0,

  input logic [1:0]      s0_rd_valid,
  input logic [1:0]      s0_rd_rdy,
  input logic [1:0]      s1_wr_valid,
  input logic [1:0]      s1_wr_rdy,

  input ir_reg_t         cdec_out0,
  input ir_reg_t         cdec_out1,
  input ir_dec_t         dec_out0,
  input ir_dec_t         dec_out1,

  input rf_raddr2_t      ira_raddr2_q,
  input rf_raddr2_t      irb_raddr2_q,
  input rf_rdata2_t      ira_rf_rdata2_q,
  input rf_rdata2_t      irb_rf_rdata2_q,
  input logic [RegW-1:0] cur_ra
);

`ifndef KUDU_FCOV_OFF

  // --------------------------------------------------------------------------
  // Reference decode (RV32IMAC + Zba/Zbb/Zbc/Zbs + CHERIoT), from the ISA specs.
  // pm is the effective CHERIoT mode (CHERIoTEn & cheri_pmode_i).
  // --------------------------------------------------------------------------
  function automatic logic ref_base_legal(logic [31:0] i, logic pm);
    logic [6:0] op, f7;
    logic [2:0] f3;
    logic [4:0] f5, r2;
    op = i[6:0]; f3 = i[14:12]; f7 = i[31:25]; f5 = i[31:27]; r2 = i[24:20];
    case (op)
      7'h37, 7'h17, 7'h6f: return 1'b1;                     // lui, auipc, jal
      7'h67: return (f3 == 3'b000);                         // jalr
      7'h63: return (f3 != 3'b010) && (f3 != 3'b011);       // beq..bgeu
      7'h03: return (f3 == 3'b000) || (f3 == 3'b001) || (f3 == 3'b010) ||
                    (f3 == 3'b100) || (f3 == 3'b101) || (pm && (f3 == 3'b011));  // clc
      7'h23: return (f3 == 3'b000) || (f3 == 3'b001) || (f3 == 3'b010) ||
                    (pm && (f3 == 3'b011));                 // csc
      7'h2f: return RV32A && (f3 == 3'b010) &&
                    ((f5 == 5'b00000) || (f5 == 5'b00001) || (f5 == 5'b00100) ||
                     (f5 == 5'b01000) || (f5 == 5'b01100) || (f5 == 5'b10000) ||
                     (f5 == 5'b10100) || (f5 == 5'b11000) || (f5 == 5'b11100) ||
                     (f5 == 5'b00011) || ((f5 == 5'b00010) && (r2 == 5'h0)));
      7'h13: begin
        if (f3 == 3'b001)       // slli, clz/ctz/cpop/sext.b/sext.h, bseti/bclri/binvi
          return (f7 == 7'h00) ||
                 (RV32B && (((f7 == 7'h30) && ((r2 == 5'h00) || (r2 == 5'h01) ||
                                               (r2 == 5'h02) || (r2 == 5'h04) ||
                                               (r2 == 5'h05))) ||
                            (f7 == 7'h14) || (f7 == 7'h24) || (f7 == 7'h34)));
        else if (f3 == 3'b101)  // srli/srai, rori, orc.b, rev8, bexti
          return (f7 == 7'h00) || (f7 == 7'h20) ||
                 (RV32B && ((f7 == 7'h30) || (f7 == 7'h24) ||
                            ((f7 == 7'h14) && (r2 == 5'h07)) ||
                            ((f7 == 7'h34) && (r2 == 5'h18))));
        else
          return 1'b1;
      end
      7'h33: return (f7 == 7'h00) ||
                    ((f7 == 7'h20) && ((f3 == 3'b000) || (f3 == 3'b101))) ||
                    (RV32M && (f7 == 7'h01)) ||
                    (RV32B && (((f7 == 7'h10) && ((f3 == 3'b010) || (f3 == 3'b100) ||
                                                  (f3 == 3'b110))) ||        // sh*add
                               ((f7 == 7'h20) && ((f3 == 3'b100) || (f3 == 3'b110) ||
                                                  (f3 == 3'b111))) ||        // xnor/orn/andn
                               ((f7 == 7'h30) && ((f3 == 3'b001) || (f3 == 3'b101))) ||
                               ((f7 == 7'h05) && (f3 != 3'b000)) ||          // clmul*, min/max
                               ((f7 == 7'h24) && ((f3 == 3'b001) || (f3 == 3'b101))) ||
                               ((f7 == 7'h14) && (f3 == 3'b001)) ||
                               ((f7 == 7'h34) && (f3 == 3'b001)) ||
                               ((f7 == 7'h04) && (f3 == 3'b100) && (r2 == 5'h0))));  // zext.h
      7'h0f: return (f3 == 3'b000) || (f3 == 3'b001);       // fence, fence.i
      7'h73: begin
        if (f3 == 3'b000)
          return (i[19:7] == 13'h0) &&
                 ((i[31:20] == 12'h000) || (i[31:20] == 12'h001) ||
                  (i[31:20] == 12'h302) || (i[31:20] == 12'h7b2) ||
                  (i[31:20] == 12'h105));
        else
          return (f3 != 3'b100);                            // Zicsr
      end
      7'h5b: return pm &&
                    (((f3 == 3'b000) &&
                      ((f7 == 7'h01) || (f7 == 7'h08) || (f7 == 7'h09) || (f7 == 7'h0a) ||
                       (f7 == 7'h0b) || (f7 == 7'h0c) || (f7 == 7'h0d) || (f7 == 7'h10) ||
                       (f7 == 7'h11) || (f7 == 7'h14) || (f7 == 7'h16) || (f7 == 7'h20) ||
                       (f7 == 7'h21) ||
                       ((f7 == 7'h7f) &&
                        ((r2 == 5'h00) || (r2 == 5'h01) || (r2 == 5'h02) || (r2 == 5'h03) ||
                         (r2 == 5'h04) || (r2 == 5'h08) || (r2 == 5'h09) || (r2 == 5'h0a) ||
                         (r2 == 5'h0b) || (r2 == 5'h0f) || (r2 == 5'h17) || (r2 == 5'h18))))) ||
                     (f3 == 3'b001) || (f3 == 3'b010));     // cincaddrimm, csetboundsimm
      7'h7b: return pm;                                     // auicgp
      default: return 1'b0;
    endcase
  endfunction

  // Register-file usage {we, ren_b, ren_a} of an encoding (only meaningful if legal).
  function automatic logic [2:0] ref_rf_use(logic [31:0] i);
    logic [2:0] f3;
    f3 = i[14:12];
    case (i[6:0])
      7'h37, 7'h17, 7'h6f: return 3'b100;
      7'h67, 7'h03, 7'h13, 7'h7b: return 3'b101;
      7'h63, 7'h23: return 3'b011;
      7'h33: return 3'b111;
      7'h2f: return {1'b1, (i[31:27] != 5'b00010), 1'b1};          // lr has no rs2
      7'h73: return (f3 == 3'b000) ? 3'b000 : {1'b1, 1'b0, ~f3[2]};   // csr / csr*i
      7'h5b: return {1'b1, (f3 == 3'b000) && (i[31:25] != 7'h7f) && (i[31:25] != 7'h01), 1'b1};
      default: return 3'b000;
    endcase
  endfunction

  function automatic logic [4:0] ref_rs1(logic [31:0] i);
    return (i[6:0] == 7'h7b) ? 5'h3 : i[19:15];   // auicgp reads cgp (x3)
  endfunction

  // CHERIoT (RV32E register file in pmode): any used register >= x16 is illegal.
  function automatic logic ref_reg_illegal(logic [31:0] i, logic pm);
    logic [2:0] u;
    logic [4:0] r1;
    u  = ref_rf_use(i);
    r1 = ref_rs1(i);
    return pm && ((u[0] && r1[4]) || (u[1] && i[24]) || (u[2] && i[11]));
  endfunction

  function automatic logic ref_illegal(logic [31:0] i, logic pm);
    return !ref_base_legal(i, pm) || ref_reg_illegal(i, pm);
  endfunction

  function automatic pl_type_e ref_pl(logic [31:0] i);
    logic [2:0] f3;
    logic [6:0] f7;
    f3 = i[14:12]; f7 = i[31:25];
    case (i[6:0])
      7'h6f: return PL_JAL;
      7'h67: return PL_JALR;
      7'h63, 7'h0f: return PL_LOCAL;
      7'h03, 7'h23: return PL_LS;
      7'h2f: return (i[31:28] == 4'b0001) ? PL_LS : PL_LOCAL;       // lr/sc vs amo
      7'h33: return (f7 == 7'h01) ? PL_MULT : PL_ALU;
      7'h73: return (f3 == 3'b000) ? PL_LOCAL : PL_LS;
      7'h5b: begin
        if ((f3 == 3'b000) && (f7 == 7'h01)) return PL_LS;           // cspecialrw
        if ((f3 == 3'b010) ||
            ((f3 == 3'b000) && ((f7 == 7'h08) || (f7 == 7'h09) || (f7 == 7'h0a))) ||
            ((f3 == 3'b000) && (f7 == 7'h7f) && ((i[24:20] == 5'h08) || (i[24:20] == 5'h09))))
          return PL_MULT;                                            // setbounds*, crrl, cram
        return PL_ALU;
      end
      default: return PL_ALU;
    endcase
  endfunction

  function automatic sysctl_t ref_sysctl(logic [31:0] i);
    sysctl_t s;
    s        = '0;
    s.ecall  = (i == 32'h0000_0073);
    s.ebrk   = (i == 32'h0010_0073);
    s.mret   = (i == 32'h3020_0073);
    s.dret   = (i == 32'h7b20_0073);
    s.wfi    = (i == 32'h1050_0073);
    s.fencei = (i[6:0] == 7'h0f) && (i[14:12] == 3'b001);
    // csrrw/csrrwi always write; csrrs/c(i) write only with a non-zero rs1/uimm
    s.csrw   = (i[6:0] == 7'h73) && (i[14:12] != 3'b000) &&
               !(i[13] && (i[19:15] == 5'h0)) &&
               ((i[31:20] == 12'h300) || (i[31:20] == 12'h304));   // mstatus, mie
    s.valid  = s.ecall | s.ebrk | s.mret | s.dret | s.wfi | s.fencei | s.csrw;
    return s;
  endfunction

  function automatic logic [31:0] next_pc(ir_dec_t d);
    return d.ptaken ? d.ptarget[31:0] : d.pc_nxt;
  endfunction

  // --------------------------------------------------------------------------
  // Per-decoder checks (combinational, hold for any decoder input).
  // --------------------------------------------------------------------------
  ir_reg_t    dec_in  [2];
  ir_dec_t    dec_res [2];
  logic [1:0] dec_valid;

  assign dec_in[0]  = cdec_out0;
  assign dec_in[1]  = cdec_out1;
  assign dec_res[0] = dec_out0;
  assign dec_res[1] = dec_out1;

  // Decoder k holds a live instruction (stage-0 read port; Cfg2 decodes mema/memb).
  if (StageBypass[1]) begin : gen_dv_direct
    assign dec_valid[0] = ira_is0_o ? s0_rd_valid[0] : s0_rd_valid[1];
    assign dec_valid[1] = ira_is0_o ? s0_rd_valid[1] : s0_rd_valid[0];
  end else begin : gen_dv_buffer
    assign dec_valid = s0_rd_valid;
  end

  for (genvar k = 0; k < 2; k++) begin : g_dec
    logic [31:0] insn;
    logic        legal;
    logic [2:0]  use_ref;
    logic [32:0] fetch_end;
    logic        allow_all, bound_ref;

    assign insn    = dec_res[k].insn;
    // An idle decoder slot can hold an X instruction in simulation (constant 1 in FV).
    assign legal   = !$isunknown(insn) && !ref_illegal(insn, cheri_pmode);
    assign use_ref = ref_rf_use(insn);

    // rtl/ir_decoder.sv:183-501,:142: illegal_insn flags exactly the encodings that are
    // not RV32IMAC+B(+CHERIoT in pmode), plus x16..x31 operands in pmode (RV32E).
    AssertDecIllegalRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !$isunknown(insn) |-> dec_res[k].errs.illegal_insn == ref_illegal(insn, cheri_pmode));

    // rtl/ir_decoder.sv:76-86: legal instructions read/write exactly the ISA operands,
    // and unused register fields are reported as x0.
    AssertDecOperandRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      legal |-> (dec_res[k].rf_ren == use_ref[1:0]) && (dec_res[k].rf_we == use_ref[2]) &&
                (dec_res[k].rs1 == (use_ref[0] ? ref_rs1(insn) : 5'h0)) &&
                (dec_res[k].rs2 == (use_ref[1] ? insn[24:20] : 5'h0)) &&
                (dec_res[k].rd  == (use_ref[2] ? insn[11:7]  : 5'h0)));

    // rtl/ir_decoder.sv:107,:150-501: legal instructions are routed to the right pipeline,
    // only AMOs (not lr/sc) are complex, and is_csr marks Zicsr and cspecialrw.
    AssertDecPipeRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      legal |-> (dec_res[k].pl_type == ref_pl(insn)) &&
                (dec_res[k].is_cmplx == ((insn[6:0] == 7'h2f) && (insn[31:28] != 4'b0001))) &&
                (dec_res[k].is_csr == (((insn[6:0] == 7'h73) && (insn[14:12] != 3'b000)) ||
                                       ((insn[6:0] == 7'h5b) && (insn[14:12] == 3'b000) &&
                                        (insn[31:25] == 7'h01)))));

    // rtl/ir_decoder.sv:130-140: special-case (sysctl) flags of legal instructions match
    // their exact encodings (ecall/ebreak/mret/dret/wfi/fence.i/mstatus|mie write).
    AssertDecSysctlRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      legal |-> (dec_res[k].sysctl == ref_sysctl(insn)));

    // rtl/ir_decoder.sv:88-99: any_err is exactly the OR of the reported error flags
    // (IF may only supply fetch_err / illegal_c_insn).
    AssertDecAnyErrMatchesErrs: assert property (@(posedge clk_i) disable iff (!rst_ni)
      dec_res[k].any_err == (|dec_res[k].errs));

    // rtl/ir_decoder.sv:518-552: at most one CHERI operation is decoded per instruction.
    AssertDecCheriOpOneHot: assert property (@(posedge clk_i) disable iff (!rst_ni)
      $onehot0(dec_res[k].cheri_op));

    // rtl/ir_decoder.sv:252-256,:207-226,:475-494: a CHERI operation (incl. auipcc/clc/csc)
    // is decoded on a legal instruction only in CHERIoT mode, and exactly for the
    // CHERIoT opcodes.
    AssertDecCheriOpRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      legal |-> ((|dec_res[k].cheri_op) ==
                 (cheri_pmode && ((insn[6:0] == 7'h5b) || (insn[6:0] == 7'h7b) ||
                                  (insn[6:0] == 7'h17) ||
                                  (((insn[6:0] == 7'h03) || (insn[6:0] == 7'h23)) &&
                                   (insn[14:12] == 3'b011))))));

    // rtl/ir_decoder.sv:559-575: PCC bounds check of a live fetch uses the fetched length,
    // which is 2 bytes when the first fetch word errored (Sail riscv_fetch); KUDU-070.
    assign allow_all = (pcc_cap_i.base32 == 32'h0) && pcc_cap_i.top33[32];
    assign fetch_end = {1'b0, dec_in[k].pc} +
                       (((dec_in[k].errs.fetch_err && !dec_in[k].ferr2w) || dec_in[k].is_comp) ?
                        33'd2 : 33'd4);
    assign bound_ref = cheri_pmode && !debug_mode_i &&
                       ((dec_in[k].pc < pcc_cap_i.base32) ||
                        (!allow_all && (fetch_end > pcc_cap_i.top33)));
    AssertDecFetchBoundsRef: assert property (@(posedge clk_i) disable iff (!rst_ni)
      dec_valid[k] && !$isunknown(bound_ref) |->
        kudu_fcov_pkg::sva_xok(dec_res[k].errs.bound_vio == bound_ref));

    // rtl/compressed_decoder.sv:47-360: a compressed instruction not flagged illegal_c
    // expands to a legal base encoding (register range is checked separately).
    AssertCompExpandsLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (dec_valid[k] && dec_in[k].is_comp && !dec_in[k].errs.illegal_c_insn) |->
        ref_base_legal(dec_in[k].insn, cheri_pmode));
  end

  // --------------------------------------------------------------------------
  // IR output (issuer view): ir0/ir1 in program order.
  // --------------------------------------------------------------------------
  ir_dec_t ir0, ir1, ir_out[2];
  assign ir0       = ira_is0_o ? ira_dec_o : irb_dec_o;
  assign ir1       = ira_is0_o ? irb_dec_o : ira_dec_o;
  assign ir_out[0] = ir0;
  assign ir_out[1] = ir1;

  for (genvar k = 0; k < 2; k++) begin : g_out
    // rtl/compressed_decoder.sv:34-45: is_comp agrees with the original 16-bit encoding,
    // a 32-bit instruction keeps its low half in c_insn, and only compressed instructions
    // can be illegal_c.
    AssertIrCompFieldsConsistent: assert property (@(posedge clk_i) disable iff (!rst_ni)
      ir_valid_o[k] && !$isunknown(ir_out[k].c_insn) |-> kudu_fcov_pkg::sva_xok(
        (ir_out[k].is_comp == (ir_out[k].c_insn[1:0] != 2'b11)) &&
        (ir_out[k].is_comp || ((ir_out[k].insn[15:0] == ir_out[k].c_insn) &&
                               !ir_out[k].errs.illegal_c_insn)) &&
        (ir_out[k].errs.illegal_c_insn || (ir_out[k].insn[1:0] == 2'b11))));

    // rtl/branch_predict.sv:338-370, rtl/ir_decoder.sv:101-103: only control-transfer
    // instructions (or fetch-errored / illegal_c garbage) reach IR predicted taken.
    AssertIrPtakenIsCti: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (ir_valid_o[k] && ir_out[k].ptaken) |->
        (ir_out[k].is_branch || ir_out[k].is_jal || ir_out[k].is_jalr ||
         ir_out[k].errs.fetch_err || ir_out[k].errs.illegal_c_insn));
  end

  // A stage-1 CJALR whose RA prediction failed has ptaken cleared although IF already
  // redirected (rtl/ir_stage.sv:209-210), so its successor PC is not derivable.
  function automatic logic succ_unknown(ir_dec_t d);
    return CHERIoTEn && !StageBypass[1] && d.is_jalr && !d.ptaken;
  endfunction

  // Simulation only: X taint of the IR FIFOs (kudu_sva_fifo_ref x_o, constant 0 in
  // FV). An X write handshake can leave the FIFO pointers, and so the slot order,
  // inconsistent until the next flush. Also used by kudu_sva_issue.
  logic ir_fifo_x;
  if (StageBypass[1]) begin : g_ir_fifo_x_s0
    assign ir_fifo_x = gen_stage0_direct.s0_fifo.u_fcov_sva_stage_fifo.ref_x;
  end else begin : g_ir_fifo_x_s1
    assign ir_fifo_x = gen_stage1.s1_fifo.u_fcov_sva_stage_fifo.ref_x |
                       gen_stage0_buffer.s0_fifo.u_fcov_sva_dual_fifo.ref_x;
  end

  // rtl/ir_stage.sv:441-452, rtl/stage_fifo.sv: the two IR slots are consecutive in
  // program order (ir1 follows ir0's sequential or predicted-taken successor).
  AssertIrSlotOrder: assert property (@(posedge clk_i) disable iff (!rst_ni || $sampled(ir_fifo_x))
    ((ir_valid_o == 2'b11) && !$isunknown({ir0.ptaken, ir0.is_jalr}) && !succ_unknown(ir0)) |->
      kudu_fcov_pkg::sva_xok((ir1.pc == next_pc(ir0))));

  // Shadow of the last instruction handed to the issuer.
  logic        consume, consume2;
  logic        exp_valid;
  logic [31:0] exp_pc;
  ir_dec_t     last_out;

  assign consume  = ir_valid_o[0] && ds_rdy_i[0];
  assign consume2 = consume && (ir_valid_o == 2'b11) && (ds_rdy_i == 2'b11);
  assign last_out = consume2 ? ir1 : ir0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      exp_valid <= 1'b0;
      exp_pc    <= 32'h0;
    end else if (flush_s0) begin
      exp_valid <= 1'b0;
    end else if (consume) begin
      exp_valid <= !succ_unknown(last_out);
      exp_pc    <= next_pc(last_out);
    end
  end

  // rtl/ir_stage.sv:244-298,:441-470: between flushes the IR delivers a gap-free,
  // duplicate-free instruction stream (no loss or replay across cycles).
  AssertIrPcContinuity: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (ir_valid_o[0] && exp_valid) |-> (ir0.pc == exp_pc));

  // rtl/dual_fifo.sv:79, rtl/stage_fifo.sv:104-105: IR ready to IF is never 2'b10
  // (backs the fcov illegal bin on ir_rdy_o).
  AssertIrRdyLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_rdy_o[1] |-> ir_rdy_o[0]);

  // rtl/stage_fifo.sv:85-88: the issuer never takes slot 1 without slot 0.
  AssertDsRdyLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ds_rdy_i[1] |-> ds_rdy_i[0]);

  // rtl/stage_fifo.sv:141-145, rtl/dual_fifo.sv:126-129: a flush empties the IR.
  AssertFlushClearsIr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ir_flush_i |=> (ir_valid_o == 2'b00));

  // --------------------------------------------------------------------------
  // Two-stage configurations: s0 -> s1 transfer and pre-read operands.
  // --------------------------------------------------------------------------
  if (!StageBypass[1]) begin : gen_s1_chk
    logic [1:0] s0_rd_cnt, s1_wr_cnt;
    logic [RegW-1:0] rf_ira0, rf_ira1, rf_irb0, rf_irb1;
    // The tag bit (CHERIoT builds only) is compared only in pmode: the regfile's revocation
    // clear ignores pmode (rtl/regfile.sv:52) while the IR copy uses it.
    localparam logic [RegW-1:0] TagMask = (RegW > 32) ? ({{(RegW-1){1'b0}}, 1'b1} << (RegW-1))
                                                      : '0;
    logic [RegW-1:0] cmp_mask;

    assign s0_rd_cnt = ((s0_rd_valid == 2'b11) && (s0_rd_rdy == 2'b11)) ? 2'd2 :
                       (s0_rd_valid[0] && s0_rd_rdy[0]) ? 2'd1 : 2'd0;
    assign s1_wr_cnt = 2'(ir_stage.gen_stage1.s1_fifo.wr_data_en[0]) +
                       2'(ir_stage.gen_stage1.s1_fifo.wr_data_en[1]);

    // rtl/ir_stage.sv:441-452, rtl/dual_fifo.sv:96-101, rtl/stage_fifo.sv:124-133: every
    // instruction popped from stage 0 is written to stage 1 (no loss / duplication).
    AssertS0S1TransferCount: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !flush_s0 |-> (s0_rd_cnt == s1_wr_cnt));

    // rtl/ir_stage.sv:519-528: the latched operand addresses track the stage-1 entries.
    AssertIrRaddrQMatchesEntry: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (ira_raddr2_q.a0 == ira_dec_o.rs1) && (ira_raddr2_q.a1 == ira_dec_o.rs2) &&
      (irb_raddr2_q.a0 == irb_dec_o.rs1) && (irb_raddr2_q.a1 == irb_dec_o.rs2));

    assign cmp_mask = cheri_pmode ? '1 : ~TagMask;
    // Read the flops directly (x0 = 0), as in the KUDU_FORMAL_RTL read path of
    // rtl/regfile.sv:81-84: Jasper mis-evaluates a variable index into rf_reg.
    assign rf_ira0  = (ira_raddr2_q.a0 == '0) ? '0 : kudu_top.regfile_i.rf_reg_q[ira_raddr2_q.a0];
    assign rf_ira1  = (ira_raddr2_q.a1 == '0) ? '0 : kudu_top.regfile_i.rf_reg_q[ira_raddr2_q.a1];
    assign rf_irb0  = (irb_raddr2_q.a0 == '0) ? '0 : kudu_top.regfile_i.rf_reg_q[irb_raddr2_q.a0];
    assign rf_irb1  = (irb_raddr2_q.a1 == '0) ? '0 : kudu_top.regfile_i.rf_reg_q[irb_raddr2_q.a1];

    // rtl/ir_stage.sv:123-205 ("equivalent to read RF"): the pre-read operands of stage-1
    // entry A always equal the architectural register file (bypass, x0, revocation).
    AssertIraRdataMatchesRf: assert property (@(posedge clk_i) disable iff (!rst_ni)
      kudu_fcov_pkg::sva_xok((((ira_rf_rdata2_q.d0 ^ rf_ira0) & cmp_mask) == '0) &&
                             (((ira_rf_rdata2_q.d1 ^ rf_ira1) & cmp_mask) == '0)));

    // Same for stage-1 entry B.
    AssertIrbRdataMatchesRf: assert property (@(posedge clk_i) disable iff (!rst_ni)
      kudu_fcov_pkg::sva_xok((((irb_rf_rdata2_q.d0 ^ rf_irb0) & cmp_mask) == '0) &&
                             (((irb_rf_rdata2_q.d1 ^ rf_irb1) & cmp_mask) == '0)));
  end

  // --------------------------------------------------------------------------
  // Return-address prediction copy (rtl/ir_stage.sv:550-604).
  // --------------------------------------------------------------------------
  if (PredictRA && CHERIoTEn) begin : gen_ra_chk
    localparam logic [RegW-1:0] RaTagMask = (RegW > 32) ?
                                            ({{(RegW-1){1'b0}}, 1'b1} << (RegW-1)) : '0;
    logic [RegW-1:0] rf_x1;
    assign rf_x1 = kudu_top.regfile_i.rf_reg_q[1];

    // rtl/ir_stage.sv:562-575: the RA shadow (the CJALR predicted target and predicted
    // PCC, cjalr_rcap_o) equals x1 in every field. Only the tag may be stale-set: the
    // shadow ignores revocation clears of x1 (rtl/regfile.sv:52); the full-cap compare
    // in rtl/branch_unit.sv:91-93 then turns the prediction into a mispredict.
    AssertCurRaMatchesRf: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (((cur_ra ^ rf_x1) & ~RaTagMask) == '0) && ((rf_x1 & RaTagMask) == (cur_ra & rf_x1 & RaTagMask)));
  end

`endif  // KUDU_FCOV_OFF

endmodule
