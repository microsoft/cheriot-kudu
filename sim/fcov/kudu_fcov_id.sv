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
      bins rs2  = {2'b10};
      bins both = {2'b11};
    }
    cp_rf_ren1: coverpoint dec_out1.rf_ren iff (ir_valid_o[1]) {
      bins none = {2'b00};
      bins rs1  = {2'b01};
      bins rs2  = {2'b10};
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

    cp_is_cheri0: coverpoint ira_dec_o.is_cheri iff (cheri_active && ir_valid_o[0]) {
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

    // Prediction flags are physical decoder slots; invalid slots must not count.
    cp_cjalr_predict_ok: coverpoint (cjalr_predict_ok & s0_rd_valid)
        iff (CjalrPredictEn && cheri_active && (|s0_rd_valid)) {
      option.weight = CjalrPredictEn ? 1 : 0;
      bins none = {2'b00};
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both = {2'b11};
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
    logic hdrm_ge4, hdrm_ge2, hdrm_ok, base_ok, allow_all, cheri_perm_vio;

    // Buffered inputs are age ordered. With stage 1 bypassed the decoders
    // instead see physical mema/memb, so validity must follow that mapping.
    assign decode_valid = StageBypass[1] && !ira_is0_o ?
                          s0_rd_valid[1-i] : s0_rd_valid[i];
    assign sample_checks = decode_valid && cheri_active && !debug_mode_i &&
                           !(StageBypass[1] ? ir_flush_i : flush_s0);
    if (i == 0) begin : gen_tap0
      assign hdrm_ge4 = ir_stage.ir0_decoder_i.hdrm_ge4;
      assign hdrm_ge2 = ir_stage.ir0_decoder_i.hdrm_ge2;
      assign hdrm_ok = ir_stage.ir0_decoder_i.hdrm_ok;
      assign base_ok = ir_stage.ir0_decoder_i.base_ok;
      assign allow_all = ir_stage.ir0_decoder_i.allow_all;
      assign cheri_perm_vio = ir_stage.ir0_decoder_i.cheri_perm_vio;
    end else begin : gen_tap1
      assign hdrm_ge4 = ir_stage.ir1_decoder_i.hdrm_ge4;
      assign hdrm_ge2 = ir_stage.ir1_decoder_i.hdrm_ge2;
      assign hdrm_ok = ir_stage.ir1_decoder_i.hdrm_ok;
      assign base_ok = ir_stage.ir1_decoder_i.base_ok;
      assign allow_all = ir_stage.ir1_decoder_i.allow_all;
      assign cheri_perm_vio = ir_stage.ir1_decoder_i.cheri_perm_vio;
    end

    covergroup cg_ir_decoder @(posedge clk_i iff (rst_ni && sample_checks));
      option.per_instance = 1;
      option.name = {"FC_MA_ID.", DecoderName};
      option.weight = CHERIoTEn ? 1 : 0;
      cp_hdrm_ge4: coverpoint hdrm_ge4 { bins zero = {0}; bins one = {1}; }
      cp_hdrm_ge2: coverpoint hdrm_ge2 { bins zero = {0}; bins one = {1}; }
      cp_hdrm_ok: coverpoint hdrm_ok { bins zero = {0}; bins one = {1}; }
      cp_base_ok: coverpoint base_ok { bins zero = {0}; bins one = {1}; }
      cp_allow_all: coverpoint allow_all { bins zero = {0}; bins one = {1}; }
      cp_cheri_perm_vio: coverpoint cheri_perm_vio { bins zero = {0}; bins one = {1}; }
    endgroup
    cg_ir_decoder u_cg_ir_decoder = new();
  end

  // ==========================================================================
  // Structural assertions backing the illegal_bins above.
  // ==========================================================================
  AssertErr0Encoding: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    ir_valid_o[0] |-> (err0 inside {[ERR_NONE:ERR_MULTIPLE]}))
    else $error("FCOV: reserved error-category encoding in cp_err0");

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
