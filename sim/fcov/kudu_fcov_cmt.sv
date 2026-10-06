// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_MA_CMT -- in-order commit, scoreboard drain, register write ports and
// commit-error handling.  Bound to rtl/committer.sv.
//
// See doc/functional_coverage_plan.md section 13.

module kudu_fcov_cmt
  import super_pkg::*;
  import kudu_fcov_pkg::*;
(
  input logic        clk_i,
  input logic        rst_ni,

  // --- scoreboard read side --------------------------------------------------
  input logic [1:0]  sbdfifo_rd_valid_i,
  input logic [1:0]  sbd_deq,
  input logic        sbd_same_pl,

  // --- pipeline result status ------------------------------------------------
  input logic [4:0]  pl_valid_st,
  input logic [4:0]  pl_err_st,
  input logic [4:0]  instr0_pl_sel,
  input logic [4:0]  instr1_pl_sel,
  input logic [1:0]  instr_avail,
  input logic [1:0]  instr_err,
  input logic [1:0]  is_alu_mult,

  // --- register write ports --------------------------------------------------
  input logic        rf_we0_o,
  input logic        rf_we1_o,
  input logic        rf_we2_o,
  input logic [4:0]  rf_waddr0_o,
  input logic [4:0]  rf_waddr1_o,
  input logic [4:0]  rf_waddr2_o,
  input logic        load_early,
  input logic        load_late,
  input logic        load_waddr_conflict,
  input logic        cmt_wrsv0,
  input logic        cmt_wrsv1,
  input logic        cmt_wrsv2,

  // --- commit error ----------------------------------------------------------
  input logic        cmt_err_q,
  input exc_info_t   cmt_err_info_q,
  input logic        cmt_flush_i,
  input pl_out_t     lspl_output_i,

  // --- pipeline release ------------------------------------------------------
  input logic        alupl0_rdy_o,
  input logic        alupl1_rdy_o,
  input logic        lspl_rdy_o,
  input logic        multpl_rdy_o
);

`ifndef KUDU_FCOV_OFF

  // pl_valid_st / pl_err_st have bit 0 tied to 1'b0 (committer.sv:72-73); the
  // pipeline encoding in these two status vectors is {mult, ls, alu1, alu0, 0}.
  // The scoreboard's pl field is different: it is the raw pl_sel from issue, so
  // its bit 0 (the branch unit) is set for jumps.  See cp_cmt_pl0.

  logic [1:0] we_pair, err_slot_q;
  logic [2:0] effective_wrsv;
  wire cheri_cov_en = committer.CHERIoTEn && kudu_top.cheri_pmode_i;
  logic err_cheri_mode_q;

  assign we_pair = {rf_we1_o, rf_we0_o};
  // Match committer.gen_cmt_reg_wr: stale mux outputs do not clear a
  // reservation, and x0 is explicitly excluded from cmt_regwr_o.
  assign effective_wrsv = {
    cmt_wrsv2 && rf_we2_o && (rf_waddr2_o != 0),
    cmt_wrsv1 && rf_we1_o && (rf_waddr1_o != 0),
    cmt_wrsv0 && rf_we0_o && (rf_waddr0_o != 0)
  };
  // Match the cmt_err_info_q capture enable, including while a previous error
  // is pending or cmt_flush_i is asserted. The live scoreboard and mode can
  // advance, so keep the error's observation mode alongside its slot.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_slot_q <= '0;
      err_cheri_mode_q <= 1'b0;
    end else if (|instr_err) begin
      err_slot_q <= instr_err;
      err_cheri_mode_q <= cheri_cov_en;
    end
  end

  // ==========================================================================
  // FC_MA_CMT - commit stage
  // ==========================================================================
  covergroup cg_ma_cmt @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_MA_CMT";

    // ======================================================================
    // 13.1 Commit arbitration
    // ======================================================================

    cp_sbd_rd_valid: coverpoint sbdfifo_rd_valid_i {
      bins empty = {2'b00};
      bins one   = {2'b01};
      bins two   = {2'b11};
      illegal_bins slot1_only = {2'b10};   // dual_fifo.sv:208 asserts this
    }

    cp_sbd_deq: coverpoint sbd_deq {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      illegal_bins slot1_only = {2'b10};   // sbd_deq[1] is gated on sbd_deq[0]
    }

    // Both scoreboard entries name the same pipeline, so only one of them can
    // have its result on the pipeline output bus this cycle.  This is the sole
    // reason a ready pair retires one-at-a-time (committer.sv:94, :102).
    cp_sbd_same_pl: coverpoint sbd_same_pl iff (&sbdfifo_rd_valid_i) {
      bins different = {1'b0};
      bins same      = {1'b1};
    }

    cp_instr_avail: coverpoint instr_avail {
      bins none = {2'b00};
      bins one  = {2'b01};
      bins two  = {2'b11};
      // instr1_pl_sel is masked by instr_avail[0], so 2'b10 is unreachable.
    }

    // The younger-instruction-errors-first case (2'b10) is the one that must
    // not corrupt architectural state: slot 0 has to retire normally and only
    // slot 1 is squashed.  See cp_we_vs_err below.
    cp_instr_err: coverpoint instr_err iff (|instr_avail) {
      bins none = {2'b00};
      bins ir0  = {2'b01};
      bins ir1  = {2'b10};
      bins both = {2'b11};
    }

    cp_pl_valid: coverpoint pl_valid_st {
      bins none      = {5'b00000};
      bins alu0_only = {5'b00010};
      bins alu1_only = {5'b00100};
      bins ls_only   = {5'b01000};
      bins mult_only = {5'b10000};
      bins multiple  = {[5'b00000:5'b11111]} with ($countones(item) > 1);
      illegal_bins bit0_set = {[5'b00000:5'b11111]} with (item[0] == 1'b1);
    }

    cp_pl_valid_cnt: coverpoint $countones(pl_valid_st) {
      bins n[] = {[0:4]};
    }

    cp_pl_err: coverpoint pl_err_st {
      bins none = {5'b00000};
      // alu_pipeline.sv:274 and mult_pipeline.sv:394 tie .err to 1'b0, so only
      // the LS pipeline can ever set an error bit here.  If an ALU or MULT bit
      // fills, finding F-03 has become a live bug: cmt_err_info_d is hardwired
      // to lspl_output_i (committer.sv:199-205) and would report the wrong PC
      // and cause for a non-LS error.
      bins ls = {5'b01000};
      // Listed explicitly instead of 'default' so that X samples match no bin.
      illegal_bins non_ls = {[5'b00001:5'b00111], [5'b01001:5'b11111]};
    }

    cp_release: coverpoint {multpl_rdy_o, lspl_rdy_o, alupl1_rdy_o, alupl0_rdy_o} {
      bins none = {4'b0000};
      bins alu0 = {4'b0001};
      bins alu1 = {4'b0010};
      bins ls   = {4'b0100};
      bins mult = {4'b1000};
      bins two[] = {4'b0011, 4'b0101, 4'b1001, 4'b0110, 4'b1010, 4'b1100};
    }

    // Which pipeline each retiring instruction came from.  The scoreboard entry
    // carries only {pl, pc} (super_pkg.sv:133-136), so this is the whole of the
    // commit-side instruction identity: recovering an instruction category here
    // needs a PC-keyed shadow table in the testbench (finding F-18).
    // The scoreboard carries the raw pl_sel, so the branch-unit bit rides along
    // with the execution-pipe bit for jumps (see cp_pl_sel_ir0 in
    // kudu_fcov_issue.sv).  An entry is only written when an execution pipe is
    // engaged -- ir_fifo_wr = ir_issued & |pl_sel[4:1] (issuer.sv:348-349) --
    // so 5'h00 and 5'h01 stay illegal here even though they are legal at issue.
    cp_cmt_pl0: coverpoint instr0_pl_sel iff (sbd_deq[0]) {
      bins alu0       = {5'h02};
      bins alu1       = {5'h04};
      bins ls         = {5'h08};
      bins mult       = {5'h10};
      bins jump_alu0  = {5'h03};
      bins jump_alu1  = {5'h05};
      // Issuer selects 5'h11 only for CHERI-mode JALR; the saved scoreboard
      // route is instruction provenance, unlike the current mode alone.
      bins cjalr_mult = {5'h11} iff (cheri_cov_en);
      // Listed explicitly instead of 'default' so that X samples match no bin.
      illegal_bins bad = {[5'h00:5'h01], [5'h06:5'h07], [5'h09:5'h0f],
                          [5'h12:5'h1f]};
    }

    cp_cmt_pl1: coverpoint instr1_pl_sel iff (sbd_deq[1]) {
      bins alu0       = {5'h02};
      bins alu1       = {5'h04};
      bins ls         = {5'h08};
      bins mult       = {5'h10};
      bins jump_alu0  = {5'h03};
      bins jump_alu1  = {5'h05};
      bins cjalr_mult = {5'h11} iff (cheri_cov_en);
      illegal_bins bad = {[5'h00:5'h01], [5'h06:5'h07], [5'h09:5'h0f],
                          [5'h12:5'h1f]};
    }

    // ======================================================================
    // 13.2 Register file write ports
    // ======================================================================
    // The write enables are deliberately asymmetric (committer.sv:113-114):
    // rf_we0_o ignores instr_err[1], rf_we1_o is killed by the OR of both.
    // The cell that must be correct is instr_err == 2'b10 -> we_pair == 2'b01:
    // an older instruction still commits when a younger one faults.  Anything
    // else in that cell is architectural state corruption.
    cp_we_vs_err: coverpoint we_pair iff (instr_err == 2'b10 && instr_avail[0]
                                          && is_alu_mult[0] && !cmt_err_q) {
      bins older_commits = {2'b01};
      illegal_bins younger_leaked = {2'b10, 2'b11};
    }

    cp_waddr0_cheri: coverpoint rf_waddr0_o iff (rf_we0_o && cheri_cov_en) {
      option.weight = committer.CHERIoTEn ? 1 : 0;
      bins gpr[] = {[1:15]};
    }

    cp_waddr0_rv32: coverpoint rf_waddr0_o iff (rf_we0_o && !cheri_cov_en) {
      bins gpr[] = {[1:31]};
    }

    cp_waddr1_cheri: coverpoint rf_waddr1_o iff (rf_we1_o && cheri_cov_en) {
      option.weight = committer.CHERIoTEn ? 1 : 0;
      bins gpr[] = {[1:15]};
    }

    cp_waddr1_rv32: coverpoint rf_waddr1_o iff (rf_we1_o && !cheri_cov_en) {
      bins gpr[] = {[1:31]};
    }

    // Loads use the dedicated third port, but still occupy one of the two
    // commit slots. "Early"/"late" selects slot 0/1, not a different cycle.
    cp_load_timing: coverpoint {load_late, load_early} {
      bins idle  = {2'b00};
      bins early = {2'b01};
      bins late  = {2'b10};
      illegal_bins both = {2'b11};   // one load result, one timing
    }

    // load_waddr_conflict suppresses the early write when the same destination
    // is being written by port 0 or port 1 in the same cycle.
    cp_load_waddr_conflict: coverpoint load_waddr_conflict iff (load_early) {
      bins clean    = {1'b0};
      bins conflict = {1'b1};
    }

    cp_waddr2_cheri: coverpoint rf_waddr2_o iff (rf_we2_o && cheri_cov_en) {
      option.weight = committer.CHERIoTEn ? 1 : 0;
      bins gpr[] = {[1:15]};
    }

    cp_waddr2_rv32: coverpoint rf_waddr2_o iff (rf_we2_o && !cheri_cov_en) {
      bins gpr[] = {[1:31]};
    }

    cp_waddr0_eq_waddr1: coverpoint (rf_waddr0_o == rf_waddr1_o)
        iff (rf_we0_o && rf_we1_o && rf_waddr0_o != 0) {
      bins match_ = {1'b1};
    }

    // Observe load candidates before arbitration suppresses a conflicting
    // early load's rf_we2_o; inactive mux addresses and x0 are not WAW events.
    cp_waddr1_eq_waddr2: coverpoint (rf_waddr1_o == rf_waddr2_o)
        iff (rf_we1_o && (load_early || load_late) && rf_waddr1_o != 0) {
      bins match_ = {1'b1};
    }

    cp_waddr0_eq_waddr2: coverpoint (rf_waddr0_o == rf_waddr2_o)
        iff (rf_we0_o && (load_early || load_late) && rf_waddr0_o != 0) {
      bins match_ = {1'b1};
    }

    // A port-2 write occupies one of the two slots (load_early/load_late);
    // its slot cannot also select an ALU/MULT writer. At most two writes.
    cp_wr_port_cnt: coverpoint $countones({rf_we2_o, rf_we1_o, rf_we0_o}) {
      bins n[] = {[0:2]};
    }

    cp_wrsv_clear: coverpoint effective_wrsv {
      bins none = {3'b000};
      bins p0   = {3'b001};
      bins p1   = {3'b010};
      bins p2   = {3'b100};
      bins multi[] = {3'b011, 3'b101, 3'b110};
    }

    cp_cap_writeback: coverpoint lspl_output_i.is_cap iff (rf_we2_o && cheri_cov_en) {
      option.weight = committer.CHERIoTEn ? 1 : 0;
      bins integer_ = {1'b0};
      // is_cap travels with the LS request/result; RV32 loads cannot acquire
      // capability coverage merely because pmode changes before writeback.
      bins capability = {1'b1} iff (cheri_cov_en);
    }

    // ======================================================================
    // 13.3 Commit errors
    // ======================================================================
    cp_cmt_err:   coverpoint cmt_err_q   { bins hit = {1'b1}; }
    cp_cmt_flush: coverpoint cmt_flush_i { bins hit = {1'b1}; }

    // Named against csr_pkg::exc_cause_e rather than raw numbers so that the
    // bins move if the encoding does.  Interrupt causes (mcause[5] == 1) never
    // arrive through the committer -- they are injected by the issuer -- hence
    // the illegal_bin.
    cp_err_cause: coverpoint cmt_err_info_q.mcause iff (cmt_err_q) {
      bins illegal_insn  = {csr_pkg::EXC_CAUSE_ILLEGAL_INSN};
      bins load_align    = {csr_pkg::EXC_CAUSE_LOAD_ADDR_MISALIGN};
      bins load_access   = {csr_pkg::EXC_CAUSE_LOAD_ACCESS_FAULT};
      bins store_align   = {csr_pkg::EXC_CAUSE_STORE_ADDR_MISALIGN};
      bins store_access  = {csr_pkg::EXC_CAUSE_STORE_ACCESS_FAULT};
      bins cheri_fault   = {csr_pkg::EXC_CAUSE_CHERI_FAULT}
                           iff (cheri_cov_en && err_cheri_mode_q);
      illegal_bins interrupt = {[6'd32:6'd63]};
    }

    // committer.cmt_err_info_d fixes has_pcc=1 and clrtag=0.
    cp_err_mie:     coverpoint cmt_err_info_q.mie     iff (cmt_err_q);

    // Which retire slot the faulting instruction occupied.  cmt_err_info_d
    // takes its PC from lspl_output_i unconditionally (committer.sv:199-205),
    // so slot-1 faults are the case where a wrong PC would show up first.
    cp_err_slot: coverpoint err_slot_q iff (cmt_err_q) {
      bins slot0 = {2'b01};
      bins slot1 = {2'b10};
      bins both  = {2'b11};
    }
  endgroup

  cg_ma_cmt u_cg_ma_cmt = new();

  // ==========================================================================
  // Structural assertions backing the illegal_bins above.
  // ==========================================================================
  AssertSbdRdLegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni) sbdfifo_rd_valid_i[1] |-> sbdfifo_rd_valid_i[0])
    else $error("FCOV: sbdfifo_rd_valid_i == 2'b10");

  AssertDeqInOrder: assert property (
    @(posedge clk_i) disable iff (!rst_ni) sbd_deq[1] |-> sbd_deq[0])
    else $error("FCOV: out-of-order scoreboard dequeue");

  // Backs cp_we_vs_err.  Stated as an assertion as well as an illegal_bin so
  // that a build without coverage still catches it.
  AssertOlderCommitsOnYoungerFault: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (instr_err == 2'b10) && instr_avail[0] && is_alu_mult[0] && !cmt_err_q
      |-> rf_we0_o && !rf_we1_o)
    else $error("FCOV: younger fault suppressed the older instruction's writeback");

  // Backs cp_pl_err.  See finding F-03.
  AssertOnlyLsuErrors: assert property (
    @(posedge clk_i) disable iff (!rst_ni) (pl_err_st & 5'b10111) == 5'b0)
    else $error("FCOV: non-LSU pipeline reported an error; cmt_err_info_d is hardwired to lspl_output_i (F-03)");

`endif  // KUDU_FCOV_OFF

endmodule
