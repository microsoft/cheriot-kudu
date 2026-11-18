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

  // The SVA twins of the illegal_bins above are in kudu_sva_cmt.

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// kudu_sva_cmt -- SVA properties extracted from rtl/committer.sv.
// Bound to committer as u_fcov_sva_cmt (see kudu_fcov_bind.sv, FC_MA_CMT).
// All ports are committer ports or internal signals connected through .*.
// ============================================================================
module kudu_sva_cmt
  import super_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b0
) (
  input logic        clk_i,
  input logic        rst_ni,

  input logic [1:0]  sbdfifo_rd_valid_i,
  input sbd_fifo_t   sbdfifo_rdata0_i,
  input sbd_fifo_t   sbdfifo_rdata1_i,
  input logic [1:0]  sbdfifo_rd_rdy_o,

  input logic        alupl0_valid_i,
  input pl_out_t     alupl0_output_i,
  input logic        alupl0_rdy_o,
  input logic        alupl1_valid_i,
  input pl_out_t     alupl1_output_i,
  input logic        alupl1_rdy_o,
  input logic        lspl_valid_i,
  input pl_out_t     lspl_output_i,
  input logic        lspl_rdy_o,
  input logic        multpl_valid_i,
  input pl_out_t     multpl_output_i,
  input logic        multpl_rdy_o,

  input logic        cmt_flush_i,

  input logic        rf_we0_o,
  input logic        rf_we1_o,
  input logic        rf_we2_o,
  input logic [4:0]  rf_waddr0_o,
  input logic [4:0]  rf_waddr1_o,
  input logic [4:0]  rf_waddr2_o,

  input logic [4:0]  pl_valid_st,
  input logic [4:0]  pl_err_st,
  input logic [4:0]  pl_we_st,
  input logic [4:0]  instr0_pl_sel,
  input logic [4:0]  instr1_pl_sel,
  input logic [1:0]  instr_avail,
  input logic [1:0]  instr_err,
  input logic [1:0]  is_alu_mult,
  input logic [1:0]  sbd_deq,
  input logic        cmt_err_q,
  input exc_info_t   cmt_err_info_q
);

`ifndef KUDU_FCOV_OFF

  // Legal scoreboard pl encodings written by issuer.sv:135-156 (select_pl) and
  // cmplx_unit.sv:75: one EX pipeline, plus bit 0 for a JAL/JALR. 5'h11 is
  // the CHERIoT JALR through the mult pipeline (issuer cheri_pmode = CHERIoTEn & pmode).
  function automatic logic pl_legal(logic [4:0] pl);
    return (pl == 5'h02) || (pl == 5'h04) || (pl == 5'h08) || (pl == 5'h10) ||
           (pl == 5'h03) || (pl == 5'h05) || (CHERIoTEn && (pl == 5'h11));
  endfunction

  // Instruction PC carried by the selected pipeline output (pc[31:0] is the
  // address field for both the RV32 and the reg_cap_t formats).
  function automatic logic [31:0] sel_pc(logic [4:0] sel, pl_out_t o0, pl_out_t o1,
                                         pl_out_t ols, pl_out_t omult);
    logic [31:0] r;
    r = 32'h0;
    if (sel[1]) r = r | o0.pc[31:0];
    if (sel[2]) r = r | o1.pc[31:0];
    if (sel[3]) r = r | ols.pc[31:0];
    if (sel[4]) r = r | omult.pc[31:0];
    return r;
  endfunction

  logic [4:0] pl_rdy_st;
  logic [2:0] wr_port_age;   // 0 = older (instr0), 1 = younger (instr1); one bit per port
  logic       ls_is_instr1;
  logic [31:0] cmt_pc0, cmt_pc1;

  assign pl_rdy_st    = {multpl_rdy_o, lspl_rdy_o, alupl1_rdy_o, alupl0_rdy_o, 1'b0};
  assign ls_is_instr1 = sbd_deq[1] & instr1_pl_sel[3];
  assign wr_port_age  = {ls_is_instr1, 1'b1, 1'b0};
  assign cmt_pc0      = sel_pc(instr0_pl_sel, alupl0_output_i, alupl1_output_i,
                               lspl_output_i, multpl_output_i);
  assign cmt_pc1      = sel_pc(instr1_pl_sel, alupl0_output_i, alupl1_output_i,
                               lspl_output_i, multpl_output_i);

  // committer.sv:84-89 trusts the scoreboard pl field to select exactly one EX pipeline.
  AssertSbdPlLegal0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbdfifo_rd_valid_i[0] |-> pl_legal(sbdfifo_rdata0_i.pl))
    else $error("SVA: illegal scoreboard pl at head");

  // committer.sv:88-90 same as above for the second scoreboard entry.
  AssertSbdPlLegal1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbdfifo_rd_valid_i[1] |-> pl_legal(sbdfifo_rdata1_i.pl))
    else $error("SVA: illegal scoreboard pl at head+1");

  // committer.sv:101-102 the result committed for instr0 is the instruction the scoreboard recorded (program order).
  AssertCmtPcMatch0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbd_deq[0] |-> (cmt_pc0 == sbdfifo_rdata0_i.pc))
    else $error("SVA: instr0 pipeline result does not belong to the scoreboard head");

  // committer.sv:102 the result committed for instr1 is the instruction the scoreboard recorded.
  AssertCmtPcMatch1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbd_deq[1] |-> (cmt_pc1 == sbdfifo_rdata1_i.pc))
    else $error("SVA: instr1 pipeline result does not belong to scoreboard head+1");

  // committer.sv:107-110 each dequeued scoreboard entry pops exactly one valid pipeline output (no lost/duplicate commit).
  AssertCmtPopMatchesDeq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ($countones(pl_rdy_st) == $countones(sbd_deq)) && ((pl_rdy_st & ~pl_valid_st) == 5'h0))
    else $error("SVA: pipeline pops do not match scoreboard dequeues");

  // committer.sv:113-114,174-180 a register write only happens for a dequeued entry whose pipeline asserted we.
  AssertCmtWriteNeedsRetire: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!rf_we0_o || (sbd_deq[0] && |(instr0_pl_sel & pl_we_st & 5'b10110))) &&
    (!rf_we1_o || (sbd_deq[1] && |(instr1_pl_sel & pl_we_st & 5'b10110))) &&
    (!rf_we2_o || (lspl_output_i.we && ((sbd_deq[0] && instr0_pl_sel[3]) ||
                                        (sbd_deq[1] && instr1_pl_sel[3])))))
    else $error("SVA: register write without a retiring instruction");

  // committer.sv:113-114,174-177 a faulting instr0 writes nothing and nothing younger writes in that cycle.
  AssertCmtNoWriteOnErr0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_err[0] |-> !rf_we0_o && !rf_we1_o && !rf_we2_o)
    else $error("SVA: register written in the cycle instr0 faults");

  // committer.sv:114,176-177 a faulting instr1 does not write the register file.
  AssertCmtNoWriteOnErr1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    instr_err[1] |-> !rf_we1_o && !(rf_we2_o && ls_is_instr1))
    else $error("SVA: faulting instr1 wrote the register file");

  // committer.sv:101,113-114,174-177 after a fault nothing is dequeued, popped or written until the flush.
  AssertCmtErrBlocksCommit: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt_err_q |-> (sbd_deq == 2'b00) && (pl_rdy_st == 5'h0) && !rf_we0_o && !rf_we1_o && !rf_we2_o)
    else $error("SVA: commit activity while a commit error is pending");

  // committer.sv:177-180 + regfile.sv:58-63 (priority we2 > we1 > we0): when two
  // ports write the same register, the higher-priority port carries the younger instruction.
  AssertCmtWriteOrder: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!(rf_we2_o && rf_we1_o && (rf_waddr2_o == rf_waddr1_o)) || (wr_port_age[2] >= wr_port_age[1])) &&
    (!(rf_we2_o && rf_we0_o && (rf_waddr2_o == rf_waddr0_o)) || (wr_port_age[2] >= wr_port_age[0])))
    else $error("SVA: an older write overrides a younger one to the same register");

  // committer.sv:212-216 the exception info handed to the issuer is the first
  // fault's: it must not change while the error is pending (issuer.sv:961 reads it in CMT_FLUSH).
  AssertCmtErrInfoStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt_err_q && $past(cmt_err_q) |-> (cmt_err_info_q == $past(cmt_err_info_q)))
    else $error("SVA: commit error info overwritten by a younger fault before the flush");

  // ==========================================================================
  // SVA twins of the illegal_bins in kudu_fcov_cmt, so that a build without
  // coverage still catches the violation.
  // ==========================================================================
  AssertSbdRdLegal: assert property (
    @(posedge clk_i) disable iff (!rst_ni) sbdfifo_rd_valid_i[1] |-> sbdfifo_rd_valid_i[0])
    else $error("FCOV: sbdfifo_rd_valid_i == 2'b10");

  AssertDeqInOrder: assert property (
    @(posedge clk_i) disable iff (!rst_ni) sbd_deq[1] |-> sbd_deq[0])
    else $error("FCOV: out-of-order scoreboard dequeue");

  // Backs cp_we_vs_err.
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

// ============================================================================
// FV helper lemmas: formal only, compiled only with +define+KUDU_FV_HELPERS.
//
// Auxiliary invariants that JasperGold proves and then assumes (run_fcov_clean
// in fv/fv_kudu_fcov.tcl) so that the harder assertions above become
// inductive. No covergroups; simulation never defines KUDU_FV_HELPERS. They
// are bound only in the KUDU_FV_HELPERS block at the end of kudu_fcov_bind.sv,
// which sits inside its KUDU_FCOV_OFF and CHERIoT guards. They read the fcov
// instances bound there and were proven only with CHERIoTEn=1, so the
// definitions carry the same guards: an unbound copy would become an extra
// top-level module with unresolvable kudu_top.* references.
// ============================================================================
`ifdef KUDU_FV_HELPERS
`ifdef CHERIoT
`ifndef KUDU_FCOV_OFF

// kudu_fvh_backend (was sim/fcov/fv_help_backend.sv, bound into kudu_top as
// u_fvh_backend; kudu_fvh_issue_ctrl reads its seq_cnt / lsu_e). Supports
// kudu_sva_cmt AssertCmtPcMatch0/1, the wb/rvfi wt_fifo u_ref
// AssertFifoRdData0, kudu_sva_waw_fifo AssertWawNoDropWrite and kudu_sva_top
// AssertNoOrphanPlOutput / AssertTrvkClrNoYoungerTaggedWrite.
//
// FV helper lemmas (backend area): program-order correspondence between the
// scoreboard FIFO entries and the in-flight instructions of each EX pipeline.
// For pipeline X (pl bit 1 alu0, 2 alu1, 3 ls, 4 mult) seq_pc[X][0..seq_cnt-1]
// lists the pcs of the instructions in flight in X, oldest first. The k-th
// occupied scoreboard entry with pl[X] must carry seq_pc[X][k].
module kudu_fvh_backend import super_pkg::*; (
  input logic clk_i,
  input logic rst_ni
);
  localparam int unsigned SbdDepth = 8;

  logic [3:0]  sbd_rd, sbd_cnt;
  sbd_fifo_t   sbd_e   [SbdDepth];
  logic        sbd_v   [SbdDepth];
  logic [3:0]  rank    [5][SbdDepth];
  logic [3:0]  plcnt   [5];
  logic [31:0] seq_pc  [5][SbdDepth];
  logic [3:0]  seq_cnt [5];

  assign sbd_rd  = kudu_top.sbd_fifo_i.rd_ptr_q;
  assign sbd_cnt = kudu_top.sbd_fifo_i.wr_ptr_q - kudu_top.sbd_fifo_i.rd_ptr_q;

  always_comb begin
    for (int k = 0; k < SbdDepth; k++) begin
      sbd_e[k] = sbd_fifo_t'(kudu_top.sbd_fifo_i.fifo_mem[3'(sbd_rd[2:0] + k[2:0])]);
      sbd_v[k] = (k < 32'(sbd_cnt));
    end
    for (int x = 0; x < 5; x++) begin
      plcnt[x] = 4'h0;
      for (int k = 0; k < SbdDepth; k++) begin
        rank[x][k] = plcnt[x];
        if (sbd_v[k] && sbd_e[k].pl[x]) plcnt[x] = plcnt[x] + 4'h1;
      end
    end
  end

  // ---- in-flight instruction sequences per pipeline ----
  logic        lsu_e, hold_e, dly_e;
  logic [2:0]  wb_occ;
  logic [2:0]  lsif_fsm;

  assign lsif_fsm = kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q;
  assign wb_occ   = kudu_top.ls_pipeline_i.wb_fifo_i.wr_ptr_q - kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q;
  assign lsu_e    = kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q &&
                    (kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs == IDLE);
  assign hold_e   = (lsif_fsm == 3'h1) || (lsif_fsm == 3'h3);
  assign dly_e    = ((lsif_fsm == 3'h2) || (lsif_fsm == 3'h3)) && kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid;

  always_comb begin
    logic [3:0] n;
    pl_out_t    wbe;
    for (int x = 0; x < 5; x++)
      for (int k = 0; k < SbdDepth; k++) seq_pc[x][k] = 32'h0;
    seq_cnt[0] = 4'h0;
    // alu pipelines: single wb stage
    seq_cnt[1]    = {3'h0, kudu_top.alu_pipeline0_i.wb_valid};
    seq_pc[1][0]  = kudu_top.alu_pipeline0_i.wb_reg.pc[31:0];
    seq_cnt[2]    = {3'h0, kudu_top.alu_pipeline1_i.wb_valid};
    seq_pc[2][0]  = kudu_top.alu_pipeline1_i.wb_reg.pc[31:0];
    // mult pipeline: wb (older) then ex2
    seq_cnt[4]    = {3'h0, kudu_top.mult_pipeline_i.wb_valid} + {3'h0, kudu_top.mult_pipeline_i.ex2_valid};
    seq_pc[4][0]  = kudu_top.mult_pipeline_i.wb_valid ? kudu_top.mult_pipeline_i.wb_reg.pc[31:0] :
                                                        kudu_top.mult_pipeline_i.ex2_reg.pc[31:0];
    seq_pc[4][1]  = kudu_top.mult_pipeline_i.ex2_reg.pc[31:0];
    // ls pipeline: wb_fifo entries, LSU outstanding response, lsu_if hold, lsu_if dly
    n = 4'h0;
    for (int i = 0; i < 4; i++) begin
      wbe = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[2'(kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q[1:0] + i[1:0])]);
      if (i < 32'(wb_occ)) begin
        seq_pc[3][n[2:0]] = wbe.pc[31:0];
        n = n + 4'h1;
      end
    end
    if (lsu_e) begin
      seq_pc[3][n[2:0]] = kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.pc[31:0];
      n = n + 4'h1;
    end
    if (hold_e) begin
      seq_pc[3][n[2:0]] = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.pc[31:0];
      n = n + 4'h1;
    end
    if (dly_e) begin
      seq_pc[3][n[2:0]] = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.pc[31:0];
      n = n + 4'h1;
    end
    seq_cnt[3] = n;
  end

  logic [4:0] pc_ok;
  always_comb begin
    for (int x = 0; x < 5; x++) begin
      pc_ok[x] = 1'b1;
      for (int k = 0; k < SbdDepth; k++)
        if (sbd_v[k] && sbd_e[k].pl[x] && (sbd_e[k].pc != seq_pc[x][rank[x][k]])) pc_ok[x] = 1'b0;
    end
  end

  function automatic logic pl_legal(logic [4:0] pl);
    return (pl == 5'h02) || (pl == 5'h04) || (pl == 5'h08) || (pl == 5'h10) ||
           (pl == 5'h03) || (pl == 5'h05) || (pl == 5'h11);
  endfunction

  // every occupied scoreboard entry has a legal pl encoding (one EX pipeline)
  AssertHbPlLegalAll: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!sbd_v[0] || pl_legal(sbd_e[0].pl)) && (!sbd_v[1] || pl_legal(sbd_e[1].pl)) &&
    (!sbd_v[2] || pl_legal(sbd_e[2].pl)) && (!sbd_v[3] || pl_legal(sbd_e[3].pl)) &&
    (!sbd_v[4] || pl_legal(sbd_e[4].pl)) && (!sbd_v[5] || pl_legal(sbd_e[5].pl)) &&
    (!sbd_v[6] || pl_legal(sbd_e[6].pl)) && (!sbd_v[7] || pl_legal(sbd_e[7].pl)));

  for (genvar x = 1; x < 5; x++) begin : g_pl
    // number of scoreboard entries targeting pipeline x == number of instructions in flight in x
    AssertHbCnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
      plcnt[x] == seq_cnt[x]);
    // the k-th scoreboard entry with pl[x] carries the pc of the k-th (oldest first) in-flight instruction of x
    AssertHbPcAll: assert property (@(posedge clk_i) disable iff (!rst_ni)
      pc_ok[x]);
  end

  // LSU busy (waiting for grant) implies lsu_if still holds the same request in its hold register
  AssertHbLsuBusyHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs != IDLE) |->
      hold_e && kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q &&
      (kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.pc[31:0] ==
       kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.pc[31:0]));

  // cmplx unit: the lsu request pc and the scoreboard pc are captured together
  AssertHbCmplxPc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.comlx_unit_i.pcc_rcap_q[31:0] == kudu_top.comlx_unit_i.ir_dec_q.pc);

  // ==== Trvk helpers (CHERIoT load filter) ====
  // LS in-flight sequence, parallel to seq_pc[3]: is the element a CLC (tagged load writing rd), and its rd
  logic       seq_clc [SbdDepth];
  logic [4:0] seq_rd  [SbdDepth];
  logic [3:0] posr    [5][SbdDepth];   // sbd position (relative to head) of the r-th entry with pl[x]
  logic [2:0] clcq;
  logic [4:0] trR [3];
  logic [15:1] trsv;

  assign clcq   = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.clc_valid_q;
  assign trR[0] = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[0];
  assign trR[1] = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[1];
  assign trR[2] = kudu_top.ls_pipeline_i.gen_trvk.cheri_trvk_stage_i.trsv_addr_q[2];
  assign trsv   = kudu_top.issuer_i.reg_cheri_trsv_q;

  always_comb begin
    logic [3:0] n;
    pl_out_t    wbe;
    for (int k = 0; k < SbdDepth; k++) begin
      seq_clc[k] = 1'b0;
      seq_rd[k]  = 5'h0;
    end
    n = 4'h0;
    for (int i = 0; i < 4; i++) begin
      wbe = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[2'(kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q[1:0] + i[1:0])]);
      if (i < 32'(wb_occ)) begin
        seq_clc[n[2:0]] = wbe.is_cap & wbe.we;
        seq_rd[n[2:0]]  = wbe.waddr;
        n = n + 4'h1;
      end
    end
    if (lsu_e) begin
      seq_clc[n[2:0]] = kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.is_cap &
                        kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.rf_we;
      seq_rd[n[2:0]]  = kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.rd;
      n = n + 4'h1;
    end
    if (hold_e) begin
      seq_clc[n[2:0]] = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.is_cap & kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.rf_we;
      seq_rd[n[2:0]]  = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.rd;
      n = n + 4'h1;
    end
    if (dly_e) begin
      seq_clc[n[2:0]] = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.is_cap & kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.rf_we;
      seq_rd[n[2:0]]  = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.rd;
      n = n + 4'h1;
    end
    for (int x = 0; x < 5; x++)
      for (int r = 0; r < SbdDepth; r++) posr[x][r] = 4'hf;
    for (int x = 0; x < 5; x++)
      for (int k = 0; k < SbdDepth; k++)
        if (sbd_v[k] && sbd_e[k].pl[x]) posr[x][rank[x][k][2:0]] = 4'(k);
  end

  function automatic logic stage_has(logic [2:0] q, logic [4:0] r0, logic [4:0] r1, logic [4:0] r2, logic [4:0] R);
    return (q[0] && (r0 == R)) || (q[1] && (r1 == R)) || (q[2] && (r2 == R));
  endfunction

  // the LS in-flight CLC on R is younger than the instruction at sbd position p (or does not exist)
  logic [5:0] ls_clc_younger_ok;  // per writer: alu0, alu1, mult wb, mult ex2
  logic [5:0] wr_v;
  logic [4:0] wr_rd [6];
  logic [3:0] wr_pos [6];
  always_comb begin
    wr_v[0]   = kudu_top.alu_pipeline0_i.wb_valid && kudu_top.alu_pipeline0_i.wb_reg.rf_we &&
                kudu_top.alu_pipeline0_i.wb_reg.is_cheri;
    wr_rd[0]  = kudu_top.alu_pipeline0_i.wb_reg.rd;
    wr_pos[0] = posr[1][0];
    wr_v[1]   = kudu_top.alu_pipeline1_i.wb_valid && kudu_top.alu_pipeline1_i.wb_reg.rf_we &&
                kudu_top.alu_pipeline1_i.wb_reg.is_cheri;
    wr_rd[1]  = kudu_top.alu_pipeline1_i.wb_reg.rd;
    wr_pos[1] = posr[2][0];
    wr_v[2]   = kudu_top.mult_pipeline_i.wb_valid && kudu_top.mult_pipeline_i.wb_reg.rf_we &&
                (kudu_top.mult_pipeline_i.wb_reg.flags.is_cjalr || (|kudu_top.mult_pipeline_i.wb_reg.cheri_op));
    wr_rd[2]  = kudu_top.mult_pipeline_i.wb_reg.rd;
    wr_pos[2] = posr[4][0];
    wr_v[3]   = kudu_top.mult_pipeline_i.ex2_valid && kudu_top.mult_pipeline_i.ex2_reg.rf_we &&
                (kudu_top.mult_pipeline_i.ex2_reg.flags.is_cjalr || (|kudu_top.mult_pipeline_i.ex2_reg.cheri_op));
    wr_rd[3]  = kudu_top.mult_pipeline_i.ex2_reg.rd;
    wr_pos[3] = kudu_top.mult_pipeline_i.wb_valid ? posr[4][1] : posr[4][0];
    wr_v[5:4] = 2'b00;
    wr_rd[4] = 5'h0; wr_rd[5] = 5'h0; wr_pos[4] = 4'h0; wr_pos[5] = 4'h0;
    for (int w = 0; w < 6; w++) begin
      ls_clc_younger_ok[w] = 1'b1;
      for (int j = 0; j < SbdDepth; j++)
        if (wr_v[w] && (wr_rd[w] != 5'h0) && (j < 32'(seq_cnt[3])) && seq_clc[j] && (seq_rd[j] == wr_rd[w]) &&
            !(wr_pos[w] < posr[3][j[2:0]]))
          ls_clc_younger_ok[w] = 1'b0;
    end
  end

  logic ls_clc_ok;
  always_comb begin
    ls_clc_ok = 1'b1;
    for (int j = 0; j < SbdDepth; j++) begin
      if ((j < 32'(seq_cnt[3])) && seq_clc[j] && (seq_rd[j] != 5'h0)) begin
        if (seq_rd[j][4] || !trsv[seq_rd[j][3:0]] || stage_has(clcq, trR[0], trR[1], trR[2], seq_rd[j]))
          ls_clc_ok = 1'b0;
        for (int j2 = 0; j2 < SbdDepth; j2++)
          if ((j2 != j) && (j2 < 32'(seq_cnt[3])) && seq_clc[j2] && (seq_rd[j2] == seq_rd[j])) ls_clc_ok = 1'b0;
      end
    end
  end

  // issuer waits for the trvk stage to drain after a commit flush (trsv already cleared, nothing issues)
  logic drain, stage_trsv_ok, drain_ok;
  assign drain = kudu_top.issuer_i.ctrl_fsm_cs[CSM_WAIT_TRVK];
  assign stage_trsv_ok = drain || (
    (!(clcq[0] && (trR[0] != 0)) || (!trR[0][4] && trsv[trR[0][3:0]])) &&
    (!(clcq[1] && (trR[1] != 0)) || (!trR[1][4] && trsv[trR[1][3:0]])) &&
    (!(clcq[2] && (trR[2] != 0)) || (!trR[2][4] && trsv[trR[2][3:0]])));
  assign drain_ok = !drain || ((wr_v[3:0] == 4'h0) && (seq_cnt[3] == 4'h0));

  // while draining the trvk stage after a flush, no tag-capable ALU/mult writer and no LS instruction is in flight
  AssertHtDrainEmpty: assert property (@(posedge clk_i) disable iff (!rst_ni)
    drain_ok);

  // a CLC in the trvk stage keeps its register reserved in the issuer (rd < 16), except while draining after a flush
  AssertHtStageTrsv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    stage_trsv_ok);

  // at most one CLC per destination register in the trvk stage
  AssertHtStageUniq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(clcq[0] && clcq[1] && (trR[0] != 0) && (trR[0] == trR[1])) &&
    !(clcq[0] && clcq[2] && (trR[0] != 0) && (trR[0] == trR[2])) &&
    !(clcq[1] && clcq[2] && (trR[1] != 0) && (trR[1] == trR[2])));

  // every CLC in flight in the LS pipeline has its rd reserved, is the only CLC on that rd, and none is in the trvk stage
  AssertHtLsClc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ls_clc_ok);

  // an ALU/mult instruction that can write a tagged value to R is older than any in-flight LS CLC on R
  AssertHtWrOlder: assert property (@(posedge clk_i) disable iff (!rst_ni)
    &ls_clc_younger_ok);

  // no ALU/mult instruction that can write a tagged value to R is in flight while a CLC on R is in the trvk stage
  AssertHtWrNoStage: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(wr_v[0] && (wr_rd[0] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[0])) &&
    !(wr_v[1] && (wr_rd[1] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[1])) &&
    !(wr_v[2] && (wr_rd[2] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[2])) &&
    !(wr_v[3] && (wr_rd[3] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[3])));

  // conjunction of the five trvk helpers above (mutually inductive)
  AssertHtAll: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ls_clc_ok && (&ls_clc_younger_ok) &&
    stage_trsv_ok && drain_ok &&
    !(clcq[0] && clcq[1] && (trR[0] != 0) && (trR[0] == trR[1])) &&
    !(clcq[0] && clcq[2] && (trR[0] != 0) && (trR[0] == trR[2])) &&
    !(clcq[1] && clcq[2] && (trR[1] != 0) && (trR[1] == trR[2])) &&
    !(wr_v[0] && (wr_rd[0] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[0])) &&
    !(wr_v[1] && (wr_rd[1] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[1])) &&
    !(wr_v[2] && (wr_rd[2] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[2])) &&
    !(wr_v[3] && (wr_rd[3] != 0) && stage_has(clcq, trR[0], trR[1], trR[2], wr_rd[3])));

endmodule

`endif  // KUDU_FCOV_OFF
`endif  // CHERIoT
`endif  // KUDU_FV_HELPERS
