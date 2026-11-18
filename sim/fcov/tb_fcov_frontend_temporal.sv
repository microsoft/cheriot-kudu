// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module fifo_stub #(parameter int unsigned FifoDepth = 4) ();
  logic fifo_ready;
  logic [FifoDepth-1:0] valid_q;
  logic clear_i, in_valid_i, pop_fifo, apply_alt, alloc_alt, pop_alt;
  logic [1:0] instr_xfr, out_is_comp, fetch_err, out_valid_o;
  logic [31:0] out_addr0, out_addr1;
  logic [1:0] instr_addr16;
  logic [3:0] addr16_incr;
  logic first_word_err, second_word_err;
  logic [2:0] alt_rd_valid;
endmodule

module prefetch_stub #(parameter int unsigned PrefetchDepth = 3,
                       parameter int unsigned FifoDepth = 4) ();
  logic fifo_ready, branch_i, valid_req_q, valid_req;
  logic [PrefetchDepth-1:0] rdata_outstanding_q;
  fifo_stub #(.FifoDepth(FifoDepth)) fifo_i();
endmodule

module if_stage
  import super_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter int unsigned BhtSize = 16,
  parameter int unsigned PrefetchDepth = 3,
  parameter bit AltEnable = 1'b1
) (
  input logic clk_i,
  input logic rst_ni
);
  localparam int unsigned FifoDepth = AltEnable ? PrefetchDepth + 4 : PrefetchDepth + 1;

  logic req_i, instr_req_o, instr_gnt_i, instr_rvalid_i, instr_err_i;
  logic if_busy_o, prefetch_busy;
  logic [1:0] if_valid_o, ds_rdy_i;
  ir_reg_t if_instr0_o, if_instr1_o;
  logic ex_pc_set_i, ex_bp_init_i, alloc_alt, alt_has_free;
  logic [31:0] ex_pc_target_i;
  ex_alt_ctrl_t ex_alt_ctrl_i;
  logic [1:0] alt_free_id;
  logic [PrefetchDepth-1:0] rdata_outstanding_q, branch_discard_q, fifo_busy;
  logic discard_req_q, fifo_clear;
  int unsigned fifo_occupancy;
  logic [1:0] alt_status;
  logic pdt_en_i;
  logic [1:0] pdt_valid_o, bp_is_branch, bp_is_jal, bp_is_jalr_ra;
  logic [1:0] pdt_branch_go, pdt_jal_go, pdt_jalr_go, pdt_pc_set;
  logic [31:0] cur_ra32_i;
  ir_reg_t pdt_instr0, pdt_instr1;
  logic [1:0] bht_rdata0, bht_rdata1;
  logic fetch_instr0_is_comp;
  ex_bp_info_t ex_bp_info_i;

  prefetch_stub #(.PrefetchDepth(PrefetchDepth), .FifoDepth(FifoDepth)) prefetch_buffer_i();

  kudu_fcov_if #(
    .BhtSize(BhtSize), .PrefetchDepth(PrefetchDepth),
    .AltEnable(AltEnable), .InstrBufEn(1'b1)
  ) u_fcov_if (
    .clk_i, .rst_ni, .req_i, .instr_req_o, .instr_gnt_i, .instr_rvalid_i,
    .instr_err_i, .if_busy_o, .prefetch_busy, .if_valid_o, .ds_rdy_i,
    .if_instr0_o, .if_instr1_o, .ex_pc_set_i, .ex_pc_target_i,
    .ex_bp_init_i, .ex_alt_ctrl_i, .alloc_alt, .alt_has_free, .alt_free_id,
    .rdata_outstanding_q, .branch_discard_q, .discard_req_q, .fifo_clear,
    .fifo_busy, .fifo_occupancy, .alt_status, .pdt_en_i, .pdt_valid_o,
    .pdt_instr0, .pdt_instr1, .bp_is_branch, .bp_is_jal, .bp_is_jalr_ra,
    .pdt_branch_go, .pdt_jal_go, .pdt_jalr_go, .cur_ra32_i, .pdt_pc_set, .bht_rdata0,
    .bht_rdata1, .fetch_instr0_is_comp, .ex_bp_info_i
  );

  task automatic clear();
    req_i = 1'b1;
    instr_req_o = 1'b0;
    instr_gnt_i = 1'b0;
    instr_rvalid_i = 1'b0;
    instr_err_i = 1'b0;
    if_busy_o = 1'b0;
    prefetch_busy = 1'b0;
    if_valid_o = 2'b00;
    ds_rdy_i = 2'b00;
    if_instr0_o = '0;
    if_instr1_o = '0;
    ex_pc_set_i = 1'b0;
    ex_pc_target_i = '0;
    ex_bp_init_i = 1'b0;
    ex_alt_ctrl_i = '0;
    alloc_alt = 1'b0;
    alt_has_free = 1'b1;
    alt_free_id = '0;
    rdata_outstanding_q = '0;
    branch_discard_q = '0;
    discard_req_q = 1'b0;
    fifo_clear = 1'b0;
    fifo_busy = '0;
    fifo_occupancy = 0;
    alt_status = '0;
    pdt_en_i = 1'b0;
    pdt_valid_o = 2'b00;
    pdt_instr0 = '0;
    pdt_instr1 = '0;
    bp_is_branch = 2'b00;
    bp_is_jal = 2'b00;
    bp_is_jalr_ra = 2'b00;
    pdt_branch_go = 2'b00;
    pdt_jal_go = 2'b00;
    pdt_jalr_go = 2'b00;
    cur_ra32_i = '0;
    pdt_pc_set = 2'b00;
    bht_rdata0 = 2'b00;
    bht_rdata1 = 2'b00;
    fetch_instr0_is_comp = 1'b0;
    ex_bp_info_i = '0;
    prefetch_buffer_i.fifo_ready = 1'b1;
    prefetch_buffer_i.branch_i = 1'b0;
    prefetch_buffer_i.valid_req_q = 1'b0;
    prefetch_buffer_i.valid_req = 1'b0;
    prefetch_buffer_i.rdata_outstanding_q = '0;
    prefetch_buffer_i.fifo_i.valid_q = '0;
    prefetch_buffer_i.fifo_i.clear_i = 1'b0;
    prefetch_buffer_i.fifo_i.in_valid_i = 1'b0;
    prefetch_buffer_i.fifo_i.pop_fifo = 1'b0;
    prefetch_buffer_i.fifo_i.apply_alt = 1'b0;
    prefetch_buffer_i.fifo_i.alloc_alt = 1'b0;
    prefetch_buffer_i.fifo_i.pop_alt = 1'b0;
    prefetch_buffer_i.fifo_i.instr_xfr = 2'b00;
    prefetch_buffer_i.fifo_i.out_is_comp = 2'b00;
    prefetch_buffer_i.fifo_i.fetch_err = 2'b00;
    prefetch_buffer_i.fifo_i.out_valid_o = 2'b00;
    prefetch_buffer_i.fifo_i.out_addr0 = '0;
    prefetch_buffer_i.fifo_i.out_addr1 = '0;
    prefetch_buffer_i.fifo_i.instr_addr16 = '0;
    prefetch_buffer_i.fifo_i.addr16_incr = '0;
    prefetch_buffer_i.fifo_i.first_word_err = 1'b0;
    prefetch_buffer_i.fifo_i.second_word_err = 1'b0;
    prefetch_buffer_i.fifo_i.alt_rd_valid = '0;
  endtask
endmodule

module issuer
  import super_pkg::*;
  import cheri_pkg::*;
  import csr_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter bit CHERIoTEn = 1'b1,
  parameter bit LoadFiltEn = 1'b1
) (
  input logic clk_i,
  input logic rst_ni,
  input logic cheri_pmode_i
);
  logic ira_is0_i;
  logic [1:0] ir_valid_i, ir_any_err, ir_hazard, ir_raw_hazard, ir_waw_hazard, ir_cheri_hazard;
  logic ir0_issued, ir1_issued, ir1_ooo_rdy_event;
  logic [4:0] ir0_pl_sel, ir1_pl_sel, ex_valid_o, ir0_raw_cause, ir1_raw_cause;
  logic [1:0] sbdfifo_wr_rdy_i, mispredict, branch_mispredict_event;
  logic wr_req_conflict, ir1_raw_by_ir0_event, ir0_stall_nohaz_event, ir1_stall_nohaz_event;
  logic [31:1] reg_wrsv_q;
  logic [15:1] reg_cheri_trsv_q;
  logic [31:0] ir0_pl_fwd_act, ir1_pl_fwd_act;
  logic [31:0] alupl0_fwd_act_i, alupl1_fwd_act_i, lspl_fwd_act_i, multpl_fwd_act_i;
  logic alupl0_fwd_act_i_any, alupl1_fwd_act_i_any, lspl_fwd_act_i_any, multpl_fwd_act_i_any;
  logic [15:0] ctrl_fsm_cs, ctrl_fsm_ns;
  special_case_e special_case_q;
  logic handle_err, handle_sysctl, handle_cmplx, handle_irq, handle_debug, cmt_flush_o, cmt_err_i;
  ir_dec_t ir0_dec, ir1_dec;
  logic [1:0] ir_sysctl, ir_cmplx;
  exc_info_t csr_exc_info_o;
  logic csr_save_cause_o, debug_csr_save_o, irq_pending_i, csr_mstatus_mie_i;
  logic [14:0] irq_fast;
  logic debug_req_i, debug_mode_q, debug_single_step_i, single_step_trap_q;
  dbg_cause_e debug_cause_o;
  logic intr_event, ir0_trap_event, cheri_pmode, ir_flush_o, pc_set_o;
  priv_lvl_e priv_mode_i;
  logic csr_mstatus_tw_i, ebreak_enter_debug, ir0_mode_err;
  full_data2_t ira_full_data2_fwd_o, irb_full_data2_fwd_o;
  branch_info_t branch_info_i;
  ex_alt_ctrl_t ex_alt_ctrl_o;

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;

  kudu_fcov_issue u_fcov_issue (
    .clk_i, .rst_ni, .ira_is0_i, .ir_valid_i, .ir_any_err, .ir_hazard,
    .ir0_issued, .ir1_issued, .ir0_pl_sel, .ir1_pl_sel, .ex_valid_o,
    .ir1_ooo_rdy_event, .sbdfifo_wr_rdy_i, .mispredict, .branch_mispredict_event,
    .ir_raw_hazard, .ir_waw_hazard, .ir_cheri_hazard, .wr_req_conflict,
    .ir0_raw_cause, .ir1_raw_cause, .ir1_raw_by_ir0_event,
    .ir0_stall_nohaz_event, .ir1_stall_nohaz_event, .reg_wrsv_q,
    .reg_cheri_trsv_q, .ir0_pl_fwd_act, .ir1_pl_fwd_act,
    .alupl0_fwd_act_i_any, .alupl1_fwd_act_i_any, .lspl_fwd_act_i_any,
    .multpl_fwd_act_i_any, .ctrl_fsm_cs, .ctrl_fsm_ns, .special_case_q,
    .handle_err, .handle_sysctl, .handle_cmplx, .handle_irq, .handle_debug,
    .cmt_flush_o, .cmt_err_i, .ir0_dec, .ir1_dec, .ir_sysctl, .ir_cmplx,
    .cheri_pmode_i, .csr_exc_info_o, .csr_save_cause_o, .debug_csr_save_o,
    .irq_pending_i, .csr_mstatus_mie_i, .irq_fast, .debug_req_i,
    .debug_mode_q, .debug_single_step_i, .single_step_trap_q, .debug_cause_o,
    .intr_event, .ir0_trap_event, .priv_mode_i, .csr_mstatus_tw_i,
    .ebreak_enter_debug, .ir0_mode_err
  );

  function automatic ir_dec_t mk_dec(input logic [4:0] rs1, rs2, rd,
                                     input logic [1:0] ren,
                                     input logic we);
    ir_dec_t d;
    d = '0;
    d.insn[6:0] = OPCODE_OP_IMM;
    d.rs1 = rs1;
    d.rs2 = rs2;
    d.rd = rd;
    d.rf_ren = ren;
    d.rf_we = we;
    d.pl_type = PL_ALU;
    return d;
  endfunction

  task automatic clear();
    ira_is0_i = 1'b1;
    ir_valid_i = 2'b00;
    ir_any_err = 2'b00;
    ir_hazard = 2'b00;
    ir_raw_hazard = 2'b00;
    ir_waw_hazard = 2'b00;
    ir_cheri_hazard = 2'b00;
    ir0_issued = 1'b0;
    ir1_issued = 1'b0;
    ir0_pl_sel = 5'h0;
    ir1_pl_sel = 5'h0;
    ex_valid_o = 5'h0;
    ir1_ooo_rdy_event = 1'b0;
    sbdfifo_wr_rdy_i = 2'b11;
    mispredict = 2'b00;
    branch_mispredict_event = 2'b00;
    wr_req_conflict = 1'b0;
    ir0_raw_cause = 5'h0;
    ir1_raw_cause = 5'h0;
    ir1_raw_by_ir0_event = 1'b0;
    ir0_stall_nohaz_event = 1'b0;
    ir1_stall_nohaz_event = 1'b0;
    reg_wrsv_q = '0;
    reg_cheri_trsv_q = '0;
    alupl0_fwd_act_i = '0;
    alupl1_fwd_act_i = '0;
    lspl_fwd_act_i = '0;
    multpl_fwd_act_i = '0;
    ir0_pl_fwd_act = '0;
    ir1_pl_fwd_act = '0;
    alupl0_fwd_act_i_any = 1'b0;
    alupl1_fwd_act_i_any = 1'b0;
    lspl_fwd_act_i_any = 1'b0;
    multpl_fwd_act_i_any = 1'b0;
    ctrl_fsm_cs = 16'(1 << CSM_DECODE);
    ctrl_fsm_ns = 16'(1 << CSM_DECODE);
    special_case_q = EXEC;
    handle_err = 1'b0;
    handle_sysctl = 1'b0;
    handle_cmplx = 1'b0;
    handle_irq = 1'b0;
    handle_debug = 1'b0;
    cmt_flush_o = 1'b0;
    cmt_err_i = 1'b0;
    ir0_dec = '0;
    ir1_dec = '0;
    ir_sysctl = 2'b00;
    ir_cmplx = 2'b00;
    csr_exc_info_o = '0;
    csr_save_cause_o = 1'b0;
    debug_csr_save_o = 1'b0;
    irq_pending_i = 1'b0;
    csr_mstatus_mie_i = 1'b0;
    irq_fast = '0;
    debug_req_i = 1'b0;
    debug_mode_q = 1'b0;
    debug_single_step_i = 1'b0;
    single_step_trap_q = 1'b0;
    debug_cause_o = DBG_CAUSE_NONE;
    intr_event = 1'b0;
    ir0_trap_event = 1'b0;
    priv_mode_i = PRIV_LVL_M;
    csr_mstatus_tw_i = 1'b0;
    ebreak_enter_debug = 1'b0;
    ir0_mode_err = 1'b0;
    ir_flush_o = 1'b0;
    pc_set_o = 1'b0;
    ira_full_data2_fwd_o = '0;
    irb_full_data2_fwd_o = '0;
    branch_info_i = '0;
    ex_alt_ctrl_o = '0;
  endtask

  task automatic drive_forwarding();
    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd5, 5'd0, 5'd0, 2'b01, 1'b0);
    ir0_issued = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd6, 5'd0, 5'd0, 2'b01, 1'b0);
    reg_wrsv_q[6] = 1'b1;
    ir_raw_hazard[0] = 1'b1;
    ir_hazard[0] = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd7, 5'd0, 5'd0, 2'b01, 1'b0);
    reg_wrsv_q[7] = 1'b1;
    alupl0_fwd_act_i[7] = 1'b1;
    ir0_pl_fwd_act[7] = 1'b1;
    alupl0_fwd_act_i_any = 1'b1;
    ir0_issued = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd8, 5'd0, 5'd0, 2'b01, 1'b0);
    reg_wrsv_q[8] = 1'b1;
    lspl_fwd_act_i[8] = 1'b1;
    ir0_pl_fwd_act[8] = 1'b1;
    lspl_fwd_act_i_any = 1'b1;
    ir0_stall_nohaz_event = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b11;
    ir0_dec = mk_dec(5'd0, 5'd0, 5'd9, 2'b00, 1'b1);
    ir1_dec = mk_dec(5'd9, 5'd0, 5'd0, 2'b01, 1'b0);
    ir0_issued = 1'b1;
    ir_hazard[1] = 1'b1;
    ir_raw_hazard[1] = 1'b1;
    ir1_raw_by_ir0_event = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd0, 5'd0, 5'd0, 2'b01, 1'b0);
    reg_wrsv_q[1] = 1'b1;
    ir0_pl_fwd_act[1] = 1'b1;
    @(posedge clk_i);
  endtask

  task automatic drive_prediction();
    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd1, 5'd2, 5'd0, 2'b11, 1'b0);
    ir0_dec.is_branch = 1'b1;
    ir0_dec.ptaken = 1'b0;
    branch_info_i.branch_taken[0] = 1'b0;
    ir0_issued = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd1, 5'd2, 5'd0, 2'b11, 1'b0);
    ir0_dec.is_branch = 1'b1;
    ir0_dec.ptaken = 1'b1;
    ir0_dec.alt_valid = 1'b1;
    branch_info_i.branch_taken[0] = 1'b0;
    branch_info_i.mis_not_taken[0] = 1'b1;
    mispredict[0] = 1'b1;
    branch_mispredict_event[0] = 1'b1;
    ex_alt_ctrl_o.apply = 1'b1;
    ex_alt_ctrl_o.flush = 1'b1;
    pc_set_o = 1'b1;
    ir0_issued = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd0, 5'd0, 5'd1, 2'b00, 1'b1);
    ir0_dec.is_jal = 1'b1;
    ir0_dec.ptaken = 1'b0;
    branch_info_i.mis_jal[0] = 1'b1;
    mispredict[0] = 1'b1;
    pc_set_o = 1'b1;
    ir0_issued = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b11;
    ir0_dec = mk_dec(5'd1, 5'd2, 5'd0, 2'b11, 1'b0);
    ir0_dec.is_branch = 1'b1;
    ir0_dec.ptaken = 1'b1;
    ir1_dec = mk_dec(5'd3, 5'd4, 5'd0, 2'b11, 1'b0);
    ir1_dec.is_branch = 1'b1;
    branch_info_i.branch_taken[0] = 1'b0;
    branch_info_i.mis_not_taken[0] = 1'b1;
    mispredict[0] = 1'b1;
    ir0_issued = 1'b1;
    @(posedge clk_i);

    clear();
    ir_valid_i = 2'b11;
    ir0_dec = mk_dec(5'd1, 5'd2, 5'd0, 2'b11, 1'b0);
    ir0_dec.is_branch = 1'b1;
    ir0_dec.ptaken = 1'b1;
    ir0_dec.alt_valid = 1'b1;
    ir1_dec = mk_dec(5'd3, 5'd4, 5'd0, 2'b11, 1'b0);
    ir1_dec.is_jalr = 1'b1;
    ir1_dec.ptaken = 1'b1;
    branch_info_i.branch_taken[0] = 1'b1;
    ex_alt_ctrl_o.cancel[0] = 1'b1;
    ir0_issued = 1'b1;
    ir1_issued = 1'b1;
    @(posedge clk_i);
  endtask

  task automatic drive_cheri_temporal();
    if (!CHERIoTEn) return;
    clear();
    ir_valid_i = 2'b01;
    ir0_dec = mk_dec(5'd2, 5'd0, 5'd0, 2'b01, 1'b0);
    ir0_dec.rs_cheri = 1'b1;
    reg_cheri_trsv_q[2] = 1'b1;
    ir_cheri_hazard[0] = 1'b1;
    @(posedge clk_i);
  endtask

  // Deliberately overlap all event kinds to detect accidental cycle resampling.
  // This is monitor stimulus, not a claim that every decode combination issues.
  task automatic sampling_burst(input int n);
    clear();
    ir_valid_i = 2'b11;
    ir0_dec = mk_dec(5'd5, 5'd6, 5'd7, 2'b11, n[1:0] == 3);
    ir1_dec = mk_dec(5'd7, 5'd8, 5'd0, 2'b11, 1'b0);
    ir0_dec.is_branch = 1'b1;
    ir1_dec.is_jalr = 1'b1;
    ir0_dec.rs_cheri = 1'b1;
    ir1_dec.rs_cheri = 1'b1;
    ir0_dec.ptaken = n[0];
    ir1_dec.ptaken = n[1];
    ir0_issued = 1'b1;
    ir1_issued = 1'b1;
    ira_is0_i = n[0];
    ir_any_err = n[1:0];
    ir_hazard = n[1:0];
    ir_raw_hazard = n[1:0];
    ir_waw_hazard = n[3:2];
    ir_cheri_hazard = n[1:0];
    ir0_raw_cause = 5'(n);
    ir1_raw_cause = 5'(~n);
    if (n[1:0] inside {1, 2}) reg_wrsv_q = '1;
    reg_cheri_trsv_q = n[2] ? '1 : '0;
    if (n[1:0] == 2) begin
      ir0_pl_fwd_act = '1;
      ir1_pl_fwd_act = '1;
      case ((n / 4) % 5)
        0: alupl0_fwd_act_i = '1;
        1: alupl1_fwd_act_i = '1;
        2: lspl_fwd_act_i = '1;
        3: multpl_fwd_act_i = '1;
        4: begin alupl0_fwd_act_i = '1; lspl_fwd_act_i = '1; end
      endcase
    end
    alupl0_fwd_act_i_any = |alupl0_fwd_act_i;
    alupl1_fwd_act_i_any = |alupl1_fwd_act_i;
    lspl_fwd_act_i_any = |lspl_fwd_act_i;
    multpl_fwd_act_i_any = |multpl_fwd_act_i;
    branch_info_i.branch_taken = n[1:0];
    pc_set_o = n[2];
    ex_alt_ctrl_o.apply = n[3];
    ex_alt_ctrl_o.cancel = n[1:0];
    ex_alt_ctrl_o.flush = n[4];
    mispredict = n[1:0];
    branch_mispredict_event = n[1:0];
    // handle_irq is masked by debug mode and single step (issuer.sv:736-737).
    handle_irq = n[0] & ~n[3] & ~n[4];
    handle_debug = n[1];
    handle_err = n[2];
    handle_sysctl = n[3];
    handle_cmplx = n[4];
    irq_pending_i = n[0];
    irq_fast = 15'(1 << (n % 15));
    csr_mstatus_mie_i = n[1];
    debug_req_i = n[2];
    debug_mode_q = n[3];
    debug_single_step_i = n[4];
    single_step_trap_q = n[5];
    csr_save_cause_o = 1'b1;
    csr_exc_info_o.mcause = 6'(n);
    debug_csr_save_o = n[5];
    intr_event = n[0];
    ir0_trap_event = n[1];
    wr_req_conflict = n[2];
    ir0_stall_nohaz_event = n[3];
    ir1_stall_nohaz_event = n[4];
    ir1_raw_by_ir0_event = n[5];
    cmt_flush_o = n[1];
    cmt_err_i = n[2];
  endtask
endmodule

module kudu_top
  import super_pkg::*;
#(
`ifdef CHERIoT
  parameter bit CHERIoTEn = 1'b1,
`else
  parameter bit CHERIoTEn = 1'b0,
`endif
  parameter bit LoadFiltEn = 1'b1
) ();
  logic clk, rst_n, pmode;
  issuer #(.CHERIoTEn(CHERIoTEn), .LoadFiltEn(LoadFiltEn)) issuer(.clk_i(clk), .rst_ni(rst_n),
                                                             .cheri_pmode_i(pmode));
  if_stage if_stage(.clk_i(clk), .rst_ni(rst_n));

  initial begin
    clk = 1'b0;
    forever #5 clk = ~clk;
  end

  task automatic tick();
    @(posedge clk);
  endtask

  task automatic check_issue_sampling();
    int states[20] = '{CSM_RESET, CSM_BOOT_SET, CSM_DECODE, CSM_CMT_FLUSH,
        CSM_WAIT_TRVK, CSM_DECODE, CSM_WAIT_CMT0, CSM_CMT_FLUSH,
        CSM_WAIT_TRVK, CSM_DECODE, CSM_WAIT_CMT0, CSM_ISSUE_SPECIAL,
        CSM_WAIT_CMPLX, CSM_DECODE, CSM_WAIT_CMT0, CSM_ISSUE_SPECIAL,
        CSM_WAIT_FINAL, CSM_SLEEP, CSM_DECODE, CSM_SLEEP};
    // Identical event-rich traffic during reset must produce no coverage.
    for (int n = 0; n < 8; n++) begin
      @(negedge clk);
      issuer.sampling_burst(n);
      @(posedge clk);
      #1;
    end
    for (int n = 0; n < 64; n++) begin
      @(negedge clk);
      rst_n = 1'b1;
      issuer.sampling_burst(n);
      issuer.ctrl_fsm_cs = 16'(1 << states[n % 20]);
      issuer.ctrl_fsm_ns = 16'(1 << states[(n + 1) % 20]);
      @(posedge clk);
      #1;
    end
    // Invalid slots, unused operands and x0 must not create operand samples.
    for (int n = 0; n < 3; n++) begin
      @(negedge clk);
      issuer.clear();
      issuer.ir0_dec = issuer.mk_dec(0, 0, 0, n == 0 ? 2'b00 : 2'b11, 0);
      issuer.ir1_dec = issuer.ir0_dec;
      issuer.ir_valid_i = n == 2 ? 2'b00 : 2'b11;
      @(posedge clk);
      #1;
    end
    // Exercise the saved-RA tracker across a nonblocking state update.
    @(negedge clk);
    issuer.clear();
    issuer.ir_valid_i = 2'b11;
    issuer.ir0_dec = issuer.mk_dec(0, 0, 1, 2'b00, 1);
    issuer.ir1_dec = issuer.mk_dec(1, 0, 0, 2'b01, 0);
    issuer.ir1_dec.is_jalr = 1;
    issuer.ir1_dec.ptaken = 1;
    issuer.ir1_dec.ptarget = cheri_pkg::NULL_REG_CAP;
    issuer.ir0_issued = 1;
    issuer.ir_raw_hazard = 2'b10;
    @(posedge clk);
    #1;
    @(negedge clk);
    issuer.ir0_dec = issuer.ir1_dec;
    issuer.ir_valid_i = 2'b01;
    issuer.ir_raw_hazard = 2'b00;
    issuer.ira_full_data2_fwd_o.d0 =
        cheri_pkg::op2fullcap(cheri_pkg::reg2opcap(cheri_pkg::NULL_REG_CAP));
    @(posedge clk);
    #1;
    $display("PASS issue sampling CHERIoTEn=%0d LoadFiltEn=%0d PMODE=%0d",
             CHERIoTEn, LoadFiltEn, pmode);
    $finish;
  endtask

  task automatic check_forwarding_pairs();
    // Present every forwarding-only bit during reset; none may sample.
    for (int r = 1; r < 32; r++) begin
      @(negedge clk);
      issuer.clear();
      issuer.ir0_pl_fwd_act[r] = 1'b1;
      @(posedge clk);
      #1;
    end
    for (int r = 1; r < 32; r++) begin
      for (int pair_value = 0; pair_value < 4; pair_value++) begin
        if (pair_value == 2) continue;
        @(negedge clk);
        rst_n = 1'b1;
        issuer.clear();
        issuer.ir0_pl_fwd_act[0] = 1'b1;
        issuer.ir0_pl_fwd_act[r] = pair_value[1];
        issuer.reg_wrsv_q[r] = pair_value[0];
        @(posedge clk);
        #1;
        // A forwarding-only value between sampling edges must not create hits.
        issuer.ir0_pl_fwd_act = '1;
        issuer.reg_wrsv_q = '0;
        #1;
        issuer.clear();
      end
    end
    $display("BEGIN pair_2 coverage");
    for (int r = 1; r < 32; r++) begin
      @(negedge clk);
      issuer.clear();
      issuer.ir0_pl_fwd_act[r] = 1'b1;
      @(posedge clk);
      #1;
    end
    $display("PASS forwarding pairs CHERIoTEn=%0d PMODE=%0d", CHERIoTEn, pmode);
    $finish;
  endtask

  initial begin
    if (!$value$plusargs("PMODE=%d", pmode)) pmode = 1'b1;
    rst_n = 1'b0;
    issuer.clear();
    if_stage.clear();
    if ($test$plusargs("issue_sampling")) check_issue_sampling();
    if ($test$plusargs("forwarding_pairs")) check_forwarding_pairs();
    repeat (2) tick();
    rst_n = 1'b1;
    issuer.drive_forwarding();
    issuer.drive_prediction();
    issuer.drive_cheri_temporal();

    if_stage.clear();
    if_stage.pdt_en_i = 1'b1;
    if_stage.pdt_pc_set = 2'b11;
    if_stage.pdt_branch_go = 2'b01;
    if_stage.pdt_jal_go = 2'b10;
    tick();
    if_stage.clear();
    if_stage.pdt_en_i = 1'b1;
    if_stage.pdt_pc_set = 2'b11;
    if_stage.pdt_jalr_go = 2'b01;
    if_stage.pdt_branch_go = 2'b10;
    tick();
    if_stage.clear();
    repeat (2) tick();
    $display("PASS frontend temporal CHERIoTEn=%0d PMODE=%0d", CHERIoTEn, pmode);
    $finish;
  end
endmodule
