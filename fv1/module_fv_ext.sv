//
// extend internal modules for SVA & FCOV signals
//
module bindfiles;
  bind issuer              issuer_fv_ext          issuer_fv_ext_i (.*);
  bind committer           committer_fv_ext       committer_fv_ext_i (.*);
  bind prefetch_buffer64   prefetch_fv_ext        prefetch_fv_ext_i (.*);
  bind ls_pipeline         ls_pipeline_fv_ext     ls_pipeline_fv_ext_i (.*);
  bind mult_pipeline       mult_pipeline_fv_ext   mult_pipeline_fv_ext_i (.*);
  bind alu_pipeline        alu_pipeline_fv_ext    alu_pipeline_fv_ext_i (.*);
  bind dcache              dcache_fv_ext          dcache_fv_ext_i (.*);
  bind kudu_top            kudu_top_fv_ext        kudo_top_fv_ext_i (.*);
`ifdef KUDU_FORMAL_G0_Long
  // helper lemmas for the G0_Long asserts (see the helper modules at the end of this file)
  bind kudu_top            fv_long_help_cmplx     fv_long_help_cmplx_i (.*);
  bind kudu_top            fv_long_help_fwdact    fv_long_help_fwdact_i (.*);
  bind kudu_top            fv_long_help_pcc       fv_long_help_pcc_i (.*);
`endif
endmodule

////////////////////////////////////////////////////////////////
// issuer
////////////////////////////////////////////////////////////////

module issuer_fv_ext import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  logic [1:0]     ir_valid_i,
  input  logic           ir0_issued,
  input  logic           ir1_issued,
  input  logic           irq_pending_i,
  input  logic           csr_mstatus_mie_i,
  input  logic           cmt_err_i,
  input  logic           debug_req_i,
  input  logic           handle_special,
  input  logic           handle_irq,
  input  special_case_e  special_case_q,
  input  logic [15:0]    ctrl_fsm_cs,
  input  logic [15:0]    ctrl_fsm_ns,
  input  logic [1:0]     sbdfifo_wr_valid_o,
  input  sbd_fifo_t      sbdfifo_wdata0_o,
  input  sbd_fifo_t      sbdfifo_wdata1_o,
  input  logic [1:0]     sbdfifo_rd_valid_i,
  input  logic           trvk_outstanding_i,
  input  logic [1:0]     issuer_rdy_o,
  input  logic [2:0]     ir0_cjalr_err_i,
  input  logic [4:0]     ir0_pl_sel,
  input  logic [4:0]     ir1_pl_sel,
  input  logic [4:0]     ex_rdy,
  input  logic           pc_set_o,
  input  logic           ir_flush_o,
  input  logic           ir_hold_o,
  input  logic           csr_save_cause_o,
  input  ir_dec_t        ir0_dec, 
  input  ir_dec_t        ir1_dec, 
  input  logic [31:0]    ir0_reg_rd_req, 
  input  logic [31:0]    ir0_reg_wr_req, 
  input  logic [31:0]    ir1_reg_rd_req, 
  input  logic [31:0]    ir1_reg_wr_req,
  input  logic [1:0]     mispredict,
  input  logic           debug_ebreak,
  input  logic [31:0]    ir0_nxt_pc_q,
  input  logic           lspl_rdy_i,
  input  logic            cmplx_instr_start_o
);

`ifdef KUDU_FORMAL_G1_0
  // we only issue actual instructions (not interrurpts or traps)
  AssertIssue0Valid: assert property (@(posedge clk_i) 
    (ir0_issued  |-> ir_valid_i[0] ));
  AssertIssue1Valid: assert property (@(posedge clk_i) 
    (ir1_issued  |-> ir_valid_i[1] ));

  //
  // IR1 (dual-issue) enabling
  // 

  // IR1 should only be issued when IR0 is issued and there is no special case
  AssertIssue1NoErrOnly: assert property (@(posedge clk_i) 
    (ir1_issued |-> (ir0_issued && ~handle_special && ctrl_fsm_cs[CSM_DECODE]
                    && ~mispredict[0] && ~ir0_dec.is_jalr) ));

  // if pc_set & ir_flush (from ir0 misprediction, etc), issuer_rdy_o[1] is a don't care
  AssertDequeueIR1: assert property (@(posedge clk_i) 
    (issuer_rdy_o[1] |-> (ctrl_fsm_cs[CSM_DECODE] | ctrl_fsm_cs[CSM_CMT_FLUSH] | ctrl_fsm_cs[CSM_ISSUE_SPECIAL]) ));

  AssertDequeueIR1Normal: assert property (@(posedge clk_i) 
    ((issuer_rdy_o[1] & ctrl_fsm_cs[CSM_DECODE]) |-> (ir1_issued | (pc_set_o & ir_flush_o)) ));

  // IR1 is only issued if no RAW or WAW hazard with IR0
  AssertIR1Hazard0: assert property (@(posedge clk_i) 
    (ir1_issued |-> (((ir0_reg_wr_req & ir1_reg_rd_req) == 0) && ((ir0_reg_wr_req & ir1_reg_wr_req) == 0)) ));

  //
  // "Normal" issue, non-local case
  //

  // all "normal" issued instructions must be retired from IR
  logic ir0_issued_normal, ir1_issued_normal;
  assign ir0_issued_normal = ir0_issued & ctrl_fsm_cs[CSM_DECODE]; 
  assign ir1_issued_normal = ir1_issued & ctrl_fsm_cs[CSM_DECODE];
  
  AssertIR0IssueNormal0: assert property (@(posedge clk_i) 
    (ir0_issued_normal  |-> issuer_rdy_o[0] ));
  AssertIR1IssueNormal0: assert property (@(posedge clk_i) 
    (ir1_issued_normal  |-> issuer_rdy_o[1] ));

  // make sure all issued instruction are send to SBD and EX pipelines
  logic ir0_issued_nonlocal, ir1_issued_nonlocal;

  // this assertion is local to the issuer module so it can't model the instr decoder
  assign ir0_issued_nonlocal = ir0_issued & ctrl_fsm_cs[CSM_DECODE] & (ir0_dec.pl_type != PL_LOCAL);
  assign ir1_issued_nonlocal = ir1_issued & ctrl_fsm_cs[CSM_DECODE] & (ir1_dec.pl_type != PL_LOCAL);
  AssertIR0IssueNonLocal0: assert property (@(posedge clk_i) 
    (ir0_issued_nonlocal  |-> sbdfifo_wr_valid_o[0] ));
  AssertIR0IssueNonLocal1: assert property (@(posedge clk_i) 
    (ir0_issued_nonlocal  |-> $onehot(sbdfifo_wdata0_o.pl[4:1]) ));

  AssertIR0IssueExRdy0: assert property (@(posedge clk_i) 
    (ir0_issued_nonlocal  |-> (((~ir0_pl_sel | ex_rdy) == 5'b11111)) ));

  AssertIR1IssueNonLocal0: assert property (@(posedge clk_i) 
    ((ir1_issued_nonlocal & ir0_issued_nonlocal) |-> sbdfifo_wr_valid_o[1] ));
  AssertIR1IssueNonLocal1: assert property (@(posedge clk_i) 
    (ir1_issued_nonlocal  |-> $onehot(sbdfifo_wdata1_o.pl[4:1]) ));

  AssertIR1IssueExRdy0: assert property (@(posedge clk_i) 
    (ir1_issued_nonlocal  |-> (((~ir1_pl_sel | ex_rdy) == 5'b11111) &&
                               ((ir1_pl_sel[4:1] & ir0_pl_sel[4:1]) == 4'b0000)) ));
  AssertCmt1forIssue1: assert property (@(posedge clk_i) 
    (sbdfifo_wr_valid_o[1] |-> ir1_issued ));
  
  AssertMisPredict0: assert property (@(posedge clk_i) 
    ((ir0_issued_normal & mispredict[0]) |-> (pc_set_o & ~ir1_issued) ));
  AssertMisPredict1: assert property (@(posedge clk_i) 
    ((ir1_issued_normal & mispredict[1]) |-> pc_set_o ));

  // 
  // "Special" issue case
  //
  logic ir0_issued_speical;
  assign ir0_issued_special = ir0_issued & ctrl_fsm_cs[CSM_ISSUE_SPECIAL];

  // hold the IR registers while waiting for cmt fifo to clear
  AssertIssueSpecialWait0: assert property (@(posedge clk_i) 
    (ctrl_fsm_cs[CSM_WAIT_CMT0]  |-> (issuer_rdy_o == 2'b00) ));
    // (ctrl_fsm_cs[CSM_WAIT_CMT0]  |-> ((issuer_rdy_o == 2'b00) && ir_hold_o) ));

  AssertIssueSpecial0: assert property (@(posedge clk_i) 
    (ir0_issued_special  |-> issuer_rdy_o[0]  ));

  logic [1:0] pc_set_cnt;
  logic       special_in_progress, special_issued;
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      pc_set_cnt <= 0;
      special_in_progress <= 1'b0;
      special_issued      <= 1'b0;
    end else begin
      if (ctrl_fsm_cs[CSM_DECODE] || ctrl_fsm_cs[CSM_CMT_FLUSH])
        pc_set_cnt <= 0;
      else if (pc_set_o)
        pc_set_cnt <= pc_set_cnt + 1;

      if (ctrl_fsm_ns[CSM_DECODE] || ctrl_fsm_ns[CSM_CMT_FLUSH])
        special_in_progress <= 1'b0;
      else if (ctrl_fsm_ns[CSM_WAIT_CMT0])
        special_in_progress <= 1'b1;

      if (ctrl_fsm_cs[CSM_DECODE] || ctrl_fsm_cs[CSM_CMT_FLUSH])
        special_issued <= 1'b0;
      else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL])
        special_issued <= 1'b1;
    end
  end

  // a special case can only have max 1 pc_set (1st being CJALR speculative)
  AssertPCSetSPecial0: assert property (@(posedge clk_i) ((pc_set_cnt <= 1)));

`endif

`ifdef KUDU_FORMAL_G1_1
  //
  // Interrupt handling
  //
  AssumeNoDebug: assume property (@(posedge clk_i) 
    ((debug_req_i == 1'b0)  && (debug_ebreak == 1'b0) && ~ir0_dec.sysctl.ebrk &&
     ~ir0_dec.sysctl.dret ));
  AssumeNoCMTErr: assume property (@(posedge clk_i) 
    (cmt_err_i == 1'b0) );
  AssumeNoCJALRErr: assume property (@(posedge clk_i) 
    (ir0_cjalr_err_i == 3'b000));
  // if ir_valid becomes 1 while in wait_cmt0, we may still go to EXEC
  AssumeNoNewInstr: assume property (@(posedge clk_i) 
    (ctrl_fsm_cs[CSM_WAIT_CMT0] |-> ($stable (ir_valid_i) && $stable(ir0_dec)) ));

  // note in KUDU, impossible for csr_mstatus_mie_i to change while in DECODE or WAIT_CMT0, since
  // CSR write operations are treated as "special" (not issued till all previous instructions complete)
  AssumeIRQStable: assume property (@(posedge clk_i) 
    (ctrl_fsm_cs[CSM_WAIT_CMT0]  |-> $stable (irq_pending_i) ));

  AssumeSBDEmpty: assume property (@(posedge clk_i) 
    ((ctrl_fsm_cs[CSM_DECODE] & handle_special) |-> 
      ##[0:2] ((sbdfifo_rd_valid_i == 2'b00) && ~trvk_outstanding_i) ));

  //
  // Pending tnterrupt will be handled if there is no instruction in IR or no fetch errors
  //
  logic irq_case0, irq_case1;
  logic irq_handled_or_disabled;

  assign irq_case0 = ctrl_fsm_cs[CSM_DECODE] & irq_pending_i & csr_mstatus_mie_i & ~ir_valid_i[0]; 
  assign irq_case1 = ctrl_fsm_cs[CSM_DECODE] & irq_pending_i & csr_mstatus_mie_i & ir_valid_i[0] &
                     ~ir0_dec.any_err &  ~ir0_dec.sysctl.valid & ~ir0_dec.is_cmplx;

  assign irq_handled_or_disabled = ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && 
                                   ((special_case_q == IRQ) || (special_case_q == NULL)); 

  AssertIssueIRQ0: assert property (@(posedge clk_i) 
    (irq_case0  |-> (##[1:5] irq_handled_or_disabled) ));
  AssertIssueIRQ1: assert property (@(posedge clk_i) 
    (irq_case1  |-> (##[1:5] irq_handled_or_disabled) ));

   // NULL case is atually unreachable now?
//  AssertIssueIRQNull: assert property (@(posedge clk_i) 
//    ( (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (special_case_q == NULL)) |-> (~pc_set_o && ~csr_save_cause_o) ));

`endif
endmodule


////////////////////////////////////////////////////////////////
// committer
////////////////////////////////////////////////////////////////

module committer_fv_ext import super_pkg::*; (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic [1:0]        sbdfifo_rd_valid_i,
  input  sbd_fifo_t         sbdfifo_rdata0_i,
  input  sbd_fifo_t         sbdfifo_rdata1_i,
  input  logic [1:0]        sbdfifo_rd_rdy_o,
  input  logic              alupl0_valid_i,
  input  pl_out_t           alupl0_output_i,
  input  logic              alupl0_rdy_o,
  input  logic              alupl1_valid_i,
  input  pl_out_t           alupl1_output_i,
  input  logic              alupl1_rdy_o,
  input  logic              lspl_valid_i,
  input  pl_out_t           lspl_output_i,
  input  logic              lspl_rdy_o,
  input  logic              multpl_valid_i,
  input  pl_out_t           multpl_output_i,
  input  logic              multpl_rdy_o,
  input  logic              cmt_flush_i,
  input  logic [31:0]       cmt_regwr_o,
  input  logic              cmt_err_o,
  input  exc_info_t         cmt_err_info_o,
  input  logic [4:0]        rf_waddr0_o,
  input  logic [RegW-1:0]   rf_wdata0_o,
  input  logic              rf_we0_o,
  input  logic [4:0]        rf_waddr1_o,
  input  logic [RegW-1:0]   rf_wdata1_o,
  input  logic              rf_we1_o,
  input  logic [4:0]        rf_waddr2_o,
  input  logic [RegW-1:0]   rf_wdata2_o,
  input  logic              rf_we2_o,
  input  logic              cmt_err_q
  );

`ifdef KUDU_FORMAL_G2
  typedef enum logic [1:0] {
    ALUPL0,
    ALUPL1,
    LSPL,
    MULTPL
  } pl_id_e;

  typedef struct packed {
    logic       valid;
    pl_id_e     pl;
    logic       pl_valid;
    pl_out_t    pl_out;
  } sbd_req_t;

  function automatic sbd_req_t parse_sbd_req (
    logic      sbdfifo_rd_valid,
    sbd_fifo_t sbdfifo_rdata, 
    logic      alupl0_valid_i,
    pl_out_t   alupl0_output_i,
    logic      alupl1_valid_i,
    pl_out_t   alupl1_output_i,
    logic      lspl_valid_i,
    pl_out_t   lspl_output_i,
    logic      multpl_valid_i,
    pl_out_t   multpl_output_i
    );

    sbd_req_t result;

    result.valid = sbdfifo_rd_valid;

    if (sbdfifo_rdata.pl[1]) begin 
      result.pl       = ALUPL0;
      result.pl_valid = alupl0_valid_i;
      result.pl_out   = alupl0_output_i;
    end else if (sbdfifo_rdata.pl[2]) begin
      result.pl       = ALUPL1;
      result.pl_valid = alupl1_valid_i;
      result.pl_out   = alupl1_output_i;
    end else if (sbdfifo_rdata.pl[3]) begin
      result.pl       = LSPL;
      result.pl_valid = lspl_valid_i;
      result.pl_out   = lspl_output_i;
    end else if (sbdfifo_rdata.pl[4]) begin
      result.pl       = MULTPL;
      result.pl_valid = multpl_valid_i;
      result.pl_out   = multpl_output_i;
    end

    return result;
  endfunction

  sbd_req_t [1:0] sbd_req;

  assign sbd_req[0] = parse_sbd_req (
    sbdfifo_rd_valid_i[0],
    sbdfifo_rdata0_i,
    alupl0_valid_i,
    alupl0_output_i,
    alupl1_valid_i,
    alupl1_output_i,
    lspl_valid_i,
    lspl_output_i,
    multpl_valid_i,
    multpl_output_i
    );

  assign sbd_req[1] = parse_sbd_req (
    sbdfifo_rd_valid_i[1],
    sbdfifo_rdata1_i,
    alupl0_valid_i,
    alupl0_output_i,
    alupl1_valid_i,
    alupl1_output_i,
    lspl_valid_i,
    lspl_output_i,
    multpl_valid_i,
    multpl_output_i
    );

  //
  // Assumption on module inputs
  // 
  AssumeSBDFifoValid: assume property (@(posedge clk_i) 
    (sbdfifo_rd_valid_i[1] |-> sbdfifo_rd_valid_i[0] ));
  AssumeSBDFifoRdata0: assume property (@(posedge clk_i) 
    (sbdfifo_rd_valid_i[0] |-> $onehot(sbdfifo_rdata0_i[4:1]) ));
  AssumeSBDFifoRdata1: assume property (@(posedge clk_i) 
    (sbdfifo_rd_valid_i[1] |-> $onehot(sbdfifo_rdata1_i[4:1]) ));

  // 
  // Waddr conflict, load early case 
  //  -- 1st req is load, 2nd req is non-load, write to the same register
  //  -- load reg_wr is suppressed
  //
  logic        case1_def;
  logic  [1:0] case1_out;

  assign case1_def = ~cmt_err_q && 
                     sbd_req[0].valid && (sbd_req[0].pl == LSPL) && sbd_req[0].pl_valid && 
                     sbd_req[0].pl_out.we && ~sbd_req[0].pl_out.err && 
                     sbd_req[1].valid &&  (sbd_req[1].pl != LSPL) && sbd_req[1].pl_valid && 
                     sbd_req[1].pl_out.we && ~sbd_req[1].pl_out.err && 
                     (sbd_req[0].pl_out.waddr == sbd_req[1].pl_out.waddr);
             
  assign case1_out[0] = ~rf_we0_o & rf_we1_o & ~rf_we2_o;
  assign case1_out[1] = (rf_waddr1_o == sbd_req[1].pl_out.waddr) && 
                       (rf_wdata1_o == sbd_req[1].pl_out.wdata);
  AssertCmtCase1: assert property (@(posedge clk_i) (case1_def  |-> (&case1_out) ));

  // 
  // Waddr conflict, load late case 
  //  -- 2nd req is load, 1st req is non-load, write to the same register
  //  -- load reg_wr on wr port 2
  //
  logic        case2_def;
  logic  [2:0] case2_out;

  assign case2_def = ~cmt_err_q && 
                     sbd_req[1].valid && (sbd_req[1].pl == LSPL) && sbd_req[1].pl_valid && 
                     sbd_req[1].pl_out.we && ~sbd_req[1].pl_out.err && 
                     sbd_req[0].valid &&  (sbd_req[0].pl != LSPL) && sbd_req[0].pl_valid && 
                     sbd_req[0].pl_out.we && ~sbd_req[0].pl_out.err && 
                     (sbd_req[0].pl_out.waddr == sbd_req[1].pl_out.waddr);
             
  assign case2_out[0] = rf_we0_o & ~rf_we1_o & rf_we2_o;
  assign case2_out[1] = (rf_waddr0_o == sbd_req[0].pl_out.waddr) && 
                        (rf_wdata0_o == sbd_req[0].pl_out.wdata);
  assign case2_out[2] = (rf_waddr2_o == sbd_req[1].pl_out.waddr) && 
                        (rf_wdata2_o == sbd_req[1].pl_out.wdata);

  AssertCmtCase2: assert property (@(posedge clk_i) (case1_def  |-> (&case1_out) ));

  //
  // pipeline conflict case
  //
  logic [1:0] sbd_req_valid; 
  logic       sbd_req_conflict;

  assign sbd_req_valid[0] = sbd_req[0].valid && sbd_req[0].pl_valid && 
                            ~sbd_req[0].pl_out.err;
  assign sbd_req_valid[1] = sbd_req[1].valid && sbd_req[1].pl_valid && 
                            ~sbd_req[1].pl_out.err;

  assign sbd_req_conflict = (sbd_req[0].pl == sbd_req[1].pl);

  AssertCmtDeque0: assert property (@(posedge clk_i) 
    ( (sbd_req_valid[0] & ~cmt_err_q) |-> (sbdfifo_rd_rdy_o[0]) ));
  AssertCmtDeque1: assert property (@(posedge clk_i) 
    ( (sbd_req_valid[1] & sbd_req_valid[0] & ~sbd_req_conflict & ~cmt_err_q) |-> sbdfifo_rd_rdy_o[1] ));
  AssertCmtDeque2: assert property (@(posedge clk_i) 
    ( (sbd_req_valid[1] & sbd_req_conflict & ~cmt_err_q) |-> (~sbdfifo_rd_rdy_o[1]) ));
  

  //
  // RF We generation only for valid requests (no error)
  //
  logic  [1:0] sbd_req_valid_nonls, sbd_req_valid_ls;
  assign sbd_req_valid_nonls[0] = sbd_req[0].valid && (sbd_req[0].pl != LSPL) && sbd_req[0].pl_valid && 
                                  sbd_req[0].pl_out.we && ~sbd_req[0].pl_out.err;
  assign sbd_req_valid_nonls[1] = sbd_req[1].valid && (sbd_req[1].pl != LSPL) && sbd_req[1].pl_valid && 
                                  sbd_req[1].pl_out.we && ~sbd_req[1].pl_out.err;

  assign sbd_req_valid_ls[0] = sbd_req[0].valid && (sbd_req[0].pl == LSPL) && sbd_req[0].pl_valid && 
                               sbd_req[0].pl_out.we && ~sbd_req[0].pl_out.err;
  assign sbd_req_valid_ls[1] = sbd_req[1].valid && (sbd_req[1].pl == LSPL) && sbd_req[1].pl_valid && 
                               sbd_req[1].pl_out.we && ~sbd_req[1].pl_out.err;

  AssertCmtRfWe0: assert property (@(posedge clk_i) 
    (rf_we0_o |-> sbd_req_valid_nonls[0]));

  AssertCmtRfWe1: assert property (@(posedge clk_i) 
    (rf_we1_o |-> sbd_req_valid_nonls[1]));

  AssertCmtRfWe2: assert property (@(posedge clk_i) 
    (rf_we2_o |-> (|sbd_req_valid_ls) ));

  // 
  // Only dequeues the EX pipelines if SBD requests are valid and in order
  //
  
  logic [3:0] req_valid_pl_vec;

  for (genvar i=0; i<4; i++) begin
    assign req_valid_pl_vec[i] = (sbd_req[0].valid && (sbd_req[0].pl == i)) ||  
                                 (sbd_req[0].valid && sbd_req[0].pl_valid && sbd_req[1].valid);
  end

  AssertALU0Read: assert property (@(posedge clk_i) 
    (alupl0_rdy_o |-> req_valid_pl_vec[ALUPL0]));
  AssertALU1Read: assert property (@(posedge clk_i) 
    (alupl1_rdy_o |-> req_valid_pl_vec[ALUPL1]));
  AssertLSRead: assert property (@(posedge clk_i) 
    (lspl_rdy_o |-> req_valid_pl_vec[LSPL]));
  AssertMultRead: assert property (@(posedge clk_i) 
    (multpl_rdy_o |-> req_valid_pl_vec[MULTPL]));

`endif
endmodule

////////////////////////////////////////////////////////////////
// Prefetcher
////////////////////////////////////////////////////////////////

module prefetch_fv_ext import super_pkg::*; (
  input  logic          clk_i,
  input  logic          rst_ni,
  input  logic          req_i,
                        
  input  logic          branch_i,
  input  logic [31:0]   addr_i,
  input  ex_alt_ctrl_t  ex_alt_ctrl_i,
  input  logic          alloc_alt_i, 

  input  logic [1:0]    ready_i,
  input  logic [1:0]    valid_o,
  input  ir_reg_t       instr0_o,
  input  ir_reg_t       instr1_o,
  input  logic [31:0]   instr1_pc_spec0_o,
  input  logic [31:0]   instr1_pc_spec1_o,

  // goes to instruction memory / instruction cache
  input  logic          instr_req_o,
  input  logic          instr_gnt_i,
  input  logic [31:0]   instr_addr_o,
  input  logic [63:0]   instr_rdata_i,
  input  logic          instr_err_i,
  input  logic          instr_rvalid_i
);

`ifdef KUDU_FORMAL_G3
  //
  // Memory interface I/O assumptions
  //
  logic        instr_rvalid_mem, instr_err_mem;
  logic [63:0] instr_rdata_mem;
  logic        req_not_granted;
  logic [31:0] addr0, addr1;

  logic [31:0] exp_pc0, exp_pc1;
  logic [31:0] exp_insn0, exp_insn1;
  logic        exp_err0, exp_err1;
  logic [3:0]  pc_delta;

  `define MEMMASK 32'h00ff_00ff
  // The idea is that we want to prove the instr fetched is from the correct memory address.
  // - assume the each word in the memory = Func(addr)
  // - we know the expected PC value (starting at the branch address and increment)
  // - Expected instr = Func(Expect_pc)
  // - then we just compare expected instr vs prefetcher output
  // - mask off part of the word to reduce FV run time

  function automatic logic[31:0] get_mem_word32 (logic [31:0] addr);
    logic [31:0] result;

    result = {2'b00, addr[31:2]} & `MEMMASK;
    return result;
  endfunction

  function automatic logic[63:0] get_mem_word64 (logic [31:0] addr);
    logic [31:0] addr0, addr1;
    logic [63:0] result;
    
    addr0 = {addr[31:3], 3'b000};
    addr1 = {addr[31:3], 3'b100};

    result[31:0]  = get_mem_word32(addr0);
    result[63:32] = get_mem_word32(addr1);

    return result;
  endfunction

  function automatic logic get_mem_err (logic [31:0] addr);
    logic result;

    result = addr[16] ^ addr[9];
    return result;
  endfunction

  assign exp_pc1 = exp_pc0 + ((exp_insn0[1:0] == 2'b11) ? 4 : 2); 

  always_comb begin
    logic [31:0] b0, b1, c0, c1;

    b0 = get_mem_word32((exp_pc0+4));
    b1 = get_mem_word32((exp_pc1+4));

    c0 = get_mem_word32((exp_pc0));
    c1 = get_mem_word32((exp_pc1));

    exp_insn0 = exp_pc0[1] ? {b0[15:0], c0[31:16] } : c0;
    exp_insn1 = exp_pc1[1] ? {b1[15:0], c1[31:16] } : c1;
  end 

  always_comb begin
    if ((exp_pc0[2:1] == 2'b11) && (exp_insn0[1:0] == 2'b11)) 
      exp_err0 = get_mem_err(exp_pc0) | get_mem_err((exp_pc0+8));
    else 
      exp_err0 = get_mem_err(exp_pc0);

    if ((exp_pc1[2:1] == 2'b11) && (exp_insn1[1:0] == 2'b11)) 
      exp_err1 = get_mem_err(exp_pc1) | get_mem_err((exp_pc1+8));
    else 
      exp_err1 = get_mem_err(exp_pc1);
  end

  always_comb begin
    logic [3:0] a0, a1;
    if (valid_o[0] & ready_i[0])
      a0 = (exp_insn0[1:0] == 2'b11) ? 4 : 2; 
    else
      a0 = 0;

    if (valid_o[1] & ready_i[1])
      a1 = (exp_insn1[1:0] == 2'b11) ? 4 : 2; 
    else
      a1 = 0;

    pc_delta = a0 + a1;
  end

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      instr_rvalid_mem <= 1'b0;
      instr_rdata_mem  <= 64'h0;
      instr_err_mem    <= 1'b0;
      exp_pc0          <= 0;
      req_not_granted  <= 1'b0;
    end else begin
      instr_rvalid_mem <= instr_req_o & instr_gnt_i;

      if (instr_req_o & instr_gnt_i)
        instr_rdata_mem <= get_mem_word64(instr_addr_o);  // simple assumption 

      if (instr_req_o & instr_gnt_i)
        instr_err_mem <= get_mem_err(instr_addr_o);  // error injection

      if (branch_i)
        exp_pc0 <= addr_i;
      else
        exp_pc0 <= exp_pc0 + pc_delta;

      if (instr_gnt_i)
        req_not_granted <= 1'b0;
      else if (instr_req_o & ~instr_gnt_i)
        req_not_granted <= 1'b1;
      
    end
  end

  //
  // memory interface assumptions
  //
  AssumeInstrGnt0: assume property (instr_req_o |-> ##[0:3] instr_gnt_i);
  AssumeInstrGnt1: assume property ((~rst_ni | ~instr_req_o) |-> ~instr_gnt_i);
  //AssumeInstrGntNoDly0:   assume property (instr_req_o |-> instr_gnt_i);
  //AssumeInstrGntNoDly1:   assume property (~instr_req_o |-> ~instr_gnt_i);
  AssumeInstrValid:       assume property (instr_rvalid_i == instr_rvalid_mem);
  AssumeInstrErr:         assume property (instr_err_i == instr_err_mem);
  AssumeFetchedInstr:     assume property (instr_rdata_i == instr_rdata_mem);

  //
  // Assuming no ALT (runtime too long)
  //
  AssumeNoALT0:  assume property (ex_alt_ctrl_i.apply == '0);
  AssumeNoALT1:  assume property (alloc_alt_i == 1'b0);
 
  AssertFetchInstr0PC:  assert property (@(posedge clk_i) 
    (valid_o[0] |-> (instr0_o.pc == exp_pc0) ));

  AssertFetchInstr1PC:  assert property (@(posedge clk_i) 
    (valid_o[1] |-> (instr1_o.pc == exp_pc1) ));
  
  AssertFetchInstr0Data16:  assert property (@(posedge clk_i) 
    ( (valid_o[0] && (exp_insn0[1:0] != 2'b11)) |-> (instr0_o.insn[15:0] == exp_insn0[15:0])));

  AssertFetchInstr0Data32:  assert property (@(posedge clk_i) 
    ( (valid_o[0] && (exp_insn0[1:0] == 2'b11)) |-> (instr0_o.insn == exp_insn0))); 

  AssertFetchInstr1Data16:  assert property (@(posedge clk_i) 
    ( (valid_o[1] && (exp_insn1[1:0] != 2'b11)) |-> (instr1_o.insn[15:0] == exp_insn1[15:0])));

  AssertFetchInstr1Data32:  assert property (@(posedge clk_i) 
    ( (valid_o[1] && (exp_insn1[1:0] == 2'b11)) |-> (instr1_o.insn == exp_insn1)));

  AssertFetchInstr0Err:  assert property (@(posedge clk_i) 
    ( valid_o[0] |-> (instr0_o.errs.fetch_err == exp_err0) ));

  AssertFetchInstr1Err:  assert property (@(posedge clk_i) 
    ( valid_o[1] |-> (instr1_o.errs.fetch_err == exp_err1) ));

  // Memory bus protocol
  // Instr_req and instr_addr should be hold stable if instr request is not granted
  AssertInstrIfProtocol0:  assert property (@(posedge clk_i) 
    ( req_not_granted |-> $stable(instr_addr_o) ));
  AssertInstrIfProtocol1:  assert property (@(posedge clk_i) 
    ( req_not_granted |-> $stable(instr_req_o) ));

`endif
endmodule

////////////////////////////////////////////////////////////////
// LS Pipeline
////////////////////////////////////////////////////////////////

module ls_pipeline_fv_ext import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; (
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic            debug_mode_i,

  input  logic            flush_i,
  input  logic            us_valid_i,
  input  logic            lspl_rdy_o,
  input  ir_dec_t         instr_dec,

  // downstream (commit) side interface
  input  logic            ds_rdy_i,
  input  logic            lspl_valid_o,
  input  pl_out_t         lspl_output_o,

  // data memory interface
  input  logic            data_req_o,
  input  logic            data_we_o,
  input  logic [3:0]      data_be_o,
  input  logic            data_is_cap_o,
  input  logic [3:0]      data_amo_flag_o,
  input  logic [31:0]     data_addr_o,
  input  logic [MemW-1:0] data_wdata_o,
  input  logic            data_gnt_i,
  input  logic            data_rvalid_i,
  input  logic            data_err_i,
  input  logic            data_sc_fail_i,
  input  logic [MemW-1:0] data_rdata_i,

  input  logic            cmplx_lsu_req_valid_i,
  input  logic            lsu_req,
  input  logic            lsu_req_done,
  input  lsu_req_info_t   lsu_req_info,
  input  logic            lsu_resp_valid,
  input  logic            resp_err_latched,
  input  logic            lsu_err_active,
  input  logic            csr_op_en_o
);
  logic       data_rvalid_mem;
  logic [7:0] instr_seq_in, instr_seq_exp, req_seq_exp;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      data_rvalid_mem <= 1'b0;
      instr_seq_in    <= 8'h0;
      req_seq_exp     <= 8'h0;
      instr_seq_exp   <= 8'h0;
    end else begin
      data_rvalid_mem <= data_req_o & data_gnt_i;

      if (us_valid_i & lspl_rdy_o)
        instr_seq_in <= instr_seq_in + 8'h2;

      if (lsu_req & lsu_req_done)
        req_seq_exp <= req_seq_exp + 8'h2;

      if (lspl_valid_o & ds_rdy_i)
        instr_seq_exp <= instr_seq_exp + 8'h2;
    end
  end

  logic mem_not_gnt, lsu_not_done;
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      mem_not_gnt  <= 1'b0;
      lsu_not_done <= 1'b0; 
    end else begin
      if (data_gnt_i)
        mem_not_gnt <= 1'b0;
      else if (data_req_o & ~data_gnt_i)
        mem_not_gnt <= 1'b1;

      if (lsu_req_done)
        lsu_not_done <= 1'b0;
      else if (lsu_req & ~lsu_req_done)
        lsu_not_done <= 1'b1;
    end
  end

  AssumeDataGnt0:   assume property (data_req_o |-> ##[0:1] data_gnt_i);
  //AssumeDataGnt1:   assume property ((~rst_ni|~data_req_o) |-> ~data_gnt_i);
  AssumeDataGnt1:   assume property  (data_gnt_i |-> data_req_o);
  AssumeDataValid:  assume property (data_rvalid_i == data_rvalid_mem);

`ifdef KUDU_FORMAL_G4_0
  //
  // Strong assumption (no errors)
  // handshaking and instruction sequence 
  //assume property (

  AssumeDataErr:    assume property (data_err_i == 1'b0);

  AssumeNoFlush:    assume property (flush_i == 1'b0);
  AssumeNoLatchErr: assume property (load_store_unit_i.lsu_resp_err_o == 1'b0);
  AssumeNormalRq:   assume property (cmplx_lsu_req_valid_i == 1'b0);

  AssumeDsRdy:      assume property (lspl_valid_o |-> ##[0:2] ds_rdy_i);

  // Let's just assume both A&B has the same sequence number. We are not
  // using this to test the ira/b muxing logic
  AssumeInstrSeq:   assume property (instr_dec.pc == {24'h0, instr_seq_in});

  AssertLSUReq: assert property (@(posedge clk_i) 
    ((us_valid_i & lspl_rdy_o) |-> ##[0:3] lsu_req ));

  // somehow this one takes a very long time to run if data grant delay >=2 ??
  AssertLSUReqDone: assert property (@(posedge clk_i) 
    (lsu_req |-> ##[0:8] lsu_req_done ));

  AssertLSUResp: assert property (@(posedge clk_i) 
    (lsu_req_done |-> ##[0:3] lsu_resp_valid ));

  // This checks one-to-one mapping between LS instructions (requests) and results (responses)
  // - use a short sequence number to reduce runtime
  AssertLSInstrSeq: assert property (@(posedge clk_i) 
    ((lspl_valid_o & ds_rdy_i) |-> (lspl_output_o.pc[31:0] == {24'h0, instr_seq_exp}) ));

  AssertLSReqSeq: assert property (@(posedge clk_i) 
    ((lsu_req) |-> (lsu_req_info.pc[31:0] == {24'h0, req_seq_exp}) ));

  // 
  // LSU interface protocol checking
  //

  AssertLsuIf0:  assert property (@(posedge clk_i) 
    ( lsu_not_done |-> $stable(lsu_req) ));
  AssertLsuIf1:  assert property (@(posedge clk_i) 
    ( lsu_not_done |-> $stable(lsu_req_info) ));
  AssertLsuIf2:  assert property (@(posedge clk_i) 
    ( lsu_req_done |-> lsu_req ));

  //
  // WRSV istracked by WAW tracking FIFO design
  // - LS pipeline design is more complicated than alu/mult pipeliens and thus tracking 
  //   an instruction explicitly is harder. However the FIFO behavior is already verified.
  //

`endif

`ifdef KUDU_FORMAL_G4_1
  //
  // Weaker assumptions (include error conditions) 
  //
  //AssumeNoDebug:    assume property (debug_mode_i == 1'b0);
  AssumeNormalRq:   assume property (cmplx_lsu_req_valid_i == 1'b0);

  //
  // Execution-stage error handling
  // - if an execution-time exception (CSR access or load/store error) occurs, all 
  //   subsequent instructions will be cancelled (no CSR write, memory r/w or register
  //   writes), until the exception handler starts execution
  //


  //
  // Load/store/csr Error handling
  //  
  // this runs too long in Jasper..
  // Original form, kept for reference. It is stale and cannot elaborate as written:
  // there is no trap_pending signal, and cs_registers_i is not visible from the
  // ls_pipeline scope. It is restated below with the LSU's own error state
  // (resp_err_latched / lsu_err_active) and the LSU-side CSR enable (csr_op_en_o).
  // AssertTrapPendingAll: assert property (@(posedge clk_i) 
  //   (trap_pending |-> (~cs_registers_i.csr_op_en_i & ~data_req_o) ));

  // once an LSU/CSR error response has been latched (until the flush), no CSR
  // operation and no data memory request is issued (proven in ~2 s)
  AssertTrapPendingAll: assert property (@(posedge clk_i) 
    (resp_err_latched |-> (~csr_op_en_o & ~data_req_o) ));
  // same for the whole error-active window, which includes the error response cycle
  AssertTrapPendingNoReq: assert property (@(posedge clk_i) 
    (lsu_err_active |-> ~data_req_o ));

  AssertLsuTrapLatched: assert property (@(posedge clk_i) 
    ($fell(resp_err_latched) |-> $past(flush_i,1) ));

  AssertLsuTrapPending1: assert property (@(posedge clk_i) 
    (lsu_err_active |-> (~load_store_unit_i.ls_go) ));
  AssertLsuTrapPending2: assert property (@(posedge clk_i) 
    (lsu_err_active |-> (~load_store_unit_i.csr_go) ));

  AssertLsuTrapPending3: assert property (@(posedge clk_i) 
    (flush_i |-> ##[0:1] ~lsu_req ));

  AssertLsuNeverStuck: assert property (@(posedge clk_i) 
    ((load_store_unit_i.ls_fsm_cs != IDLE) |-> ##[0:10]  (load_store_unit_i.ls_fsm_cs == IDLE) ));

  // 
  // memory interface protocol checking
  //
  AssertDataIfProtocol0:  assert property (@(posedge clk_i) 
    ( mem_not_gnt |-> $stable(data_addr_o) ));
  AssertDataIfProtocol1:  assert property (@(posedge clk_i) 
    ( mem_not_gnt |-> $stable(data_req_o) ));

  //WaWFiFo can't overrun (underrun permitted if cmplx request)
  AssertWaWFifoNeverFull: assert property (@(posedge clk_i) 
    (waw_fifo_i.wr_rdy_o));

  // Verify WbFifo won't overrun (write attempt when not ready) due to backpressure to LSU
  // - somehow tryingto prove wbFifo never full takes a very long time when data_gnt deay is 2..
  // No need to assert for WbFiFoUnderrun (part of Assume already)
  AssertWbFifoOverrun: assert property (@(posedge clk_i) 
    (lsu_resp_valid |-> wb_fifo_i.wr_rdy_o));
  AssertWaWFifoUnderrun: assert property (@(posedge clk_i) 
    (lspl_valid_o |-> waw_fifo_i.rd_valid_o ));


`endif


endmodule

////////////////////////////////////////////////////////////////
// Mult Pipeline
////////////////////////////////////////////////////////////////

module mult_pipeline_fv_ext import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; (
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic            cheri_pmode,

  input  logic            flush_i,
  input  logic            us_valid_i,
  input  logic            multpl_rdy_o,
  input  waw_act_t        waw_act_i,
  input  logic [31:0]     fwd_act_o,
  input  pl_fwd_t         fwd_info_o,
  input  logic            ds_rdy_i,
  input  logic            multpl_valid_o,
  input  pl_out_t         multpl_output_o,

  input  ir_dec_t         instr_dec,
  input  full_data2_t     full_data2,
  input  logic            div_sel,
  input  logic            ex2_valid,
  input  logic            wb_rdy,
  input  logic            wb_valid
);

`ifdef KUDU_FORMAL_G5

  //
  // Pipelines shoudl work like FIFO's (guaratee ordering)
  //
  logic [7:0] instr_seq_in, instr_seq_exp;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      instr_seq_in    <= 8'h0;
      instr_seq_exp   <= 8'h0;
    end else begin
      if (us_valid_i & multpl_rdy_o)
        instr_seq_in <= instr_seq_in + 8'h2;

      if (multpl_valid_o & ds_rdy_i)
        instr_seq_exp <= instr_seq_exp + 8'h2;
    end
  end

  AssumeNoFlush:   assume property (flush_i == 1'b0);
  AssumeNoDiv:     assume property ((instr_dec.insn[6:0] == OPCODE_OP) |-> ~instr_dec.insn[14]);
  AssumeInstrSeq:  assume property (instr_dec.pc == {24'h0, instr_seq_in});

  AssertInstrProgress: assert property (@(posedge clk_i) 
    ((us_valid_i & multpl_rdy_o) |-> ##[0:7] multpl_valid_o ));

  AssertMultInstrSeq: assert property (@(posedge clk_i) 
    ((multpl_valid_o & ds_rdy_i) |-> (multpl_output_o.pc == {24'h0, instr_seq_exp}) ));

  //
  // this models the life cycle of a single instruction as it is passed through pipeline stages
  // so we can check things like whether FWD and WRSV are canceled at the right time
  //
  typedef struct packed {
    full_data2_t full_data2;
    ir_dec_t     instr;
    logic        fwd; 
    logic [7:0]  pc; 
    logic [4:0]  rd;
    logic [2:0]  state;   // which pipelime stage the instruction is in
  } instr_tracking_t;

  instr_tracking_t mult_instr;  

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      mult_instr <= '0;
    end else begin
      case (mult_instr.state) 
        0: begin
          if (us_valid_i & multpl_rdy_o)
            mult_instr <= '{full_data2, instr_dec, (instr_dec.rf_we & (instr_dec.rd!=0)), 
                           instr_dec.pc, instr_dec.rd, 3'h1};
        end
        
        1, 2: begin   // in WB stage of MULT pipeline
          if (flush_i) begin 
            mult_instr.state <= 0;
          end else if ((mult_instr.state == 1) & ex2_valid & wb_rdy) begin
            mult_instr.state <= 2;    
          end else if ((mult_instr.state == 2) & wb_valid & ds_rdy_i) begin
            mult_instr.state <= 0;    
          end

          if (flush_i) begin 
            mult_instr.fwd  <= 1'b0;
          end else if ((waw_act_i.valid[0] && (waw_act_i.rd0 == mult_instr.rd)) ||
                       (waw_act_i.valid[1] && (waw_act_i.rd1 == mult_instr.rd))) begin
            mult_instr.fwd  <= 1'b0;
          end
        end
        default: ;
      endcase
    end
  end

  AssertMultFwdOK0: assert property (@(posedge clk_i) 
    ((mult_instr.state == 2) |-> (mult_instr.fwd == fwd_info_o.valid[1]) ));

  AssertMultFwdOK1: assert property (@(posedge clk_i) 
    ((mult_instr.state == 2) |-> (mult_instr.fwd == multpl_output_o.wrsv) ));

  //
  // Check that other than CJALR
  // We can only set the tag bit of Cd if Cs1 tag is set.
  // 

  logic cd_tag_valid, cs1_tag_valid;

  assign cs1_tag_valid = mult_instr.full_data2.d0[REG_TAG];
  assign cd_tag_valid  = (mult_instr.state == 2) && 
                         ~(mult_instr.instr.is_jalr & cheri_pmode)  && 
                         multpl_valid_o && multpl_output_o.we && (multpl_output_o.waddr != 0) &&
                         multpl_output_o.wdata[REG_TAG];

  AssertMultCheriTag0: assert property (@(posedge clk_i) 
    (cd_tag_valid |-> cs1_tag_valid));


  //
  // check fwd_info and fwd_act are consistent
  //

  logic [31:0]     fwd_act_exp;

  always_comb begin
    int i;
    fwd_act_exp = 0;
    for (i = 1; i < 32; i++) begin
      fwd_act_exp[i] = (fwd_info_o.valid[0] && (fwd_info_o.addr0 == i)) ||
                       (fwd_info_o.valid[1] && (fwd_info_o.addr1 == i));
    end
  end

  AssertMultFwdActOk: assert property (@(posedge clk_i) (fwd_act_o == fwd_act_exp));

  //
  // check if the top/base_cor bits in the forwarded op_cap are always consistent with
  // its reg_cap fields
  //

  function automatic logic check_fwd_op (op_cap_t in_ocap);
    logic result;
    op_cap_t tcap;

    if (in_ocap.valid) begin 
      tcap = reg2opcap(in_ocap[RegW-1:0]);
      result = (in_ocap == tcap);
    end else begin
      result = 1'b1;    
    end

    return result;
  endfunction

  full_cap_t ref_cs1_fcap, ref_cs2_fcap;
  assign ref_cs1_fcap = op2fullcap(reg2opcap((full_data2.d0[RegW-1:0])));
  assign ref_cs2_fcap = op2fullcap(reg2opcap((full_data2.d1[RegW-1:0])));


  AssumeCS1CapOK: assume property (ref_cs1_fcap.valid |-> (ref_cs1_fcap == full_data2.d0));
  AssumeCS2CapOK: assume property (ref_cs2_fcap.valid |-> (ref_cs2_fcap == full_data2.d1));

  AssertOpRegsOkMult0: assert property (@(posedge clk_i) 
    (fwd_info_o.valid[1] |-> check_fwd_op(fwd_info_o.data1)) );


`endif
endmodule

////////////////////////////////////////////////////////////////
// ALU Pipeline
////////////////////////////////////////////////////////////////

module alu_pipeline_fv_ext import super_pkg::*; import cheri_pkg::*; (
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic                 flush_i,

  // upstream (issuer) side interface
  input  logic                 us_valid_i,
  input  logic                 alupl_rdy_o,
  input  ir_dec_t              instr_i,
  input  full_data2_t          full_data2_i,
  input  waw_act_t             waw_act_i,

  input  pcc_cap_t             pcc_cap_i,
  input  logic                 csr_mstatus_mie_i,
  input  logic [31:0]          fwd_act_o,
  input  pl_fwd_t              fwd_info_o,
            
  input  logic                 ds_rdy_i,
  input  logic                 alupl_valid_o,
  input  pl_out_t              alupl_output_o,
  input  logic                 wb_valid
);

`ifdef KUDU_FORMAL_G6

  //
  // this models the life cycle of a single instruction as it is passed through pipeline stages
  // so we can check things like whether FWD and WRSV are canceled at the right time
  //
  typedef struct packed {
    full_data2_t      full_data2;
    ir_dec_t          instr;
    logic             fwd; 
    logic [7:0]       pc; 
    logic [4:0]       rd;
    logic [2:0]       state;   // which pipelime stage the instruction is in
  } instr_tracking_t;

  instr_tracking_t alu_instr;  

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      alu_instr <= '0;
    end else begin
      case (alu_instr.state) 
        0: begin
          if (us_valid_i & alupl_rdy_o)
            alu_instr <= '{full_data2_i, instr_i, (instr_i.rf_we & (instr_i.rd!=0)), 
                           instr_i.pc, instr_i.rd, 3'h1};
        end
        1: begin   // in WB stage of ALU pipeline
          if (flush_i) begin 
            alu_instr.state <= 0;
          end else if (wb_valid & ds_rdy_i) begin
            alu_instr.state <= 0;    
          end

          if (flush_i) begin 
            alu_instr.fwd  <= 1'b0;
          end else if ((waw_act_i.valid[0] && (waw_act_i.rd0 == alu_instr.rd)) ||
                       (waw_act_i.valid[1] && (waw_act_i.rd1 == alu_instr.rd))) begin
            alu_instr.fwd  <= 1'b0;
          end
        end
        default: ;
      endcase
    end
  end

  AssertALUFwdOK0: assert property (@(posedge clk_i) 
    ((alu_instr.state == 1) |-> (alu_instr.fwd == fwd_info_o.valid[1]) ));

  AssertALUFwdOK1: assert property (@(posedge clk_i) 
    ((alu_instr.state == 1) |-> (alu_instr.fwd == alupl_output_o.wrsv) ));

  //
  // Check that other than JAL and AUIPCC (where PCC is the operand),
  // We can only set the tag bit of Cd if Cs1 tag is set.
  // 

  logic cd_tag_valid, cs1_tag_valid;

  assign cs1_tag_valid = alu_instr.full_data2.d0[REG_TAG];
  assign cd_tag_valid  = (alu_instr.state == 1) && 
                         ~alu_instr.instr.cheri_op.auipcc && ~alu_instr.instr.is_jal &&
                         alupl_valid_o && alupl_output_o.we && (alupl_output_o.waddr != 0) &&
                         alupl_output_o.wdata[REG_TAG];

  AssertALUCheriTag0: assert property (@(posedge clk_i) 
    (cd_tag_valid |-> cs1_tag_valid) );

  //
  // check fwd_info and fwd_act are consistent
  //

  logic [31:0]     fwd_act_exp;
  always_comb begin
    int i;
    fwd_act_exp = 0;
    for (i = 1; i < 32; i++) begin
      fwd_act_exp[i] = (fwd_info_o.valid[0] && (fwd_info_o.addr0 == i)) ||
                       (fwd_info_o.valid[1] && (fwd_info_o.addr1 == i));
    end
  end

  AssertALUFwdActOk: assert property (@(posedge clk_i) (fwd_act_o == fwd_act_exp));

  //
  // check if the top/base_cor bits in the forwarded op_cap are always consistent with
  // its reg_cap fields
  //

  function automatic logic check_fwd_op (op_cap_t in_ocap);
    logic result;
    op_cap_t tcap;

    if (in_ocap.valid) begin 
      tcap = reg2opcap(in_ocap[RegW-1:0]);
      result = (in_ocap == tcap);
    end else begin
      result = 1'b1;    
    end

    return result;
  endfunction

  full_cap_t ref_cs1_fcap, ref_cs2_fcap;
  assign ref_cs1_fcap = op2fullcap(reg2opcap((full_data2_i.d0[RegW-1:0])));
  assign ref_cs2_fcap = op2fullcap(reg2opcap((full_data2_i.d1[RegW-1:0])));


  AssumeCS1CapOK: assume property (ref_cs1_fcap.valid |-> (ref_cs1_fcap == full_data2_i.d0));
  AssumeCS2CapOK: assume property (ref_cs2_fcap.valid |-> (ref_cs2_fcap == full_data2_i.d1));

  AssertOpRegsOkALU0: assert property (@(posedge clk_i) 
    (fwd_info_o.valid[1] |-> check_fwd_op(fwd_info_o.data1)) );

`endif
endmodule

////////////////////////////////////////////////////////////////
// Dcache 
////////////////////////////////////////////////////////////////

module dcache_fv_ext import super_pkg::*; (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  logic [3:0]     update_valid, 
  input  logic [3:0]     update_invalid
);

`ifdef KUDU_FORMAL_G7
  AssertUpdateLegal: assert property (@(posedge clk_i) ((update_valid & update_invalid) == 4'h0));

`endif
endmodule

////////////////////////////////////////////////////////////////
// kudu_top
////////////////////////////////////////////////////////////////

module kudu_top_fv_ext import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  logic           cheri_pmode_i,
  input  logic [31:0]    boot_addr_i,
  input  logic           instr_req_o,
  input  logic           instr_gnt_i,
  input  logic [31:0]    instr_addr_o,
  input  logic [63:0]    instr_rdata_i,
  input  logic           instr_err_i,
  input  logic           instr_rvalid_i,
  input  logic           data_req_o,
  input  logic           data_gnt_i,
  input  logic           data_rvalid_i,
  input  logic           data_err_i,
  input  logic           cmt_err,
  input  logic           cmt_flush,
  input  logic           cmt_lspl_rdy,
  input  logic           lspl_valid,
  input  pl_out_t        lspl_output,
  input  logic           csr_restore_mret,
  input  logic           csr_save_cause,                
  input  logic           ex1_cjalr_pcc_set,
  input  logic           ex_pc_set,
  input  logic [1:0]     sbdfifo_rd_valid,
  input  pcc_cap_t       ex1_pcc_cap,
  input  pcc_cap_t       ir_pcc_cap,
  input  pl_fwd_t        alupl0_fwd_info,
  input  pl_fwd_t        alupl1_fwd_info,
  input  pl_fwd_t        lspl_fwd_info,
  input  pl_fwd_t        multpl_fwd_info,
  input  logic [31:0]    alupl0_fwd_act,
  input  logic [31:0]    alupl1_fwd_act,
  input  logic [31:0]    lspl_fwd_act,
  input  logic [31:0]    multpl_fwd_act,
  input  logic [1:0]     ir_valid,
  input  logic           lspl_rdy,
  input  logic           cmplx_instr_start
);


  AssumeKTopCfgCheriMode:   assume property (cheri_pmode_i == 1'b1);
  AssumeKTopCfgBootAddr:    assume property (boot_addr_i == 32'h8000_0000);

`ifdef KUDU_FORMAL_G0_0
  defparam if_stage_i.AltEnable = 1'b0;
  `define KUDU_TOP_ASSUMPTIONS
`endif 

`ifdef KUDU_FORMAL_G0_1
  defparam if_stage_i.AltEnable = 1'b0;
  `define KUDU_TOP_ASSUMPTIONS
`endif 

`ifdef KUDU_TOP_ASSUMPTIONS
  //
  // Data memory inteface handshaking and sequence
  //
  logic       data_rvalid_mem, instr_rvalid_mem;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      instr_rvalid_mem <= 1'b0;
      data_rvalid_mem  <= 1'b0;
    end else begin
      instr_rvalid_mem <= instr_req_o & instr_gnt_i;
      data_rvalid_mem  <= data_req_o & data_gnt_i;
    end
  end

  AssumeDataGnt0:   assume property (data_req_o |-> ##[0:1] data_gnt_i);
  AssumeDataGnt1:   assume property ((~rst_ni|~data_req_o) |-> ~data_gnt_i);
  AssumeDataValid:  assume property (data_rvalid_i == data_rvalid_mem);
  // AssumeDataErr:    assume property (data_err_i == 1'b0);
 
  AssumeInstrGnt0:  assume property (instr_req_o |-> ##[0:3] instr_gnt_i);
  AssumeInstrGnt1:  assume property ((~rst_ni | ~instr_req_o) |-> ~instr_gnt_i);
  AssumeInstrValid: assume property (instr_rvalid_i == instr_rvalid_mem);
  //AssumeInstrErr:   assume property (instr_err_i == 1'b0);
`endif
 
`ifdef KUDU_FORMAL_G0_0
  // 
  //  Register pre-loading logic in IR stage
  //  This should be eqivalent to read regfile combinatorially in Issuer stage
  //
  ir_dec_t         ira_dec, irb_dec;
  logic            ira_valid, irb_valid;
  logic            ira_rs1_valid, ira_rs2_valid;
  logic            irb_rs1_valid, irb_rs2_valid;

  logic [RegW-1:0] ira_rs1_rdata, ira_rs2_rdata;
  logic [RegW-1:0] irb_rs1_rdata, irb_rs2_rdata;

  logic [RegW-1:0] rf_ira_rs1_val, rf_ira_rs2_val;
  logic [RegW-1:0] rf_irb_rs1_val, rf_irb_rs2_val;

  logic            ira_is0;

  assign ira_is0 = ir_stage_i.ira_is0_o;
  assign ira_dec = ir_stage_i.ira_dec_o;
  assign irb_dec = ir_stage_i.irb_dec_o;

  assign ira_valid = ira_is0 ? ir_stage_i.ir_valid_o[0] : ir_stage_i.ir_valid_o[1];
  assign irb_valid = ira_is0 ? ir_stage_i.ir_valid_o[1] : ir_stage_i.ir_valid_o[0];

  assign ira_rs1_valid = ira_valid & ira_dec.rf_ren[0];
  assign ira_rs2_valid = ira_valid & ira_dec.rf_ren[1];
  assign irb_rs1_valid = irb_valid & irb_dec.rf_ren[0];
  assign irb_rs2_valid = irb_valid & irb_dec.rf_ren[1];

  assign ira_rs1_rdata = ir_stage_i.ira_rf_rdata2_q.d0; 
  assign ira_rs2_rdata = ir_stage_i.ira_rf_rdata2_q.d1; 
  assign irb_rs1_rdata = ir_stage_i.irb_rf_rdata2_q.d0; 
  assign irb_rs2_rdata = ir_stage_i.irb_rf_rdata2_q.d1; 

  assign rf_ira_rs1_val = (ira_dec.rs1 == 0) ? 0 : regfile_i.rf_reg_q[ira_dec.rs1];
  assign rf_ira_rs2_val = (ira_dec.rs2 == 0) ? 0 : regfile_i.rf_reg_q[ira_dec.rs2];
  assign rf_irb_rs1_val = (irb_dec.rs1 == 0) ? 0 : regfile_i.rf_reg_q[irb_dec.rs1];
  assign rf_irb_rs2_val = (irb_dec.rs2 == 0) ? 0 : regfile_i.rf_reg_q[irb_dec.rs2];

  AssertIraRs1Rdata: assert property (@(posedge clk_i) 
    (ira_rs1_valid |-> (ira_rs1_rdata == rf_ira_rs1_val) ));
  AssertIraRs2Rdata: assert property (@(posedge clk_i) 
    (ira_rs2_valid |-> (ira_rs2_rdata == rf_ira_rs2_val) ));

  AssertIrbRs1Rdata: assert property (@(posedge clk_i) 
    (irb_rs1_valid |-> (irb_rs1_rdata == rf_irb_rs1_val) ));
  AssertIrbRs2Rdata: assert property (@(posedge clk_i) 
    (irb_rs2_valid |-> (irb_rs2_rdata == rf_irb_rs2_val) ));
  
  //
  // Error handling
  //
  AssertErrMustFlush0: assert property (@(posedge clk_i) 
    ((lspl_valid & lspl_output.err & cmt_lspl_rdy) |-> ##[0:2] cmt_err ));

  AssertErrMustFlush1: assert property (@(posedge clk_i) 
    (cmt_err |-> ##[0:3] cmt_flush));

  //
  // Basic CHERIoT PCC checks
  //

  // All instructions in EX stages must be flushed when PCC changes 
  logic pcc_change_exc, pcc_change_cjalr, pcc_change_other;
  assign pcc_change_exc   = csr_save_cause | csr_restore_mret;
  assign pcc_change_cjalr = ex1_cjalr_pcc_set;

  AssertPccChangeEXC0: assert property (@(posedge clk_i) 
    (pcc_change_exc |-> ((sbdfifo_rd_valid == 2'b00) || cmt_flush) ));

  // When pcc changes, the cheri fetch checks should be done after change (based on new PCC)
  AssertPccChangeEXC1: assert property (@(posedge clk_i) 
    (pcc_change_exc |-> (ir_stage_i.gen_stage1.s1_fifo.wr_hold_i || ir_stage_i.gen_stage1.s1_fifo.flush_i) ));


`endif

`ifdef KUDU_FORMAL_G0_Long
  // Runtime is too long..

  // 
  // Each register can only be active (forwarding) in at most 1 EX pipelines 
  //
  logic [3:0] reg1_fwd_active = {multpl_fwd_act[1], lspl_fwd_act[1], alupl1_fwd_act[1], alupl0_fwd_act[1]};

  // prove one register is good enough (all registers are identical for this purpose)
  // QQQ this reaches only 33 cycles after running overnight
  // Now proven in ~1 min with the fv_long_help_fwdact lemmas: a ghost register records the
  // EX pipeline of the latest issued x1 writer, and each pipeline's x1 claim implies it is that one.
  AssertFwdActOK1: assert property (@(posedge clk_i) $onehot0(reg1_fwd_active));

  //
  // Cheriot PCC checks
  //

  pcc_cap_t s1_m_rd_data0, s1_m_rd_data1;
  logic [1:0] s1_m_rd_valid, s1_m_rd_rdy;

  assign s1_m_rd_rdy = ir_stage_i.ds_rdy_i;

    
  // mirroring the stage_fifo in RTL
  stage_fifo # (.Width(PccCapW), .PeekMem(0)) s1_fifo_mirror (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .flush_i    (ir_stage_i.ir_flush_i),
      .wr_hold_i  (ir_stage_i.ir_hold_i),
      .wr_valid_i (ir_stage_i.s1_wr_valid),
      .wr_data0_i (ir_pcc_cap),  
      .wr_data1_i (ir_pcc_cap), 
      .wr_rdy_o   (), 
      .rd_rdy_i   (s1_m_rd_rdy),
      .rd_valid_o (s1_m_rd_valid),
      .rd_data0_o (s1_m_rd_data0),
      .rd_data1_o (s1_m_rd_data1),
      .mema_is0_o (),
      .wr_mema_o  (),
      .wr_memb_o  (),
      .wr_ptr_o   (),
      .mema_o     (),
      .memb_o     ()
    );

  op_cap_t fwd_alu0_ocap, fwd_alu1_ocap;
  op_cap_t fwd_mult_ocap, fwd_ls_ocap;
  assign fwd_alu0_ocap = reg2opcap(alupl0_fwd_info.data1[RegW-1:0]);
  assign fwd_alu1_ocap = reg2opcap(alupl1_fwd_info.data1[RegW-1:0]);
  assign fwd_ls_ocap   = reg2opcap(lspl_fwd_info.data1[RegW-1:0]);
  assign fwd_mult_ocap = reg2opcap(multpl_fwd_info.data1[RegW-1:0]);

  // AssumeFwdCapOK0: assume property (fwd_alu0_ocap == alupl0_fwd_info.data1);
  // AssumeFwdCapOK1: assume property (fwd_alu1_ocap == alupl1_fwd_info.data1);
  // AssumeFwdCapOK2: assume property (fwd_ls_ocap   == lspl_fwd_info.data1);
  // AssumeFwdCapOK3: assume property (fwd_mult_ocap == multpl_fwd_info.data1);
  
  // predicted PCC (used for fetched instruction checking) equals to actual EX PCC
  // QQQ this reaches only 14 cycles after running overnight
  AssertPccCorrect0: assert property (@(posedge clk_i) 
    (s1_m_rd_valid[0] && (s1_m_rd_data0 != ex1_pcc_cap)) |-> 
    (issuer_i.mispredict[0] | issuer_i.handle_special) );
  //  ((s1_m_rd_valid[0] & s1_m_rd_rdy[0]) |-> (s1_m_rd_data0 == ex1_pcc_cap)) );
  
  //
  // ir0_nxt_pc_q tracks the next pc for ir0, used to update mepc if an interrupt occurs
  // and ir_valid[0] == 0
  // QQQ this reaches only 18 cycles after an overnight run
  AssertIR0PC: assert property (@(posedge clk_i) 
    (ir_valid[0] |-> (issuer_i.ir0_nxt_pc_q[31:1] == issuer_i.ir0_dec.pc[31:1])));
 
  // complex instruction is issue_special which wait for all previous instruciton commit.
  // therefor ls_pipeline must be ready
  // However it took too long for FV to prove it directly, so we try use sbd_fifo empty us instead
  // of using cmplx_instr_start 
  // AssertCmplxLSRdy: assert property (@(posedge clk_i) (cmplx_instr_start |-> lspl_rdy));
  // Both forms now prove in seconds with the fv_long_help_cmplx lemmas (scoreboard
  // per-pipeline counts == in-flight counts); the original intent is restored as
  // AssertCmplxStartLSRdy.
  AssertCmplxLSRdy: assert property (@(posedge clk_i) (~sbdfifo_rd_valid[0] |-> lspl_rdy));
  AssertCmplxStartLSRdy: assert property (@(posedge clk_i) (cmplx_instr_start |-> lspl_rdy));

`endif

endmodule

////////////////////////////////////////////////////////////////
// G0_Long helper lemmas (bound into kudu_top from bindfiles)
// The G0_Long targets do not prove directly in reasonable time. Each helper
// below is inductive given the earlier ones and proves in seconds. Use
// run_fv_long (fv_kudu.tcl): it proves the helpers in dependency order, assumes
// each proven one, then proves the targets (~5 min for the whole group).
////////////////////////////////////////////////////////////////
`ifdef KUDU_FORMAL_G0_Long

// Helper lemmas for AssertCmplxLSRdy / AssertCmplxStartLSRdy (G0_Long).
// Per EX pipeline X (pl bit 1 alu0, 2 alu1, 3 ls, 4 mult), the number of scoreboard
// entries targeting X equals the number of instructions in flight in X (AssertHbCnt).
// With the scoreboard empty the LS pipeline holds nothing, so lsu_if is ready.
module fv_long_help_cmplx import super_pkg::*; (
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

  // LSU busy (waiting for grant) implies lsu_if still holds the same request in its hold register
  logic lsu_busy_hold_ok;
  assign lsu_busy_hold_ok = (kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs == IDLE) ||
      (hold_e && kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q &&
       (kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.pc[31:0] ==
        kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q.pc[31:0]));

  for (genvar x = 1; x < 5; x++) begin : g_pl
    // number of scoreboard entries targeting pipeline x == number of instructions in flight in x
    // (the LS count is only inductive together with lsu_busy_hold_ok, so the two are proven jointly)
    if (x == 3) begin : g_ls
      AssertHbCnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
        (plcnt[x] == seq_cnt[x]) && lsu_busy_hold_ok);
    end else begin : g_nls
      AssertHbCnt: assert property (@(posedge clk_i) disable iff (!rst_ni)
        plcnt[x] == seq_cnt[x]);
    end
  end

  // scoreboard head valid iff the scoreboard holds at least one entry
  AssertHxSbdValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.sbdfifo_rd_valid[0] == (sbd_cnt != 4'h0));

  // lsu_if not ready only while it holds an issued request (DLY0_WGNT / DLY1_WGNT)
  AssertHxLsNotRdyHold: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !kudu_top.lspl_rdy |-> hold_e);

  // (the target forms AssertCmplxLSRdy / AssertCmplxStartLSRdy are in kudu_top_fv_ext)

endmodule

// Helper lemmas for AssertFwdActOK1 (G0_Long): x1 forwarding active in at most one EX pipeline.
// Ghost lw_q = ex-pipeline selection (pl_sel[4:1]) of the most recently issued x1 writer
// (updated exactly on issuer waw_act_o events with rd==1). Each pipeline claim implies lw_q
// points at that pipeline, so at most one pipeline can claim x1.

module fv_long_help_fwdact import super_pkg::*; (
  input logic clk_i,
  input logic rst_ni
);

  // ---------------- ghost: pipeline of latest issued x1 writer ----------------
  logic [3:0] lw_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni)
      lw_q <= 4'h0;
    else if (issuer_i.waw_act_o.valid[1] && (issuer_i.waw_act_o.rd1 == 5'd1))
      lw_q <= issuer_i.ir1_pl_sel[4:1];
    else if (issuer_i.waw_act_o.valid[0] && (issuer_i.waw_act_o.rd0 == 5'd1))
      lw_q <= issuer_i.ir0_pl_sel[4:1];
  end

  // ---------------- per pipeline claims ----------------
  logic alu0_wb_c, alu1_wb_c, mul_ex2_c, mul_wb_c, ls_fwd_c;
  assign alu0_wb_c = alu_pipeline0_i.wb_fwd_valid_q && (alu_pipeline0_i.wb_reg.rd == 5'd1);
  assign alu1_wb_c = alu_pipeline1_i.wb_fwd_valid_q && (alu_pipeline1_i.wb_reg.rd == 5'd1);
  assign mul_ex2_c = mult_pipeline_i.ex2_valid && mult_pipeline_i.ex2_fwd_ok && 
                     mult_pipeline_i.ex2_reg.rf_we && (mult_pipeline_i.ex2_reg.rd == 5'd1);
  assign mul_wb_c  = mult_pipeline_i.wb_fwd_valid_q && (mult_pipeline_i.wb_reg.rd == 5'd1);
  assign ls_fwd_c  = ls_pipeline_i.fwd_info_o.valid[1] && (ls_pipeline_i.fwd_info_o.addr1 == 5'd1);

  // fwd_act_o[1] flop equals the registered fwd valid/rd pair
  AssertHfaAlu0Eq: assert property (@(posedge clk_i) alu_pipeline0_i.fwd_act_o[1] == alu0_wb_c);
  AssertHfaAlu1Eq: assert property (@(posedge clk_i) alu_pipeline1_i.fwd_act_o[1] == alu1_wb_c);
  AssertHfaMulEq:  assert property (@(posedge clk_i) mult_pipeline_i.fwd_act_o[1] == mul_wb_c);

  // decoded instructions in IR have rd==0 unless rf_we (IbexCmpt decoder)
  AssertHfaIraRdWe: assert property (@(posedge clk_i) (ir_stage_i.ira_dec_o.rd != 0) |-> ir_stage_i.ira_dec_o.rf_we);
  AssertHfaIrbRdWe: assert property (@(posedge clk_i) (ir_stage_i.irb_dec_o.rd != 0) |-> ir_stage_i.irb_dec_o.rf_we);

  // complex-unit LSU requests never coincide with a normal LS issue
  AssertHfaCmplxNoLs: assert property (@(posedge clk_i) comlx_unit_i.cmplx_lsu_req_valid_o |-> ~issuer_i.ex_valid_o[3]);

  // ALU / MULT claims
  AssertHfaAlu0Claim:  assert property (@(posedge clk_i) alu0_wb_c |-> (lw_q == 4'b0001));
  AssertHfaAlu1Claim:  assert property (@(posedge clk_i) alu1_wb_c |-> (lw_q == 4'b0010));
  AssertHfaMulEx2Claim: assert property (@(posedge clk_i) mul_ex2_c |-> (lw_q == 4'b1000));
  AssertHfaMulWbClaim:  assert property (@(posedge clk_i) mul_wb_c  |-> (lw_q == 4'b1000));

  // ---------------- LS pipeline: lsu_if <-> dcache waw fifo correspondence ----------------
  logic [2:0] lsif_fsm;
  logic       dly_v, hold_v;
  logic [2:0] dc_cnt;
  logic [1:0] dc_rp;
  lsu_req_info_t req_dly, req_hold;

  assign lsif_fsm = ls_pipeline_i.lsu_if_i.lsif_fsm_q;
  assign req_dly  = ls_pipeline_i.lsu_if_i.req_dly_q;
  assign req_hold = ls_pipeline_i.lsu_if_i.req_hold_q;
  assign dly_v    = ((lsif_fsm == 3'h2) || (lsif_fsm == 3'h3)) && ls_pipeline_i.lsu_if_i.req_dly_valid &&
                    (req_dly.amo_flag[3:2] == 2'b00);
  assign hold_v   = ((lsif_fsm == 3'h1) || (lsif_fsm == 3'h3)) && (req_hold.amo_flag[3:2] == 2'b00);
  assign dc_cnt   = ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.wr_ptr_q - ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q;
  assign dc_rp    = ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q[1:0];

  AssertHfaLsCnt:   assert property (@(posedge clk_i) dc_cnt == (3'(dly_v) + 3'(hold_v)));
  AssertHfaLsHold:  assert property (@(posedge clk_i) hold_v |-> 
    (ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[dc_rp][4:0] == req_hold.rd));
  AssertHfaLsDly0:  assert property (@(posedge clk_i) (dly_v & ~hold_v) |-> 
    (ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[dc_rp][4:0] == req_dly.rd));
  AssertHfaLsDly1:  assert property (@(posedge clk_i) (dly_v & hold_v) |-> 
    (ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[2'(dc_rp+1)][4:0] == req_dly.rd));

  // normal LSU request matches dcache waw fifo head
  AssertHfaLsReqHead: assert property (@(posedge clk_i) 
    (ls_pipeline_i.lsu_req && (ls_pipeline_i.lsu_req_info.amo_flag[3:2] == 2'b00)) |-> 
    (ls_pipeline_i.genblk1.dcache_i.waw_fifo_rd_valid && 
     (ls_pipeline_i.genblk1.dcache_i.waw_fifo_rdata[4:0] == ls_pipeline_i.lsu_req_info.rd)));

  // dcache waw fifo entries not cancelled with rd==1 belong to the latest x1 writer
  for (genvar i = 0; i < 4; i++) begin : gen_ent
    AssertHfaLsEntClaim: assert property (@(posedge clk_i) 
      (ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[i] == 6'h21) |-> (lw_q == 4'b0100));
  end

  // LS forwarding claim
  AssertHfaLsFwdClaim: assert property (@(posedge clk_i) ls_fwd_c |-> (lw_q == 4'b0100));

  // non-vacuity covers
  CoverHfaAlu0:  cover property (@(posedge clk_i) alu0_wb_c);
  CoverHfaMulEx2: cover property (@(posedge clk_i) mul_ex2_c);
  CoverHfaMulWb: cover property (@(posedge clk_i) mul_wb_c);
  CoverHfaLsEnt: cover property (@(posedge clk_i) ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[1] == 6'h21);
  CoverHfaLsFwd: cover property (@(posedge clk_i) ls_fwd_c);
  CoverHfaLsFwdAlu: cover property (@(posedge clk_i) ls_fwd_c ##1 alu0_wb_c);

endmodule

// Helper lemmas for AssertIR0PC / AssertPccCorrect0 (G0_Long).
// Key invariants: AssertHpcChainAll (pc continuity fetch -> s0 -> s1 -> ir0_nxt_pc_q)
// and AssertHpcPccAll (s1/IR predicted PCC chain, oldest in flight == ex1_pcc_cap).
// Each helper is inductive given the earlier lemmas of the proof order.
module fv_long_help_pcc import super_pkg::*; import cheri_pkg::*; (input logic clk_i, input logic rst_ni);

  function automatic logic [31:0] succ0(ir_reg_t e);
    return e.ptaken ? e.ptarget : (e.pc + (e.is_comp ? 32'd2 : 32'd4));
  endfunction
  function automatic logic [31:0] succ1(ir_dec_t d);
    return d.ptaken ? d.ptarget[31:0] : d.pc_nxt;
  endfunction
  function automatic logic unk1(ir_dec_t d);
    return d.is_jalr && !d.ptaken;
  endfunction

  // ---------------- state taps
  logic [31:0] nxt;
  assign nxt = kudu_top.issuer_i.ir0_nxt_pc_q;

  ir_reg_t     s0m [4];
  logic [2:0]  s0_rp, s0_wp, s0_cnt;
  ir_reg_t     s0e [4];
  for (genvar i = 0; i < 4; i++) begin : g_s0
    assign s0m[i] = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.fifo_mem[i];
  end
  assign s0_rp  = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.rd_ptr_q;
  assign s0_wp  = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.wr_ptr_q;
  assign s0_cnt = s0_wp - s0_rp;
  for (genvar j = 0; j < 4; j++) begin : g_s0e
    logic [1:0] ix;
    assign ix = s0_rp[1:0] + 2'(j);
    assign s0e[j] = s0m[ix];
  end
  logic [1:0] s0_fill, s0_room;
  assign s0_fill = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.fill_status_q;
  assign s0_room = kudu_top.ir_stage_i.gen_stage0_buffer.s0_fifo.room_status_q;

  ir_dec_t     s1m [2];
  logic        s1_rp, s1_wp, s1_full;
  logic [1:0]  s1_cnt;
  ir_dec_t     s1e0, s1e1, s1t;
  assign s1m[0]  = kudu_top.ir_stage_i.gen_stage1.s1_fifo.fifo_mem[0];
  assign s1m[1]  = kudu_top.ir_stage_i.gen_stage1.s1_fifo.fifo_mem[1];
  assign s1_rp   = kudu_top.ir_stage_i.gen_stage1.s1_fifo.rd_ptr_q;
  assign s1_wp   = kudu_top.ir_stage_i.gen_stage1.s1_fifo.wr_ptr_q;
  assign s1_full = kudu_top.ir_stage_i.gen_stage1.s1_fifo.full_stat_q;
  assign s1_cnt  = s1_full ? 2'd2 : (s1_wp != s1_rp) ? 2'd1 : 2'd0;
  assign s1e0    = s1m[s1_rp];
  assign s1e1    = s1m[~s1_rp];
  assign s1t     = (s1_cnt == 2'd2) ? s1e1 : s1e0;

  ir_reg_t     s0last;
  assign s0last = s0e[2'(s0_cnt - 3'd1)];

  logic [31:0] if_pc;
  assign if_pc = {kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addr_q, 1'b0};

  // issuer still in RESET/BOOT_SET (before the first pc_set)
  logic boot;
  assign boot = kudu_top.issuer_i.ctrl_fsm_cs[CSM_RESET] | kudu_top.issuer_i.ctrl_fsm_cs[CSM_BOOT_SET];

  // ---------------- structural FIFO invariants
  // s0 dual_fifo: count bounded and fill/room status flags agree with the pointers
  AssertHpcS0Status: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s0_cnt <= 3'd4) && (s0_fill[0] == (s0_cnt > 0)) && (s0_fill[1] == (s0_cnt > 1)) &&
    (s0_room[0] == (s0_cnt < 4)) && (s0_room[1] == (s0_cnt < 3)));
  // s1 stage_fifo: full implies equal pointers
  AssertHpcS1Full: assert property (@(posedge clk_i) disable iff (!rst_ni) s1_full |-> (s1_wp == s1_rp));
  // fetch fifo precomputed address increments (or still at reset value)
  AssertHpcIfAddrP: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addrp2_q == kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addr_q + 31'd1) &&
     (kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addrp4_q == kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addr_q + 31'd2)) ||
    ((kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addr_q == '0) && (kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addrp2_q == '0) &&
     (kudu_top.if_stage_i.prefetch_buffer_i.fifo_i.instr_addrp4_q == '0) && boot));

  // ptaken in s1 only on control transfer instructions
  AssertHpcS1PtakenCti0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt != 0) && s1e0.ptaken |-> (s1e0.is_branch | s1e0.is_jal | s1e0.is_jalr));
  AssertHpcS1PtakenCti1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt == 2) && s1e1.ptaken |-> (s1e1.is_branch | s1e1.is_jal | s1e1.is_jalr));

  // ---------------- PC chain (IF -> s0 -> s1 -> ir0_nxt_pc_q)
  function automatic logic eqh(logic [31:0] a, logic [31:0] b);
    return a[31:1] == b[31:1];
  endfunction
  logic chain_ok;
  always_comb begin
    chain_ok = 1'b1;
    if (!boot) begin
    if (s1_cnt != 0) chain_ok &= (s1e0.pc_nxt == s1e0.pc + (s1e0.is_comp ? 32'd2 : 32'd4)) && eqh(s1e0.pc, nxt);
    if (s1_cnt == 2) chain_ok &= (s1e1.pc_nxt == s1e1.pc + (s1e1.is_comp ? 32'd2 : 32'd4));
    if ((s1_cnt == 2) && !unk1(s1e0)) chain_ok &= eqh(s1e1.pc, succ1(s1e0));
    if ((s0_cnt != 0) && !((s1_cnt != 0) && unk1(s1t)))
      chain_ok &= eqh(s0e[0].pc, ((s1_cnt == 0) ? nxt : succ1(s1t)));
    for (int j = 1; j < 4; j++) if (s0_cnt > j) chain_ok &= eqh(s0e[j].pc, succ0(s0e[j-1]));
    if (!((s0_cnt == 0) && (s1_cnt != 0) && unk1(s1t)))
      chain_ok &= eqh(if_pc, ((s0_cnt != 0) ? succ0(s0last) : (s1_cnt != 0) ? succ1(s1t) : nxt));
    end
  end
  // issuer control FSM is one-hot
  AssertHpcFsmOH: assert property (@(posedge clk_i) disable iff (!rst_ni) $onehot(kudu_top.issuer_i.ctrl_fsm_cs));
  // nothing in the IR stage before boot
  AssertHpcBootEmpty: assert property (@(posedge clk_i) disable iff (!rst_ni) boot |-> (s1_cnt == 0) && (s0_cnt == 0));
  // the whole chain (inductive as a conjunction)
  AssertHpcChainAll: assert property (@(posedge clk_i) disable iff (!rst_ni) chain_ok);

  // ---------------- issuer special cases
  // special issue of an instruction always has a valid IR0
  AssertHpcSpecValid: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] &&
    (kudu_top.issuer_i.special_case_q inside {EXEC, SYSCTL, CMPLX, STEP}) |-> kudu_top.issuer_i.ir_valid_i[0]);
  // single-step of a revoked-prediction jalr always redirects
  AssertHpcStepUnk: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) &&
    unk1(kudu_top.issuer_i.ir0_dec) |-> kudu_top.issuer_i.special_setpc_q);


  // special-issued CMPLX / SYSCTL instruction in IR0 is really that kind of instruction (not a CTI)
  AssertHpcSpecCase: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] |->
    (((kudu_top.issuer_i.special_case_q == CMPLX)  -> kudu_top.issuer_i.ir0_dec.is_cmplx) &&
     ((kudu_top.issuer_i.special_case_q == SYSCTL) -> kudu_top.issuer_i.ir0_dec.sysctl.valid)));
  // decoded instruction classes in valid s1 entries are mutually exclusive (all opcode based)
  function automatic logic excl(ir_dec_t d);
    return $onehot0({d.is_branch, d.is_jal, d.is_jalr, d.sysctl.valid, d.is_cmplx});
  endfunction
  AssertHpcS1Excl0: assert property (@(posedge clk_i) disable iff (!rst_ni) (s1_cnt != 0) |-> excl(s1e0));
  AssertHpcS1Excl1: assert property (@(posedge clk_i) disable iff (!rst_ni) (s1_cnt == 2) |-> excl(s1e1));

  // decoded JALR in s1 always carries pl_type PL_JALR (so it is dispatched to mult/branch)
  AssertHpcS1Pl0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt != 0) && s1e0.is_jalr |-> (s1e0.pl_type == PL_JALR));
  AssertHpcS1Pl1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (s1_cnt == 2) && s1e1.is_jalr |-> (s1e1.pl_type == PL_JALR));
  // special cases that change CSR context also redirect the pc (and so flush IR)
  AssertHpcSpecSetpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    ((kudu_top.issuer_i.special_case_q inside {DEBUG, EXEC, IRQ}) ||
     ((kudu_top.issuer_i.special_case_q == SYSCTL) &&
      (kudu_top.issuer_i.sysctl_q.ebrk | kudu_top.issuer_i.sysctl_q.ecall |
       kudu_top.issuer_i.sysctl_q.mret | kudu_top.issuer_i.sysctl_q.dret))) |-> kudu_top.issuer_i.special_setpc_q);
  // any PCC reload from CSR (trap/mret/dret) coincides with an IR flush
  AssertHpcExcSetpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.cs_registers_i.gen_scr.exc_flag |-> kudu_top.issuer_i.pc_set_o);
  // ---------------- PCC (AssertPccCorrect0)
  // s1 entry is a CJALR whose RA prediction was confirmed at s1 write (ptarget := cur_ra)
  function automatic logic pok(ir_dec_t d);
    return d.is_jalr && d.ptaken;
  endfunction
  // PCC predicted at IR for such an entry (same expression as cs_registers ir_cjalr_pcap)
  function automatic pcc_cap_t pred(ir_dec_t d);
    return full2pcap(op2fullcap(reg2opcap(unseal_rcap(reg_cap_t'(d.ptarget[RegW-1:0])))));
  endfunction

  pcc_cap_t m0, m1, mt, ex1_pcc, ir_pcc;
  assign m0      = kudu_top.kudo_top_fv_ext_i.s1_fifo_mirror.fifo_mem[s1_rp];
  assign m1      = kudu_top.kudo_top_fv_ext_i.s1_fifo_mirror.fifo_mem[~s1_rp];
  assign mt      = (s1_cnt == 2'd2) ? m1 : m0;
  assign ex1_pcc = kudu_top.cs_registers_i.ex1_pcc_cap_q;
  assign ir_pcc  = kudu_top.cs_registers_i.ir_pcc_cap_q;
  logic  esc;   // single-step pending outside debug mode: target is vacuous (handle_step)
  assign esc     = kudu_top.issuer_i.debug_step_i & ~kudu_top.issuer_i.debug_mode_q;

  // single-step special issue only happens outside debug mode with dcsr.step set
  AssertHpcStepEsc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (kudu_top.issuer_i.special_case_q == STEP) |-> esc);
  // mirror fifo pointers in lockstep with the RTL s1 fifo
  AssertHpcPLock: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.kudo_top_fv_ext_i.s1_fifo_mirror.wr_ptr_q == s1_wp) &&
    (kudu_top.kudo_top_fv_ext_i.s1_fifo_mirror.rd_ptr_q == s1_rp) &&
    (kudu_top.kudo_top_fv_ext_i.s1_fifo_mirror.full_stat_q == s1_full));

  // canonical op cap: correction bits are those recomputed from the register-format bits
  function automatic logic canon(op_cap_t c);
    return c == reg2opcap(c[RegW-1:0]);
  endfunction
  // forwarded WB data of every EX pipeline is a canonical op cap
  AssertHpcFwdCanonA0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.alupl0_fwd_info.valid[1] |-> canon(kudu_top.alupl0_fwd_info.data1));
  AssertHpcFwdCanonA1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.alupl1_fwd_info.valid[1] |-> canon(kudu_top.alupl1_fwd_info.data1));
  AssertHpcFwdCanonLS: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.lspl_fwd_info.valid[1] |-> canon(kudu_top.lspl_fwd_info.data1));
  AssertHpcFwdCanonM: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.multpl_fwd_info.valid[1] |-> canon(kudu_top.multpl_fwd_info.data1));
  // at most one forwarding source matches any register (generalises AssertFwdActOK1 to every
  // register and both forwarding stages; proven from AssertHpcFwdLiveAll)
  logic fwd_oh;
  always_comb begin
    fwd_oh = 1'b1;
    for (int r = 1; r < 32; r++) begin
      logic [7:0] mt8;
      mt8 = {kudu_top.alupl0_fwd_info.valid[0] && (kudu_top.alupl0_fwd_info.addr0 == r),
             kudu_top.alupl0_fwd_info.valid[1] && (kudu_top.alupl0_fwd_info.addr1 == r),
             kudu_top.alupl1_fwd_info.valid[0] && (kudu_top.alupl1_fwd_info.addr0 == r),
             kudu_top.alupl1_fwd_info.valid[1] && (kudu_top.alupl1_fwd_info.addr1 == r),
             kudu_top.lspl_fwd_info.valid[0]   && (kudu_top.lspl_fwd_info.addr0 == r),
             kudu_top.lspl_fwd_info.valid[1]   && (kudu_top.lspl_fwd_info.addr1 == r),
             kudu_top.multpl_fwd_info.valid[0] && (kudu_top.multpl_fwd_info.addr0 == r),
             kudu_top.multpl_fwd_info.valid[1] && (kudu_top.multpl_fwd_info.addr1 == r)};
      if (!$onehot0(mt8)) fwd_oh = 1'b0;
    end
  end
  AssertHpcFwdOH: assert property (@(posedge clk_i) disable iff (!rst_ni) fwd_oh);
  // WB forwarding flag implies a valid WB entry (ALU0/ALU1/MULT)
  AssertHpcWbFv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.alu_pipeline0_i.wb_fwd_valid_q -> kudu_top.alu_pipeline0_i.wb_valid) &&
    (kudu_top.alu_pipeline1_i.wb_fwd_valid_q -> kudu_top.alu_pipeline1_i.wb_valid) &&
    (kudu_top.mult_pipeline_i.wb_fwd_valid_q -> kudu_top.mult_pipeline_i.wb_valid));
  // dcache: EX2-stage forwarding never used; waw fifo occupancy <= Depth(4)
  AssertHpcDcV0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !kudu_top.ls_pipeline_i.genblk1.dcache_i.fwd_info_o.valid[0] &&
    ((kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.wr_ptr_q -
      kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q) <= 3'd4));
  // at most one live writer per register, now including dcache fwd and live dcache waw-fifo entries
  logic fwd_live_all;
  logic lsv0, lsv1;
  logic [5:0] lhd, lsc;
  always_comb begin
    lsv0 = kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'h1, 3'h3} &&
           !(|kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.amo_flag[3:2]);
    lsv1 = kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'h2, 3'h3} &&
           kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid &&
           !(|kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.amo_flag[3:2]);
    lhd = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q[1:0]];
    lsc = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[2'(kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q[1:0]+1)];
  end
  always_comb begin
    fwd_live_all = 1'b1;
    for (int r = 1; r < 32; r++) begin
      logic [8:0] lv;
      lv[0] = kudu_top.alu_pipeline0_i.wb_fwd_valid_q && (kudu_top.alu_pipeline0_i.wb_reg.rd == r);
      lv[1] = kudu_top.alu_pipeline1_i.wb_fwd_valid_q && (kudu_top.alu_pipeline1_i.wb_reg.rd == r);
      lv[2] = kudu_top.mult_pipeline_i.ex2_valid && kudu_top.mult_pipeline_i.ex2_fwd_ok &&
              kudu_top.mult_pipeline_i.ex2_reg.rf_we && (kudu_top.mult_pipeline_i.ex2_reg.rd == r);
      lv[3] = kudu_top.mult_pipeline_i.wb_fwd_valid_q && (kudu_top.mult_pipeline_i.wb_reg.rd == r);
      lv[4] = kudu_top.ls_pipeline_i.genblk1.dcache_i.fwd_info_o.valid[1] &&
              (kudu_top.ls_pipeline_i.genblk1.dcache_i.fwd_info_o.addr1 == r);
      // live pending loads in lsu_if (hold, dly) whose dcache waw-fifo entry is not yet WAW-cancelled
      lv[5] = lsv0 && kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.is_load && lhd[5] &&
              (kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.rd == r);
      lv[6] = lsv1 && kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.is_load && (lsv0 ? lsc[5] : lhd[5]) &&
              (kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.rd == r);
      lv[8:7] = 2'b00;
      if (!$onehot0(lv)) fwd_live_all = 1'b0;
    end
  end
  // a load issued to (or pending in) the LS pipeline always writes rd
  AssertHpcLdWeIss: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.ls_pipeline_i.us_valid_i && !kudu_top.ls_pipeline_i.cmplx_lsu_req_valid_i &&
     kudu_top.ls_pipeline_i.lsu_req_dec.is_load) -> kudu_top.ls_pipeline_i.lsu_req_dec.rf_we);
  AssertHpcLdWePend: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (lsv0 && kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.is_load -> kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.rf_we) &&
    (lsv1 && kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.is_load -> kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.rf_we));
  // AMO (cmplx) LSU requests are only generated while the issuer is not in DECODE (no normal issue)
  AssertHpcCmplxExcl: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.comlx_unit_i.cmplx_fsm_cs != 2'h0 || kudu_top.cmplx_lsu_req_valid) ->
    !kudu_top.issuer_i.ctrl_fsm_cs[CSM_DECODE]);
  // an AMO (cmplx) LSU request never coincides with an LS-pipeline issue
  AssertHpcCmplxExcl2: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.cmplx_lsu_req_valid -> !kudu_top.ls_pipeline_i.us_valid_i);
  // AMO (cmplx) requests, issued or pending in lsu_if, are never dcache-able
  AssertHpcAmoNoCache: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.ls_pipeline_i.cmplx_lsu_req_valid_i -> !kudu_top.ls_pipeline_i.lsu_req_dec.cache_ok) &&
    ((kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'h1, 3'h3}) &&
     (|kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.amo_flag[3:2]) -> !kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.cache_ok) &&
    ((kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'h2, 3'h3}) && kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid &&
     (|kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.amo_flag[3:2]) -> !kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.cache_ok));
  // dcache waw-fifo entries correspond 1:1 (in order, by rd) to the requests pending in lsu_if
  logic lsif_match;
  always_comb begin
    logic [2:0] n, cnt;
    logic [5:0] hd, sc;
    logic [1:0] rp;
    logic       v0, v1;
    logic [4:0] r0, r1, f0, f1;
    n  = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.wr_ptr_q -
         kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q;
    rp = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.rd_ptr_q[1:0];
    hd = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[rp];
    sc = kudu_top.ls_pipeline_i.genblk1.dcache_i.waw_fifo_i.fifo_mem[2'(rp+1)];
    // pending non-AMO (non-cmplx) requests in lsu_if, oldest first: hold, then dly
    v0 = kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'h1, 3'h3} &&
         !(|kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.amo_flag[3:2]);
    v1 = kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q inside {3'h2, 3'h3} &&
         kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid &&
         !(|kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.amo_flag[3:2]);
    r0 = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q.rd;
    r1 = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q.rd;
    cnt = 3'(v0) + 3'(v1);
    f0 = v0 ? r0 : r1;
    lsif_match = (n == cnt) && (cnt == 0 || hd[4:0] == f0) && (cnt < 2 || sc[4:0] == r1) &&
                 (kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q <= 3'h3);
  end
  AssertHpcLsIfMatch: assert property (@(posedge clk_i) disable iff (!rst_ni) lsif_match);
  AssertHpcFwdLiveAll: assert property (@(posedge clk_i) disable iff (!rst_ni) fwd_live_all);
  // EX2-stage forwarded data (data0) is canonical
  AssertHpcFwd0Canon: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.alupl0_fwd_info.valid[0] -> canon(kudu_top.alupl0_fwd_info.data0)) &&
    (kudu_top.alupl1_fwd_info.valid[0] -> canon(kudu_top.alupl1_fwd_info.data0)) &&
    (kudu_top.lspl_fwd_info.valid[0]   -> canon(kudu_top.lspl_fwd_info.data0)) &&
    (kudu_top.multpl_fwd_info.valid[0] -> canon(kudu_top.multpl_fwd_info.data0)));
  // ALU WB-stage cheri result registers produce a canonical cap: either set-address recomputes
  // the correction bits from a consistent ptrmi9, or the registered op cap is already canonical
  function automatic logic aluq_ok(full_cap_t c, logic sa, logic [8:0] p9);
    return sa ? (p9 == 9'(c.addr >> c.exp)) : canon(c[OpW-1:0]);
  endfunction
  logic aluq0_ok, aluq1_ok;
  assign aluq0_ok = !(kudu_top.alu_pipeline0_i.wb_fwd_valid_q && kudu_top.alu_pipeline0_i.wb_reg.is_cheri) ||
    aluq_ok(kudu_top.alu_pipeline0_i.gen_cheri_alu.cheri_alu_i.imd_fcap_q,
            kudu_top.alu_pipeline0_i.gen_cheri_alu.cheri_alu_i.setaddr_flag_q,
            kudu_top.alu_pipeline0_i.gen_cheri_alu.cheri_alu_i.ptrmi9_q);
  assign aluq1_ok = !(kudu_top.alu_pipeline1_i.wb_fwd_valid_q && kudu_top.alu_pipeline1_i.wb_reg.is_cheri) ||
    aluq_ok(kudu_top.alu_pipeline1_i.gen_cheri_alu.cheri_alu_i.imd_fcap_q,
            kudu_top.alu_pipeline1_i.gen_cheri_alu.cheri_alu_i.setaddr_flag_q,
            kudu_top.alu_pipeline1_i.gen_cheri_alu.cheri_alu_i.ptrmi9_q);
  AssertHpcAluQ: assert property (@(posedge clk_i) disable iff (!rst_ni) aluq0_ok && aluq1_ok);
  // issuer operand (after forwarding mux) is canonical
  AssertHpcOpA: assert property (@(posedge clk_i) disable iff (!rst_ni) canon(kudu_top.issuer_i.ira_op_data2_fwd.d0));
  AssertHpcOpB: assert property (@(posedge clk_i) disable iff (!rst_ni) canon(kudu_top.issuer_i.irb_op_data2_fwd.d0));
  // cs1 operand of an issued CJALR is canonical
  AssertHpcOpCanon: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.mult_pipeline_i.cjalr_pcc_set_o |->
    (kudu_top.mult_pipeline_i.full_data2.d0 == op2fullcap(reg2opcap(kudu_top.mult_pipeline_i.full_data2.d0[RegW-1:0]))));
  // combinational: canonical cs1 equal (reg bits) to the RA prediction gives the IR-predicted PCC
  AssertHpcPCjalrComb: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.mult_pipeline_i.cjalr_pcc_set_o && kudu_top.mult_pipeline_i.instr_dec.ptaken &&
    (kudu_top.mult_pipeline_i.instr_dec.ptarget[RegW-1:0] == kudu_top.mult_pipeline_i.full_data2.d0[RegW-1:0]) &&
    (kudu_top.mult_pipeline_i.full_data2.d0 == op2fullcap(reg2opcap(kudu_top.mult_pipeline_i.full_data2.d0[RegW-1:0]))) |->
    (kudu_top.mult_pipeline_i.cjalr_pcap_o == pred(kudu_top.mult_pipeline_i.instr_dec)));

  // datapath: a correctly predicted CJALR produces exactly the IR-predicted PCC
  AssertHpcPCjalr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.mult_pipeline_i.cjalr_pcc_set_o && kudu_top.mult_pipeline_i.instr_dec.ptaken &&
    (kudu_top.mult_pipeline_i.instr_dec.ptarget[RegW-1:0] == kudu_top.mult_pipeline_i.full_data2.d0[RegW-1:0]) |->
    (kudu_top.mult_pipeline_i.cjalr_pcap_o == pred(kudu_top.mult_pipeline_i.instr_dec)));


  // combined PCC invariant (1-inductive given the lemmas above + PCjalr):
  //  s1 entry1 PCC = successor of entry0, IR PCC = successor of the tail,
  //  and the oldest PCC in flight (head or IR) = EX PCC unless single-stepping
  logic pcc_ok;
  assign pcc_ok = ((s1_cnt == 2'd2) -> (m1 == (pok(s1e0) ? pred(s1e0) : m0))) &&
                  ((s1_cnt != 2'd0) -> (ir_pcc == (pok(s1t) ? pred(s1t) : mt))) &&
                  (((s1_cnt == 2'd0) && !esc) -> (ir_pcc == ex1_pcc)) &&
                  (((s1_cnt != 2'd0) && !esc) -> (m0 == ex1_pcc));
  AssertHpcPccAll: assert property (@(posedge clk_i) disable iff (!rst_ni) pcc_ok);

endmodule

`endif
