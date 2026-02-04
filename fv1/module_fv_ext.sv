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
  bind kudu_top            kudu_top_fv_ext        kudo_top_fv_ext_i (.*);
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
  input  logic           handle_special,
  input  logic [15:0]    ctrl_fsm_cs,
  input  logic [15:0]    ctrl_fsm_ns,
  input  logic [1:0]     sbdfifo_wr_valid_o,
  input  sbd_fifo_t      sbdfifo_wdata0_o,
  input  sbd_fifo_t      sbdfifo_wdata1_o,
  input  logic [1:0]     issuer_rdy_o,
  input  logic [4:0]     ir0_pl_sel,
  input  logic [4:0]     ir1_pl_sel,
  input  logic [4:0]     ex_rdy,
  input  logic           pc_set_o,
  input  ir_dec_t        ir0_dec, 
  input  ir_dec_t        ir1_dec, 
  input  logic [31:0]    ir0_reg_rd_req, 
  input  logic [31:0]    ir0_reg_wr_req, 
  input  logic [31:0]    ir1_reg_rd_req, 
  input  logic [31:0]    ir1_reg_wr_req,
  input  logic [1:0]     branch_mispredict
);

`ifdef KUDU_FORMAL_G1
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
                    && ~branch_mispredict[0]) ));

  // if pc_set (from ir0 misprediction, etc), issuer_rdy_o[1] is a don't care
  AssertDequeueIR1: assert property (@(posedge clk_i) 
    (issuer_rdy_o[1] |-> (ir1_issued | pc_set_o) ));

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
    ((ir0_issued_normal & branch_mispredict[0]) |-> (pc_set_o & ~ir1_issued) ));
  AssertMisPredict1: assert property (@(posedge clk_i) 
    ((ir1_issued_normal & branch_mispredict[1]) |-> pc_set_o ));

  // 
  // "Special" issue case
  //
  logic ir0_issued_speical;
  assign ir0_issued_special = ir0_issued & ctrl_fsm_cs[CSM_ISSUE_SPECIAL];

  // hold the IR registers while waiting for cmt fifo to clear
  AssertIssueSpecialWait0: assert property (@(posedge clk_i) 
    (ctrl_fsm_cs[CSM_WAIT_CMT0]  |-> ((issuer_rdy_o == 2'b00) && ~pc_set_o) ));

  AssertIssueSpecial0: assert property (@(posedge clk_i) 
    (ir0_issued_special  |-> issuer_rdy_o[0]  ));

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
  input  cmt_err_info_t     cmt_err_info_o,
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

`ifdef KUDU_FORMAL_G1
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
  // RF We generation only for valid requests
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
  // Only dequeues the EX pipelines if they hold valid data
  //
  AssertALU0Read: assert property (@(posedge clk_i) 
    (alupl0_rdy_o |-> alupl0_valid_i));
  AssertALU1Read: assert property (@(posedge clk_i) 
    (alupl1_rdy_o |-> alupl1_valid_i));
  AssertLSRead: assert property (@(posedge clk_i) 
    (lspl_rdy_o |-> lspl_valid_i));
  AssertMultRead: assert property (@(posedge clk_i) 
    (multpl_rdy_o |-> multpl_valid_i));

`endif
endmodule

////////////////////////////////////////////////////////////////
// Prefetcher
////////////////////////////////////////////////////////////////

module prefetch_fv_ext import super_pkg::*; (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        cheri_const_fetch_i,  
  input  logic        req_i,

  input  logic        branch_i,
  input  logic [31:0] addr_i,

  input  logic [1:0]  ready_i,
  input  logic [1:0]  valid_o,
  input  ir_reg_t     instr0_o,
  input  ir_reg_t     instr1_o,
  input  logic [31:0] instr1_pc_spec0_o,
  input  logic [31:0] instr1_pc_spec1_o,

  // goes to instruction memory / instruction cache
  input  logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic [31:0] instr_addr_o,
  input  logic [63:0] instr_rdata_i,
  input  logic        instr_err_i,
  input  logic        instr_rvalid_i
);

`ifdef KUDU_FORMAL_G2
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

  AssumeInstrGnt0: assume property (instr_req_o |-> ##[0:3] instr_gnt_i);
  AssumeInstrGnt1: assume property ((~rst_ni | ~instr_req_o) |-> ~instr_gnt_i);
  //AssumeInstrGntNoDly0:   assume property (instr_req_o |-> instr_gnt_i);
  //AssumeInstrGntNoDly1:   assume property (~instr_req_o |-> ~instr_gnt_i);
  AssumeInstrValid:       assume property (instr_rvalid_i == instr_rvalid_mem);
  AssumeInstrErr:         assume property (instr_err_i == instr_err_mem);
  AssumeFetchedInstr:     assume property (instr_rdata_i == instr_rdata_mem);
 
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
  input  logic            data_sc_resp_i,
  input  logic [MemW-1:0] data_rdata_i,

  input  logic            cmplx_lsu_req_valid_i,
  input  logic            lsu_req,
  input  logic            lsu_req_done,
  input  logic            lsu_resp_valid,
  input  logic            resp_err_latched,
  input  lsu_req_info_t   lsu_req_info
);

`ifdef KUDU_FORMAL_G3
  //
  // handshaking and sequence
  //
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

  AssumeDataGnt0:   assume property (data_req_o |-> ##[0:1] data_gnt_i);
  AssumeDataGnt1:   assume property ((~rst_ni|~data_req_o) |-> ~data_gnt_i);
  AssumeDataValid:  assume property (data_rvalid_i == data_rvalid_mem);
  AssumeDataErr:    assume property (data_err_i == 1'b0);

  AssumeNoFlush:    assume property (flush_i == 1'b0);
  AssumeNoLatchErr: assume property (load_store_unit_i.lsu_resp_err_o == 1'b0);
  AssumeNormalRq:   assume property (cmplx_lsu_req_valid_i == 1'b0);

  AssumeDsRdy:      assume property (lspl_valid_o |-> ##[0:2] ds_rdy_i);

  // Let's just assume both A&B has the same sequence number. We are not
  // using this to test the ira/b muxing logic
  AssumeInstrSeq:   assume property (instr_dec.pc == {24'h0, instr_seq_in});

  //WaWFiFo can't overrun (underrun permitted if cmplx request)
  AssertWaWFifoNeverFull: assert property (@(posedge clk_i) 
    (waw_fifo_i.wr_rdy_o));
  AssertWaWFifoUnderrun: assert property (@(posedge clk_i) 
    (lspl_valid_o |-> waw_fifo_i.rd_valid_o ));

  // Verify WbFifo won't overrun (write attempt when not ready) due to backpressure to LSU
  // - somehow tryingto prove wbFifo never full takes a very long time when data_gnt deay is 2..
  // No need to assert for WbFiFoUnderrun (part of Assume already)
  AssertWbFifoOverrun: assert property (@(posedge clk_i) 
    (lsu_resp_valid |-> wb_fifo_i.wr_rdy_o));

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
    ((lspl_valid_o & ds_rdy_i) |-> (lspl_output_o.pc == {24'h0, instr_seq_exp}) ));

  AssertLSReqSeq: assert property (@(posedge clk_i) 
    ((lsu_req) |-> (lsu_req_info.pc == {24'h0, req_seq_exp}) ));

  // 
  // memory interface and LSU interface protocol checking
  //
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

  AssertDataIfProtocol0:  assert property (@(posedge clk_i) 
    ( mem_not_gnt |-> $stable(data_addr_o) ));
  AssertDataIfProtocol1:  assert property (@(posedge clk_i) 
    ( mem_not_gnt |-> $stable(data_req_o) ));

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
endmodule

////////////////////////////////////////////////////////////////
// Mult Pipeline
////////////////////////////////////////////////////////////////

module mult_pipeline_fv_ext import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; (
  input  logic            clk_i,
  input  logic            rst_ni,

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
  input  logic            div_sel,
  input  logic            ex2_valid,
  input  logic            wb_rdy,
  input  logic            wb_valid
);

`ifdef KUDU_FORMAL_G4

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
            mult_instr <= '{(instr_dec.rf_we & (instr_dec.rd!=0)), instr_dec.pc, instr_dec.rd, 3'h1};
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

`ifdef KUDU_FORMAL_G5

  //
  // this models the life cycle of a single instruction as it is passed through pipeline stages
  // so we can check things like whether FWD and WRSV are canceled at the right time
  //
  typedef struct packed {
    logic        fwd; 
    logic [7:0]  pc; 
    logic [4:0]  rd;
    logic [2:0]  state;   // which pipelime stage the instruction is in
  } instr_tracking_t;

  instr_tracking_t alu_instr;  

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni)  begin
      alu_instr <= '0;
    end else begin
      case (alu_instr.state) 
        0: begin
          if (us_valid_i & alupl_rdy_o)
            alu_instr <= '{(instr_i.rf_we & (instr_i.rd!=0)), instr_i.pc, instr_i.rd, 3'h1};
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

`endif
endmodule


////////////////////////////////////////////////////////////////
// kudu_top
////////////////////////////////////////////////////////////////

module kudu_top_fv_ext import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; (
  input  logic           clk_i,
  input  logic           rst_ni,
  input  logic           cheri_pmode_i,
  input  logic [31:0]    boot_addr_i
);

 AssumeKTopCfgCheriMode:   assume property (cheri_pmode_i == 1'b1);
 AssumeKTopCfgBootAddr:    assume property (boot_addr_i == 32'h8000_0000);

`ifdef KUDU_FORMAL_G0
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

`endif


endmodule

