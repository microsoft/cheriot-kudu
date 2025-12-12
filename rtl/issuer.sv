// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Dual-issue instruction issuer
//
//  ir0 is always the 1st (earlier) instruction. Fifo logic handles switching.
module issuer import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; # (
  parameter bit          CHERIoTEn  = 1'b1,
  parameter bit          DualIssue  = 1'b1,
  parameter bit          AllowWaW   = 1'b1,
  parameter bit          LoadFiltEn = 1'b1,
  parameter bit          RV32A      = 1'b1,
  parameter int unsigned DmHaltAddr = 32'h1A110800,
  parameter int unsigned DmExcAddr  = 32'h1A110808
) (
  input  logic             clk_i,
  input  logic             rst_ni,
                           
  input  logic             cheri_pmode_i,
  input  logic [31:0]      boot_addr_i,
                           
  // IF/IR interface       
  input  ir_dec_t          ira_dec_i,
  input  ir_dec_t          irb_dec_i,      
  input  logic             ira_is0_i,
  input  logic [1:0]       ir_valid_i,
  output logic [1:0]       issuer_rdy_o,
                         
  // Regfile             
  input  op_data2_t        ira_op_rf_rdata2_i,
  input  op_data2_t        irb_op_rf_rdata2_i,

  // EX pipeline interface 
  input  logic             alupl0_rdy_i,
  input  pl_fwd_t          alupl0_fwd_info_i,
  input  logic[31:0]       alupl0_fwd_act_i,
                           
  input  logic             alupl1_rdy_i,
  input  pl_fwd_t          alupl1_fwd_info_i,
  input  logic[31:0]       alupl1_fwd_act_i,
                           
  input  logic             lspl_rdy_i,
  input  pl_fwd_t          lspl_fwd_info_i,
  input  logic[31:0]       lspl_fwd_act_i,
                           
  input  logic             multpl_rdy_i,
  input  pl_fwd_t          multpl_fwd_info_i,
  input  logic[31:0]       multpl_fwd_act_i,
                           
  output logic [4:0]       ex_valid_o,
  output logic             lspl_sel_ira_o,
  output logic             multpl_sel_ira_o,
  output logic             cmplx_sel_ira_o,
  output waw_act_t         waw_act_o,
                         
  // Commit interface    
  input  logic             cmt_err_i,         
  input  cmt_err_info_t    cmt_err_info_i,
  input  logic [31:0]      cmt_regwr_i,
  output logic             cmt_flush_o,      
  input  logic [1:0]       sbdfifo_rd_valid_i,
  input  logic [1:0]       sbdfifo_wr_rdy_i,
  output logic [1:0]       sbdfifo_wr_valid_o,
  output sbd_fifo_t        sbdfifo_wdata0_o,  
  output sbd_fifo_t        sbdfifo_wdata1_o,  

  // branch unit interface
  input  branch_info_t     branch_info_i,
  input  logic [31:0]      ir0_jalr_target_i,
  input  logic [31:0]      ir1_jalr_target_i,
  input  logic [2:0]       ir0_cjalr_err_i,
  input  logic [2:0]       ir1_cjalr_err_i,
  output full_data2_t      ira_full_data2_fwd_o,
  output full_data2_t      irb_full_data2_fwd_o,

  // IF fetch address interface
  output logic             fetch_req_o,
  output logic             pc_set_o,          // flushing prefetched instructions and move PC
  output logic [31:0]      pc_target_o,
  output logic             ex_bp_init_o,      // to branch predictor
  output ex_bp_info_t      ex_bp_info_o,      // to branch predictor
                           
  // CSR interface         
  input  priv_lvl_e        priv_mode_i,
  input  logic             irq_pending_i,
  input  irqs_t            irqs_i,
  input  logic             csr_mstatus_mie_i,
  input  logic [31:0]      csr_mtvec_i,
  input  logic [31:0]      csr_mepc_i,
  output logic             csr_mtvec_init_o,
  output logic             csr_save_cause_o,
  output logic [31:0]      csr_exc_pc_o,
  output logic             csr_mepcc_clrtag_o,
  output logic             csr_restore_mret_o,
  output logic             csr_restore_dret_o,
  output exc_cause_e       csr_mcause_o,
  output logic [31:0]      csr_mtval_o,

  // Debug signals
  input  logic             debug_req_i,
  input  logic [31:0]      csr_depc_i,
  input  logic             debug_single_step_i,
  input  logic             debug_ebreakm_i,
  input  logic             debug_ebreaku_i,
  output logic             debug_mode_o,
  output dbg_cause_e       debug_cause_o,
  output logic             debug_csr_save_o,

  // CHERIoT Revocation interface
  input  logic             trvk_en_i,
  input  logic [4:0]       trvk_addr_i,
  input  logic             trvk_outstanding_i,

  // cmplx unit interface
  input  logic             cmplx_instr_done_i,
  input  logic             cmplx_sbd_wr_i,
  input  sbd_fifo_t        cmplx_sbd_wdata_i,
  output logic             cmplx_instr_start_o
);

  //
  // Functions
  //
  function automatic logic [4:0] select_pl (logic cheri_pmode, logic enable, 
                                            logic ir_a, pl_type_e pl_type );
    logic [4:0] result;

    
    if (enable & cheri_pmode && (pl_type == PL_JALR)) 
      result = 5'h11;           // select branch unit and mult (CHERIoT case)
    else if (enable && ((pl_type == PL_JAL) || (pl_type == PL_JALR))  && ir_a)
      result = 5'h3;           // select branch unit and alupl0 (ira)
    else if (enable && ((pl_type == PL_JAL) || (pl_type == PL_JALR)))
      result = 5'h5;           // select branch unit and alupl1 (irb)
    else if (enable && (pl_type == PL_LOCAL))
      result = 5'h1;
    else if (enable && (pl_type == PL_ALU) && ir_a)
      result = 5'h1 << 1;
    else if (enable && (pl_type == PL_ALU))
      result = 5'h1 << 2;
    else if (enable && (pl_type == PL_LS))
      result = 5'h1 << 3;
    else if (enable && (pl_type == PL_MULT))
      result = 5'h1 << 4;
    else
      result = 5'h0;

    return result;
  endfunction

  function automatic logic [OpW-1:0] fwd_lookup (logic [4:0] rf_raddr, logic [OpW-1:0] op_rf_rdata,
                                                       pl_fwd_t fwd_info[4]);
    logic [OpW-1:0] result, result1, result2;
    logic [OpW-1:0] data0, data1, zero_mask, fwd_mask;
    logic [1:0]     rf_raddr_match[4];
    logic           zero_bit, fwd_any;

    int i;

    zero_bit  = |rf_raddr;
    zero_mask = {OpW{zero_bit}};

    fwd_any = 1'b0;
    for (i = 0; i < 4; i++) begin
      rf_raddr_match[i][0] = fwd_info[i].valid[0] && (rf_raddr == fwd_info[i].addr0);
      rf_raddr_match[i][1] = fwd_info[i].valid[1] && (rf_raddr == fwd_info[i].addr1);
      fwd_any = fwd_any | rf_raddr_match[i][0] | rf_raddr_match[i][1]; 
    end
    fwd_mask = {OpW{~fwd_any}};

    result1 = op_rf_rdata & zero_mask & fwd_mask;  // RF read data

    result2 = OpW'(0);
    for (i = 0; i < 4; i++) begin
      data0 = zero_mask & fwd_info[i].data0;
      data1 = zero_mask & fwd_info[i].data1;
      result2 = result2 | ({OpW{rf_raddr_match[i][0]}} & data0);
      result2 = result2 | ({OpW{rf_raddr_match[i][1]}} & data1);
    end

    result = result1 | result2;  // final step

    return result;
  endfunction

  function automatic op_data2_t get_fwd_rdata2 (rf_raddr2_t rf_raddr2, op_data2_t op_rf_rdata2,
                                                pl_fwd_t fwd_info[4]);
    op_data2_t result;
    result.d0 = fwd_lookup(rf_raddr2.a0, op_rf_rdata2.d0, fwd_info);
    result.d1 = fwd_lookup(rf_raddr2.a1, op_rf_rdata2.d1, fwd_info);

    return result;
  endfunction 

  function automatic logic is_issued (logic [4:0] pl_sel, logic [4:0] ex_rdy);
    logic result;
    logic ex_sel, ex_go, branch_sel;

    branch_sel = pl_sel[0];
    ex_sel     = |pl_sel[4:1];

    case ({ex_sel, branch_sel}) 
      2'b00: result = 1'b0;
      2'b01: result = 1'b1;
      2'b10, 2'b11: result = |(pl_sel[4:1] & ex_rdy[4:1]);
      default: result = 1'b0;
    endcase

    return result;
  endfunction

  logic [4:0]  ir0_pl_sel, ir0_pl_sel_raw, ir0_pl_sel_normal, ir1_pl_sel;
  logic        ir0_issued, ir0_normal_issued, ir0_special_issued; 
  logic        ir1_issued;
  logic [4:0]  ex_rdy;
  ir_dec_t     ir0_dec, ir1_dec;

  rf_raddr2_t  ira_rf_raddr2, irb_rf_raddr2;
  op_data2_t   ira_op_data2_fwd, irb_op_data2_fwd;

  pl_fwd_t     fwd_info[4];

  logic [1:0]  normal_ex_enable;
  logic [1:0]  pl_sel_enable;
  logic [1:0]  ir_hazard;

  logic [1:0]  branch_mispredict;
  logic        cheri_pmode;
  logic        ir0_is_cjalr, ir1_is_cjalr;

  logic        debug_mode_q, single_step_trap_q;
  logic        debug_ebreak;

  //
  //  Dual-issue instruction dispatcher
  //

  // "normal" and "special" cases 
  // - "Normal" instructions are issued in DECODE state
  //    -- dual issue, subject to hazards, 
  // - "Special" instructions are issued in ISSUE_SPECIAL state
  //    -- single issue (IR0 only), not subject to hazards
  //    -- Traps, IRQ, debug request, etc. are also processed the same way

  assign cheri_pmode = CHERIoTEn & cheri_pmode_i;
  
  // instr a/b input, time-ordered
  assign ir0_dec = ira_is0_i ? ira_dec_i : irb_dec_i;
  assign ir1_dec = ira_is0_i ? irb_dec_i : ira_dec_i;

  // Choise EX pipelines to issue the new instructions
  //   - pl_sel: assert valid to downstream
  //   - ir_issued: downstream accepted instruction, popping the IR FIFO

  assign ex_rdy     = {multpl_rdy_i, lspl_rdy_i, alupl1_rdy_i, alupl0_rdy_i, 1'b1};

  assign ex_valid_o = ir0_pl_sel | ir1_pl_sel;
  assign ir0_pl_sel_raw    = select_pl(cheri_pmode, 1'b1, ira_is0_i, ir0_dec.pl_type);
  assign pl_sel_enable[0]  = normal_ex_enable[0] | ir0_special_issued; 

  assign ir0_pl_sel_normal = {5{normal_ex_enable[0]}} & ir0_pl_sel_raw;
  assign ir0_pl_sel        = {5{pl_sel_enable[0]}} & ir0_pl_sel_raw;

  // ir1 can only be issued if ir0 is alredy issued and no conflict in ex pipeline selection
  //   The "local" resource is considered always ready 
  //   - special instruction only goes to ir0)
  //   - branch unit is always ready (can take both issue)
  //   - only mispredicted branches/jal needs to use pc_set. 
  //      ir0 misprediction will preempt ir1 (pl_sel_enable[1]) anyway
  assign pl_sel_enable[1] = DualIssue & ir0_normal_issued & normal_ex_enable[1] & 
                            ~(branch_mispredict[0] | ir0_dec.is_jalr);
  assign ir1_pl_sel       = {~ir0_pl_sel[4:1], 1'b1} & select_pl(cheri_pmode, pl_sel_enable[1], 
                                                                 ~ira_is0_i, ir1_dec.pl_type);

  // issued == all ex pipeline involved must be ready (jal case needs 2)
  assign ir0_normal_issued  = is_issued (ir0_pl_sel_normal, ex_rdy);

  assign ir0_issued = ir0_normal_issued | ir0_special_issued;
  assign ir1_issued = is_issued (ir1_pl_sel, ex_rdy);

  assign issuer_rdy_o[0] = ir0_issued;

  // issuer_rdy_o[1] really should be a don't care when branch_mispredict[0] == 1
  // since we will flush the IR regs. 
  // -- Taking branch_mispredict[0] out of the logic equationto avoid unnecessary timing path.
  // -- basically remove it from the pl_sel_enable[1] logic and keep the rest
  logic        ir1_enable_shadow;
  logic [4:0]  ir1_sel_shadow;
  assign ir1_enable_shadow = DualIssue & ir0_normal_issued & normal_ex_enable[1]; 
  assign ir1_sel_shadow    = {~ir0_pl_sel[4:1], 1'b1} & select_pl(cheri_pmode, ir1_enable_shadow, 
                                                                  ~ira_is0_i, ir1_dec.pl_type);
  assign issuer_rdy_o[1]   = is_issued(ir1_sel_shadow, ex_rdy);
 
  // choose EX pipeline inputs
  assign lspl_sel_ira_o = (ira_is0_i && (ira_dec_i.pl_type == PL_LS)) || 
                          (~ira_is0_i && (irb_dec_i.pl_type != PL_LS));


  logic  ira_go_mult, irb_go_mult;
  assign ira_go_mult = (ira_dec_i.pl_type == PL_MULT) || (cheri_pmode && (ira_dec_i.pl_type == PL_JALR));
  assign irb_go_mult = (irb_dec_i.pl_type == PL_MULT) || (cheri_pmode && (irb_dec_i.pl_type == PL_JALR));

  assign multpl_sel_ira_o = (ira_is0_i && ira_go_mult) || (~ira_is0_i && ~irb_go_mult);

  // complex unit only works on ir0
  assign cmplx_sel_ira_o = ira_is0_i;

  // Scoreboard FIFO writes
  //   -- branches don't go to commit stage
  logic [1:0] ir_fifo_wr;
  assign ir_fifo_wr[0] = ir0_issued & (|ir0_pl_sel[4:1]);
  assign ir_fifo_wr[1] = ir1_issued & (|ir1_pl_sel[4:1]);
  assign sbdfifo_wr_valid_o[0] = (|ir_fifo_wr) | cmplx_sbd_wr_i;
  assign sbdfifo_wr_valid_o[1] = ir_fifo_wr[0] & ir_fifo_wr[1];

  // ir0 could be local (no write to scoreboard)
  assign sbdfifo_wdata0_o.pl   = cmplx_sbd_wr_i ? cmplx_sbd_wdata_i.pl : (ir_fifo_wr[0] ? ir0_pl_sel : ir1_pl_sel);
  assign sbdfifo_wdata0_o.pc   = cmplx_sbd_wr_i ? cmplx_sbd_wdata_i.pc : (ir_fifo_wr[0] ? ir0_dec.pc : ir1_dec.pc);
  assign sbdfifo_wdata1_o.pl   = ir1_pl_sel;
  assign sbdfifo_wdata1_o.pc   = ir1_dec.pc;

  // regfile read address, will mux expanded rf_rdata into target pipelines	 
  assign ira_rf_raddr2.a0 = ira_dec_i.rs1;
  assign ira_rf_raddr2.a1 = ira_dec_i.rs2;
  assign irb_rf_raddr2.a0 = irb_dec_i.rs1;
  assign irb_rf_raddr2.a1 = irb_dec_i.rs2;

  //
  // resolve data forwarding
  //
  assign fwd_info[0] = alupl0_fwd_info_i;
  assign fwd_info[1] = alupl1_fwd_info_i;
  assign fwd_info[2] = lspl_fwd_info_i;
  assign fwd_info[3] = multpl_fwd_info_i;

  assign ira_op_data2_fwd = get_fwd_rdata2 (ira_rf_raddr2, ira_op_rf_rdata2_i, fwd_info);
  assign irb_op_data2_fwd = get_fwd_rdata2 (irb_rf_raddr2, irb_op_rf_rdata2_i, fwd_info);

  if (CHERIoTEn) begin
    assign ira_full_data2_fwd_o.d0 = op2fullcap(ira_op_data2_fwd.d0);
    assign ira_full_data2_fwd_o.d1 = op2fullcap(ira_op_data2_fwd.d1);
    assign irb_full_data2_fwd_o.d0 = op2fullcap(irb_op_data2_fwd.d0);
    assign irb_full_data2_fwd_o.d1 = op2fullcap(irb_op_data2_fwd.d1);
  end else begin
    assign ira_full_data2_fwd_o = ira_op_data2_fwd;
    assign irb_full_data2_fwd_o = irb_op_data2_fwd;
  end 
  
  //
  // Hazard resolution
  //

  // - RaW hazards staill new instruction until fwd data avaliable
  // - WaW hazards stall new instruction until committed

  logic [31:0] ir0_raw_st, ir0_waw_st;
  logic [31:0] ir1_raw_st, ir1_waw_st;
  logic [31:1] reg_wrsv_q;
  logic [31:0] ir0_reg_rd_req, ir0_reg_wr_req;
  logic [31:0] ir1_reg_rd_req, ir1_reg_wr_req;
  logic        wr_req_conflict;
  logic [1:0]  ir_raw_hazard, ir_waw_hazard;
  logic [31:1] reg_cheri_trsv_q;
  logic [31:0] ir0_cheri_trsv_st, ir1_cheri_trsv_st;
  logic [1:0]  ir_cheri_hazard;


  logic [31:0] ir0_pl_fwd_act, ir1_pl_fwd_act;

  assign ir0_pl_fwd_act = alupl0_fwd_act_i |alupl1_fwd_act_i | lspl_fwd_act_i | multpl_fwd_act_i; 
  assign ir1_pl_fwd_act = AllowWaW ? ir0_pl_fwd_act & ~ir0_reg_wr_req: ir0_pl_fwd_act ; 

  assign ir0_waw_st = {reg_wrsv_q, 1'b0};              // WaW hazards
  assign ir0_raw_st = ir0_waw_st & ~ir0_pl_fwd_act;    // RaW hazards, considering data FWD

  assign ir1_waw_st = ir0_waw_st | ir0_reg_wr_req;     // IR0 reg write happens before IR1 issued 
  assign ir1_raw_st = ir1_waw_st & ~ir1_pl_fwd_act;

  // serialize ir0/ir1 if they write to the same register (otherwise forwarding can't resolve)
  //   - the best way is probably to kill IR0 if there is no side effect (memory read etc)
  //   - however simply serializing ir0/ir1 doesn't seem to impact coremark 
  assign wr_req_conflict = | (ir0_reg_wr_req & ir1_reg_wr_req);

  assign ir_raw_hazard[0] = |(ir0_raw_st & ir0_reg_rd_req); 
  assign ir_waw_hazard[0] = ~AllowWaW & (|(ir0_waw_st & ir0_reg_wr_req));
  assign ir_raw_hazard[1] = |(ir1_raw_st & ir1_reg_rd_req); 
  assign ir_waw_hazard[1] = (~AllowWaW & (|(ir1_waw_st & ir1_reg_wr_req))) | wr_req_conflict;

  assign ir_hazard[0] = ir_raw_hazard[0] | ir_waw_hazard[0] | ir_cheri_hazard[0];
  assign ir_hazard[1] = ir_raw_hazard[1] | ir_waw_hazard[1] | ir_cheri_hazard[1];

  assign ir0_reg_rd_req[0] = 1'b0;
  assign ir0_reg_wr_req[0] = 1'b0;
  assign ir1_reg_rd_req[0] = 1'b0;
  assign ir1_reg_wr_req[0] = 1'b0;

  for (genvar i = 1; i < 32; i++) begin : gen_rsv
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (~rst_ni) begin
        reg_wrsv_q[i] <= 1'b0;
      end else begin 
        if (cmt_flush_o) 
          reg_wrsv_q[i] <= 1'b0;
        else if (ir0_normal_issued && ir0_dec.rf_we && (ir0_dec.rd == i))
          reg_wrsv_q[i] <= 1'b1;
        else if (ir1_issued && ir1_dec.rf_we && (ir1_dec.rd == i))
          reg_wrsv_q[i] <= 1'b1;
        else if (cmt_regwr_i[i])
          reg_wrsv_q[i] <= 1'b0;
      end
    end  // always_ff

    assign ir0_reg_rd_req[i] = (ir0_dec.rf_ren[0] && (ir0_dec.rs1 == i)) || 
                               (ir0_dec.rf_ren[1] && (ir0_dec.rs2 == i));
    assign ir1_reg_rd_req[i] = (ir1_dec.rf_ren[0] && (ir1_dec.rs1 == i)) ||
                               (ir1_dec.rf_ren[1] && (ir1_dec.rs2 == i));
    assign ir0_reg_wr_req[i] = ir0_dec.rf_we && (ir0_dec.rd == i);
    assign ir1_reg_wr_req[i] = ir1_dec.rf_we && (ir1_dec.rd == i);
  end

  if (CHERIoTEn & LoadFiltEn) begin : gen_cheri_trsv
    // cheri load-filter register reservation, both WaW and RaW
    assign ir0_cheri_trsv_st  = {reg_cheri_trsv_q, 1'b0};
    assign ir1_cheri_trsv_st  = ir0_cheri_trsv_st | ir0_reg_wr_req; 

    assign ir_cheri_hazard[0] = cheri_pmode & ir0_dec.is_cheri & 
                               (|((ir0_reg_rd_req | ir0_reg_wr_req) & ir0_cheri_trsv_st));
    assign ir_cheri_hazard[1] = cheri_pmode & ir1_dec.is_cheri & 
                               (|((ir1_reg_rd_req | ir1_reg_wr_req) & ir1_cheri_trsv_st));

    for (genvar i = 1; i < 32; i++) begin : gen_trsv_regs
      always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
          reg_cheri_trsv_q[i] <= 1'b0;
        end else begin 
          if (cmt_flush_o)     // controller staemachine will wait for trsv pipeline to drain
            reg_cheri_trsv_q[i] <= 1'b0;
          else if (ir0_normal_issued && ir0_dec.cheri_op.clc && (ir0_dec.rd == i))
            reg_cheri_trsv_q[i] <= 1'b1;
          else if (ir1_issued && ir1_dec.cheri_op.clc && (ir1_dec.rd == i))
            reg_cheri_trsv_q[i] <= 1'b1;
          else if (trvk_en_i && (trvk_addr_i == i))
            reg_cheri_trsv_q[i] <= 1'b0;
        end
      end  // always_ff
    end
  end else begin : gen_no_cheri_trsv
    assign reg_cheri_trsv_q  = 31'h0;
    assign ir0_cheri_trsv_st = 32'h0;
    assign ir1_cheri_trsv_st = 32'h0;
    assign ir_cheri_hazard   = 2'b00;
  end

  // if allow WAW hazard, broadcast decisions to exp ipelines to cancel forwarding
  // and keep the wrsv_q set
  assign waw_act_o.valid[0] = AllowWaW & ir0_normal_issued & ir0_dec.rf_we; 
  assign waw_act_o.rd0      = ir0_dec.rd;
  assign waw_act_o.valid[1] = AllowWaW & ir1_issued & ir1_dec.rf_we; 
  assign waw_act_o.rd1      = ir1_dec.rd;

  //
  // Controller state machine
  //
 
  logic [15:0]     ctrl_fsm_ns, ctrl_fsm_cs;
  logic [1:0]      ir_any_err, ir_sysctl, ir_cmplx;
  logic            handle_special, handle_err, handle_irq, handle_debug, handle_sysctl, handle_cmplx;
  sysctl_t         sysclt_d, sysctl_q;
  logic [31:0]     special_pc_q, last_set_pc_q;
  special_case_e   special_case_q;
  logic            special_setpc_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin 
    if (!rst_ni) begin
      ctrl_fsm_cs   <= (1 << CSM_RESET);
    end else begin
      ctrl_fsm_cs   <= ctrl_fsm_ns;
    end
  end

  always_comb begin
    ctrl_fsm_ns   = ctrl_fsm_cs;

    unique case (1'b1)
      ctrl_fsm_cs[CSM_RESET]: begin
        ctrl_fsm_ns = 1 << CSM_BOOT_SET;
      end

      ctrl_fsm_cs[CSM_BOOT_SET]: begin
        ctrl_fsm_ns = 1 << CSM_DECODE;
      end

      ctrl_fsm_cs[CSM_DECODE]: begin
        if (cmt_err_i) 
          ctrl_fsm_ns = 1 << CSM_CMT_FLUSH; 
        else if (handle_special)
          ctrl_fsm_ns = 1 << CSM_WAIT_CMT0; 
      end

      ctrl_fsm_cs[CSM_CMT_FLUSH]: begin
        ctrl_fsm_ns = 1 << CSM_WAIT_TRVK;   
      end

      ctrl_fsm_cs[CSM_WAIT_TRVK]: begin
        if (~trvk_outstanding_i)
          ctrl_fsm_ns = 1 << CSM_DECODE; 
      end

      ctrl_fsm_cs[CSM_WAIT_CMT0]: begin
        // Defer processing issuer-side special cases till
        //  - all previously issued instruction are commited
        //  - and operands are ready if the special case is caused by an instruction.
        //  - all outstanding trvk requests are completed
        //  Processing specail cases may require changing CSR context which may impact those pending 
        //  instructions if they are not completed first.
        if (cmt_err_i) 
          ctrl_fsm_ns = 1 << CSM_CMT_FLUSH;
        else if (~sbdfifo_rd_valid_i[0] & ~trvk_outstanding_i)
          ctrl_fsm_ns = 1 << CSM_ISSUE_SPECIAL;  
      end

      ctrl_fsm_cs[CSM_ISSUE_SPECIAL]: begin 
        if ((special_case_q == SYSCTL) && (sysctl_q.csrw | sysctl_q.cjalr))
          ctrl_fsm_ns = 1 << CSM_WAIT_CMT1;
        else if ((special_case_q == SYSCTL) && sysctl_q.wfi) 
          ctrl_fsm_ns = 1 << CSM_SLEEP;
        else if  (special_case_q == CMPLX)
          ctrl_fsm_ns = 1 << CSM_WAIT_CMPLX;  
        else 
          ctrl_fsm_ns = 1 << CSM_DECODE;
      end

      ctrl_fsm_cs[CSM_WAIT_CMT1]: begin
        if (cmt_err_i) 
          ctrl_fsm_ns = 1 << CSM_CMT_FLUSH;
        else if (~sbdfifo_rd_valid_i[0] & ~trvk_outstanding_i)
          ctrl_fsm_ns = 1 << CSM_DECODE;
      end

      ctrl_fsm_cs[CSM_WAIT_CMPLX]: begin
        if (cmt_err_i) 
          ctrl_fsm_ns = 1 << CSM_CMT_FLUSH;
        else if (cmplx_instr_done_i) 
          ctrl_fsm_ns = 1 << CSM_WAIT_CMT1;
      end

      ctrl_fsm_cs[CSM_SLEEP]: begin
        if (irq_pending_i)                 // don't look at MIE in sleep state
          ctrl_fsm_ns = 1 << CSM_DECODE;   // QQQ should we clear IF after exiting sleep? don't really see why..
      end
      
      default: begin
        ctrl_fsm_ns   = 1 << CSM_RESET;
      end
    endcase
  end

  //
  // PC set logic
  //
  assign branch_mispredict = branch_info_i.mispredict_taken | branch_info_i.mispredict_not_taken;

  always_comb begin

    unique case (1'b1)
      ctrl_fsm_cs[CSM_BOOT_SET] : begin
        pc_set_o    = 1'b1;
        pc_target_o = { boot_addr_i[31:8], 8'h80 };
      end 
      ctrl_fsm_cs[CSM_DECODE] : begin
        if (ir0_dec.is_jalr & ir0_issued)
          pc_set_o    = 1'b1;
        else if (branch_mispredict[0] && ir0_issued)
          pc_set_o    = 1'b1;
        else if (ir1_dec.is_jalr & ir1_issued)
          pc_set_o    = 1'b1;
        else if (branch_mispredict[1] && ir1_issued) 
          pc_set_o    = 1'b1;
        else 
          pc_set_o    = 1'b0;

        if (~cheri_pmode & ir0_dec.is_jalr)
          pc_target_o = ir0_jalr_target_i;
        else if (branch_info_i.mispredict_taken[0])
          pc_target_o = ir0_dec.btarget;
        else if (branch_info_i.mispredict_not_taken[0])
          pc_target_o = ir0_dec.pc_nxt;
        else if (ir1_dec.is_jalr)
          pc_target_o = ir1_jalr_target_i;
        else if (branch_info_i.mispredict_taken[1])
          pc_target_o = ir1_dec.btarget;
        else if (branch_info_i.mispredict_not_taken[1])
          pc_target_o = ir1_dec.pc_nxt;
        else
          pc_target_o = ir0_dec.btarget;
      end
      ctrl_fsm_cs[CSM_CMT_FLUSH] : begin
        pc_set_o    = 1'b1;
        pc_target_o = special_pc_q;
      end
      ctrl_fsm_cs[CSM_ISSUE_SPECIAL] :  begin
        pc_set_o     = special_setpc_q;
        pc_target_o  = special_pc_q;
      end
      default : begin
        pc_set_o = 1'b0;
        pc_target_o = { boot_addr_i[31:8], 8'h80 };
      end
    endcase

    // if (ctrl_fsm_cs[CSM_BOOT_SET] || ctrl_fsm_cs[CSM_DECODE])
    if (~ctrl_fsm_cs[CSM_RESET] && ~ctrl_fsm_cs[CSM_SLEEP])
      fetch_req_o = 1'b1;
    else
      fetch_req_o = 1'b0;
  end

  //
  // pipeline control
  //

  //  - branches are read from IR (IR0 branch misprediction can cause IR1 to be discarded)
  //  - special (errors, system instructions)are not read/rdy from IR. flushed directly
  //    - Commit errors are handled immediately (disable EX, flush EX pipeline)
  //    - IR0 specials are handled immediately (disable EX, wait for pipeline done)
  //    - IR1 specials are deferred (EX disabled) till it becomes IR0
  //
  //  - CJALR in CHERIoT is handled as an special instruction since it touches PCC and MIE CSR bit

  assign ir_any_err[0] = ir0_dec.any_err;       // CJALR error is handled later as a special case
  assign ir_any_err[1] = ir1_dec.any_err; 
  assign ir_sysctl[0]  = ir0_dec.sysctl.valid;
  assign ir_sysctl[1]  = ir1_dec.sysctl.valid;
  assign ir_cmplx[0]   = ir0_dec.is_cmplx;
  assign ir_cmplx[1]   = ir1_dec.is_cmplx;

  assign handle_irq     = irq_pending_i  & csr_mstatus_mie_i;
  assign handle_debug   = ~debug_mode_q & (debug_req_i | (ir_valid_i[0] & (ir0_dec.is_brkpt | single_step_trap_q)));
  assign handle_cmplx   = RV32A & ir_valid_i[0] & ~ir_any_err[0] & ir0_dec.is_cmplx;
  assign handle_sysctl  = ir_valid_i[0] & ~ir_any_err[0] & ir_sysctl[0];
  assign handle_err     = ir_valid_i[0] & ir_any_err[0]; 
  assign handle_special = handle_err | handle_sysctl | handle_cmplx | handle_irq | handle_debug;

  // "normal" case issue enable
  // instruction can't be issued for IRQ or exception case
  // don't issue if sbdfifo goes full 
  assign normal_ex_enable[0] = sbdfifo_wr_rdy_i[0] & (ctrl_fsm_cs[CSM_DECODE] &
                               ir_valid_i[0] & ~ir_hazard[0] &
                               ~(handle_special | cmt_err_i));
  
  assign normal_ex_enable[1] = sbdfifo_wr_rdy_i[1] & ctrl_fsm_cs[CSM_DECODE] & 
                               ir_valid_i[1] & ~ir_hazard[1] & 
                               ~(handle_special | cmt_err_i | debug_single_step_i) & 
                               ~(ir_any_err[1] | ir_sysctl[1] | ir_cmplx[1] | ir1_dec.is_brkpt);

  assign ir0_special_issued = ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & 
                              ((special_case_q == SYSCTL) || (special_case_q == CMPLX));

  assign debug_mode_o = debug_mode_q;

  assign cmplx_instr_start_o = RV32A & ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == CMPLX);

  //
  // Handling special instructions and IRQ
  //

  assign cmt_flush_o  = ctrl_fsm_cs[CSM_CMT_FLUSH];
  assign debug_ebreak = priv_mode_i == PRIV_LVL_M ? debug_ebreakm_i :
                        priv_mode_i == PRIV_LVL_U ? debug_ebreaku_i : 1'b0;

  // special case action (PC, save cause, etc)
  // decision is made at ISSUE_SPICAL (after WAIT_CMT0))
  // - settle error conditions from the committer side first
  // - csr values won't be settled till CMT0 completes, so special_pc_q can't resolve till then.
  // - requiring all special conditions including handle_irq and debug_req to hold till CMT0 wait done
  //
  // - corner case: if a complx instruction is erred, we allow set_pc_q to be sampled again before CSM_ISSUE_SPECIAL
  logic [1:0] sample_special_case;
 
  assign sample_special_case[0] = ctrl_fsm_ns[CSM_CMT_FLUSH];  
  assign sample_special_case[1] = ctrl_fsm_ns[CSM_ISSUE_SPECIAL];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      sysctl_q            <= NULL_SYSCTL;
      special_case_q      <= NULL;
      special_setpc_q     <= 1'b0;
      special_pc_q        <= RegW'(0);
      last_set_pc_q       <= 32'h0; 
    end else begin
      if (sample_special_case[0]) begin
        special_case_q  <= EXEC;
        special_setpc_q <= 1'b1;  // really don't care in this case
        special_pc_q    <= {csr_mtvec_i[31:2], 2'b00};
      end else if (sample_special_case[1] & 
                   (handle_debug | (ir_valid_i[0] & ir0_dec.sysctl.ebrk & debug_ebreak))) begin
        special_case_q  <= DEBUG; // debug timing is "before" execution, so takes priority
        special_setpc_q <= 1'b1;
        sysctl_q        <= ir0_dec.sysctl;
        special_pc_q    <= DmHaltAddr; 
      end else if (sample_special_case[1]  & ir_valid_i[0] &
                  (ir_any_err[0] | (ir0_dec.sysctl.cjalr & (|ir0_cjalr_err_i)) |
                   (ir0_dec.sysctl.dret & ~debug_mode_q) )) begin
        special_case_q  <= EXEC;
        special_setpc_q <= 1'b1;
        sysctl_q        <= ir0_dec.sysctl;
        special_pc_q    <= {csr_mtvec_i[31:2], 2'b00};
      end else if (sample_special_case[1] & handle_irq) begin
        special_case_q  <= IRQ;
        special_setpc_q <= 1'b1;
        sysctl_q        <= ir0_dec.sysctl;
        special_pc_q    <= {csr_mtvec_i[31:2], 2'b00};    // only support single-vector IRQ for now
      end else if (sample_special_case[1] & handle_sysctl) begin
        // wait till oprands are ready for sysctl instructions (especially cjalr)
        // till its operands are resolved to compute target PC
        special_case_q  <= SYSCTL;
        special_setpc_q <= (ir0_dec.sysctl.ebrk | ir0_dec.sysctl.ecall | ir0_dec.sysctl.mret | 
                            ir0_dec.sysctl.dret | ir0_dec.sysctl.cjalr | ir0_dec.sysctl.fencei);
        sysctl_q        <= ir0_dec.sysctl;
        unique case (1'b1)
          ir0_dec.sysctl.ebrk:   special_pc_q <= {csr_mtvec_i[31:2], 2'b00};
          ir0_dec.sysctl.ecall:  special_pc_q <= {csr_mtvec_i[31:2], 2'b00};
          ir0_dec.sysctl.mret:   special_pc_q <= csr_mepc_i;
          ir0_dec.sysctl.cjalr:  special_pc_q <= ir0_jalr_target_i;
          ir0_dec.sysctl.dret:   special_pc_q <= csr_depc_i;
          ir0_dec.sysctl.fencei: special_pc_q <= ir0_dec.pc_nxt;
          default:;
        endcase
      end else if (sample_special_case[1] & handle_cmplx) begin
        special_case_q  <= CMPLX;
        special_setpc_q <= 1'b0;             // AMO only for now
        sysctl_q        <= ir0_dec.sysctl;   // don't care
        special_pc_q    <= {csr_mtvec_i[31:2], 2'b00};    
      end else if (sample_special_case[1]) begin
        special_case_q  <= NULL;
        special_setpc_q <= 1'b0;
      end

      // if there is IRQ when current IR.pc is not valid (b/c pc_set causing the IR/IF to be flushed),
      // use the last pc_set target value as the return address from ISR
      if (ctrl_fsm_cs[CSM_BOOT_SET])
        last_set_pc_q <= boot_addr_i;
      else if (pc_set_o)
        last_set_pc_q <= pc_target_o;

    end   // posedge clk
  end

  // debug mode & single-stepping control

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      debug_mode_q       <= 1'b0;
      single_step_trap_q <= 1'b0;
    end else begin
      if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & handle_debug)
        debug_mode_q <= 1'b1;
      else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == SYSCTL) & sysctl_q.dret)
        debug_mode_q <= 1'b0;

      // single-step debugging behavior: 
      // - single-issue 
      // - execute 1 instruction, trap before next instruction is executed

		  // set when single_steip_i and executed (implies single_step_go_debug_q == 0) 
		  // clear when take exception (see below)
      if (debug_single_step_i & ~debug_mode_q & ir0_issued)
        single_step_trap_q <= 1'b1;
      else if (debug_mode_q)
        single_step_trap_q <= 1'b0;
    end
  end

  //
  // CSR interface
  //

  assign csr_mtvec_init_o   = ctrl_fsm_cs[CSM_BOOT_SET];
  assign csr_restore_mret_o = ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == SYSCTL) & sysctl_q.mret;
  assign csr_restore_dret_o = ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == SYSCTL) & sysctl_q.dret;

  logic [4:0]        cjalr_err_cause;
  logic [PVIO_W-1:0] ir0_pvio_vec;

  always_comb begin
    logic [3:0]      mfip_id;

    csr_save_cause_o   = 1'b0;
    csr_mepcc_clrtag_o = 1'b0;
    csr_exc_pc_o       = ir0_dec.pc;
    csr_mtval_o        = 32'h0;                         
    csr_mcause_o       = EXC_CAUSE_IRQ_SOFTWARE_M;
    debug_cause_o      = DBG_CAUSE_NONE;       
    debug_csr_save_o   = 1'b0;

    mfip_id = 4'd0;
    for (int i = 14; i >= 0; i--) begin
      if (irqs_i.irq_fast[i]) begin
        mfip_id = i[3:0];
      end
    end

    ir0_pvio_vec            = 0;
    ir0_pvio_vec[PVIO_TAG]  = ir0_cjalr_err_i[0];
    ir0_pvio_vec[PVIO_SEAL] = ir0_cjalr_err_i[1];
    ir0_pvio_vec[PVIO_EX]   = ir0_cjalr_err_i[2];

    cjalr_err_cause = vio_cause_enc (1'b0, ir0_pvio_vec);

    if (ctrl_fsm_cs[CSM_CMT_FLUSH] & cmt_err_i) begin
      csr_save_cause_o = 1'b1;
      csr_exc_pc_o     = cmt_err_info_i.pc;
      csr_mcause_o     = exc_cause_e'(cmt_err_info_i.mcause);                         
      csr_mtval_o      = cmt_err_info_i.mtval;
    end else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == DEBUG)) begin  
      csr_save_cause_o = 1'b1;
      csr_exc_pc_o     = ir0_dec.pc;
      debug_csr_save_o = 1'b1;
      if (ir_valid_i[0] & ir0_dec.is_brkpt)
        debug_cause_o = DBG_CAUSE_TRIGGER;
      else if (debug_single_step_i)
        debug_cause_o = DBG_CAUSE_STEP;
      else if (debug_req_i)
        debug_cause_o = DBG_CAUSE_HALTREQ;
      else if (debug_ebreak)
        debug_cause_o    = DBG_CAUSE_EBREAK;
    end else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] & (special_case_q == EXEC)) begin
      csr_save_cause_o = 1'b1;
      csr_exc_pc_o     = ir0_dec.pc;
      csr_mcause_o     = EXC_CAUSE_CHERI_FAULT;
      csr_mtval_o      = 0;

      if (ir0_dec.errs.perm_vio) begin 
        csr_mcause_o = EXC_CAUSE_CHERI_FAULT;
        csr_mtval_o  = {21'h0, 1'b1, 5'h0, 5'h2};   // s=1, cap_idx=0
      end else if (ir0_dec.errs.bound_vio) begin 
        csr_mcause_o = EXC_CAUSE_CHERI_FAULT;
        csr_mtval_o  = {21'h0, 1'b1, 5'h0, 5'h1};   // s=1, cap_idx=0
        csr_mepcc_clrtag_o = 1'b1; 
      end else if (ir0_dec.errs.fetch_err) begin 
        csr_mcause_o = EXC_CAUSE_INSTR_ACCESS_FAULT;
        csr_mtval_o  = ir0_dec.pc;
      end else if (ir0_dec.errs.illegal_insn | ir0_dec.errs.illegal_c_insn) begin
        csr_mcause_o = EXC_CAUSE_ILLEGAL_INSN;
        csr_mtval_o  = cheri_pmode ? 32'h0 :
                       (ir0_dec.is_comp ? {16'b0, ir0_dec.c_insn} : ir0_dec.insn);
      end else if (|ir0_cjalr_err_i) begin
        csr_mcause_o = EXC_CAUSE_CHERI_FAULT;
        csr_mtval_o  = {21'h0, 1'b0, ir0_dec.rs1, cjalr_err_cause};
      end
    end else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (special_case_q == IRQ)) begin
      csr_save_cause_o = 1'b1;
      csr_exc_pc_o     = ir_valid_i[0] ? ir0_dec.pc : last_set_pc_q;
      if (irqs_i.irq_fast != 15'b0) 
        // generate exception cause ID from fast interrupt ID:
        // - first bit distinguishes interrupts from exceptions,
        // - second bit adds 16 to fast interrupt ID
        // for example EXC_CAUSE_IRQ_FAST_0 = {1'b1, 5'd16}
        csr_mcause_o = exc_cause_e'({2'b11, mfip_id});
      else if (irqs_i.irq_external) 
        csr_mcause_o = EXC_CAUSE_IRQ_EXTERNAL_M;
      else if (irqs_i.irq_software)
        csr_mcause_o = EXC_CAUSE_IRQ_SOFTWARE_M;
      else  // irqs_i.irq_timer
        csr_mcause_o = EXC_CAUSE_IRQ_TIMER_M;      
    end else if (ctrl_fsm_cs[CSM_ISSUE_SPECIAL] && (special_case_q == SYSCTL) & (sysctl_q.ebrk | sysctl_q.ecall)) begin
      csr_save_cause_o = 1'b1;
      csr_exc_pc_o     = ir0_dec.pc;             
      csr_mcause_o     = sysctl_q.ebrk ? EXC_CAUSE_BREAKPOINT : 
                         (priv_mode_i == PRIV_LVL_M) ?  EXC_CAUSE_ECALL_MMODE :
                          EXC_CAUSE_ECALL_UMODE;

      csr_mtval_o      = ir0_dec.pc;
    end

  end

  //
  // feedback information to branch predictor
  //
  assign ex_bp_init_o = ctrl_fsm_cs[CSM_BOOT_SET];

  assign ex_bp_info_o.is_branch  = {ir1_dec.is_branch, ir0_dec.is_branch} & {ir1_issued, ir0_issued};
  assign ex_bp_info_o.is_jal     = {ir1_dec.is_jal, ir0_dec.is_jal} & {ir1_issued, ir0_issued};
  assign ex_bp_info_o.taken      = branch_info_i.branch_taken;
  assign ex_bp_info_o.pc0        = ir0_dec.pc;
  assign ex_bp_info_o.pc1        = ir1_dec.pc;
  assign ex_bp_info_o.target0    = ir0_dec.btarget;
  assign ex_bp_info_o.target1    = ir1_dec.btarget;


`ifndef SYNTHESIS
  //
  // debug signals
  //

  logic [31:0] issue_pc0, issue_pc1;

  logic [64:0] ir0_cs0_mcap, ir0_cs1_mcap;
  logic [64:0] ir1_cs0_mcap, ir1_cs1_mcap;

  logic        issue_err_event;
  logic        ir0_stall_nohaz_event, ir1_stall_nohaz_event;
  logic        ir0_hazard_event, ir1_hazard_event;
  logic        ir0_raw_hazard_event, ir0_waw_hazard_event;
  logic        ir1_raw_hazard_event, ir1_waw_hazard_event;
  logic [4:0]  ir1_pl_sel_ooo;
  logic        ir1_pl_sel_enable_ooo, ir1_ooo_rdy_event;

  logic [1:0]  branch_mispredict_event;
  logic [1:0]  jal_mispredict_event;

  ctrl_fsm_e   ctrl_fsm_cs_dec;
  logic        ctrl_fsm_err;
  logic        ir0_trap_event;
  logic        ir0_amo_issued;

  function automatic ctrl_fsm_e ctrl_fsm_dec(logic[15:0] ctrl_fsm);
    ctrl_fsm_e result;
    int i;

    result = CSM_RESET;
    for (i = 0; i<16; i++) begin
      if (ctrl_fsm[i]) result = (ctrl_fsm_e'(i));
    end
    return result;  
  endfunction

  assign ctrl_fsm_err    = ($countbits(ctrl_fsm_cs, '1) > 1) || (ctrl_fsm_cs == 0);
  assign ctrl_fsm_cs_dec = ctrl_fsm_dec(ctrl_fsm_cs);

  // visualizing PC for issued insructions
  assign issue_pc0 = ir0_issued ? ir0_dec.pc : {32{1'bz}};
  assign issue_pc1 = ir1_issued ? ir1_dec.pc : {32{1'bz}};

  // cs1/cs2 in memcap format (to compare with trace file)
  assign ir0_cs0_mcap = ira_is0_i ? op2memcap(ira_op_data2_fwd.d0) : op2memcap(irb_op_data2_fwd.d0);
  assign ir0_cs1_mcap = ira_is0_i ? op2memcap(ira_op_data2_fwd.d1) : op2memcap(irb_op_data2_fwd.d1);
  assign ir1_cs0_mcap = ira_is0_i ? op2memcap(irb_op_data2_fwd.d0) : op2memcap(ira_op_data2_fwd.d0);
  assign ir1_cs1_mcap = ira_is0_i ? op2memcap(irb_op_data2_fwd.d1) : op2memcap(ira_op_data2_fwd.d1);
 
  // events for debugging/perfomrance count
  assign issue_err_event = ~ir0_issued & ir1_issued;

  assign branch_mispredict_event = branch_mispredict & ex_bp_info_o.is_branch;
  assign jal_mispredict_event    = branch_mispredict & ex_bp_info_o.is_jal;

  assign ir0_trap_event = (ctrl_fsm_cs_dec == CSM_ISSUE_SPECIAL) && (special_case_q == EXEC);
  assign ir0_amo_issued = (ctrl_fsm_cs_dec == CSM_ISSUE_SPECIAL) && (special_case_q == CMPLX) &&
                          (ir0_dec.insn[6:0] == OPCODE_AMO);
  
  // ir1 ready to be issued otherwise, but blocked by ir0
  assign ir1_pl_sel_enable_ooo = DualIssue & ~branch_mispredict[0] & normal_ex_enable[1]; 
  assign ir1_pl_sel_ooo = ~ir0_pl_sel & select_pl(cheri_pmode, ir1_pl_sel_enable_ooo, 
                                                  ira_is0_i, ir1_dec.pl_type);

  // branch_mispredict[0] is sufficient - if ir0 is branch but correctly predicted, IR1 is good to go.
  assign ir1_ooo_rdy_event = ~ir1_issued & (|(ir1_pl_sel_ooo & ex_rdy));

  assign ir0_stall_nohaz_event = ir_valid_i[0] & ~ir0_issued & ~ir_hazard[0];
  assign ir1_stall_nohaz_event = ir_valid_i[1] & ~ir1_issued & ~ir_hazard[1];

  assign ir0_hazard_event =  ir_valid_i[0] & ir_hazard[0];
  assign ir1_hazard_event =  ir_valid_i[1] & ir_hazard[1];

  assign ir0_raw_hazard_event = ir_valid_i[0] & ir_raw_hazard[0];
  assign ir0_waw_hazard_event = ir_valid_i[0] & ir_waw_hazard[0];

  assign ir1_raw_hazard_event = ir_valid_i[1] & ir_raw_hazard[1];
  assign ir1_waw_hazard_event = ir_valid_i[1] & ir_waw_hazard[1];

  logic [4:0] reg_wrsv_cause[0:31];
  logic [4:0] ir0_raw_cause, ir1_raw_cause;
  logic [4:0] ir0_cause_mask[2], ir1_cause_mask[2];
  logic       ir1_raw_by_ir0_event;

  for (genvar i = 0; i < 32; i++) begin 
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (~rst_ni)
       reg_wrsv_cause[i] <= 0;
      else begin 
        if (i == 0)
          reg_wrsv_cause[i] <= 0;
        else if (ir0_issued && ir0_dec.rf_we && (ir0_dec.rd == i))
          reg_wrsv_cause[i] <= ir0_pl_sel;
        else if (ir1_issued && ir1_dec.rf_we && (ir1_dec.rd == i))
          reg_wrsv_cause[i] <= ir1_pl_sel;
      end
    end
  end

  assign ir0_cause_mask[0] = {5{ir0_dec.rf_ren[0]}} & {5{ir0_raw_st[ir0_dec.rs1]}};
  assign ir0_cause_mask[1] = {5{ir0_dec.rf_ren[1]}} & {5{ir0_raw_st[ir0_dec.rs2]}};

  assign ir0_raw_cause = (reg_wrsv_cause[ir0_dec.rs1] & ir0_cause_mask[0]) | 
                         (reg_wrsv_cause[ir0_dec.rs2] & ir0_cause_mask[1]);

  assign ir1_raw_by_ir0_event = ir_valid_i[1] & ir_raw_hazard[1] & (|(ir0_reg_wr_req & ir1_reg_rd_req));
   
  assign ir1_cause_mask[0] = {5{ir1_dec.rf_ren[0]}} & {5{ir1_raw_st[ir1_dec.rs1]}};
  assign ir1_cause_mask[1] = {5{ir1_dec.rf_ren[1]}} & {5{ir1_raw_st[ir1_dec.rs2]}};

  assign ir1_raw_cause = (reg_wrsv_cause[ir1_dec.rs1] & ir1_cause_mask[0]) | 
                         (reg_wrsv_cause[ir1_dec.rs2] & ir1_cause_mask[1]);
`endif

endmodule     
