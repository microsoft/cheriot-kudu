// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define TOP_PATH kudu_top
`define ISSUER_PATH kudu_top.issuer_i
`define COMMITTER_PATH kudu_top.committer_i

module tracer import cheri_pkg::*; import super_pkg::*; import tracer_pkg::*; (
  input logic        clk_i,
  input logic        rst_ni,
  input logic        cheri_pmode_i
);

  // synthesis translate_off
  parameter bit     RvfiDumpEn   = 1'b0;
  parameter string  TraceLogFile = "trace_kudu_core.log";
  parameter string  RvfiLogFile  = "rvfi_kudu_core.log";

`ifdef TraceDPI
  `include "tracer_dpi_wrapper.sv"
`endif

  typedef struct packed {
    logic [4:0]  pl;
    logic        is_ex;   // instr actually goes to commit FIFO and EX pipelines
    logic        is_amo;
    rvfi_t       rvfi;
    ir_dec_t     ir_dec;
  } instr_trace_t;
  
  function automatic logic [31:0] get_pc_wdata (int ir_sel);
    logic [31:0] result;
    // only need to conside issued branch/jal/jalr instructions (rvfi.valid == 1)
    // note this is basically 
    ir_dec_t      ir_dec;
    logic         mis_taken, mis_not_taken, mis_jal, mis_jalr;
    logic         branch_taken;
    logic         any_err;

    if (ir_sel == 0) begin
      ir_dec        = `ISSUER_PATH.ir0_dec;
      mis_taken     = `ISSUER_PATH.branch_info_i.mis_taken[0];
      mis_not_taken = `ISSUER_PATH.branch_info_i.mis_not_taken[0];
      mis_jal       = `ISSUER_PATH.branch_info_i.mis_jal[0];
      mis_jalr      = `ISSUER_PATH.branch_info_i.mis_jalr[0];
      branch_taken  = `ISSUER_PATH.branch_info_i.branch_taken[0];
      any_err       = `ISSUER_PATH.ir_any_err[0];
    end else begin
      ir_dec        = `ISSUER_PATH.ir1_dec;
      mis_taken     = `ISSUER_PATH.branch_info_i.mis_taken[1];
      mis_not_taken = `ISSUER_PATH.branch_info_i.mis_not_taken[1];
      mis_jal       = `ISSUER_PATH.branch_info_i.mis_jal[1];
      mis_jalr      = `ISSUER_PATH.branch_info_i.mis_jalr[1];
      branch_taken  = `ISSUER_PATH.branch_info_i.branch_taken[1];
      any_err       = `ISSUER_PATH.ir_any_err[1];
    end

    if (any_err) 
      result = ir_dec.pc_nxt;  // somehow this is the ibex tracer behavor - should use the instr.btarget?
    else if ((ir_dec.is_jalr & mis_jalr) | (ir_dec.is_jal & mis_jal)) 
      result = `TOP_PATH.ex_pc_target; 
    else if (ir_dec.is_jalr | ir_dec.is_jal ) 
      result = ir_dec.ptarget;
    else if (ir_dec.is_branch & branch_taken & mis_taken)
      result = `TOP_PATH.ex_pc_target; 
    else if (ir_dec.is_branch & branch_taken)
      result = ir_dec.ptarget;
    else
      result = ir_dec.pc_nxt;
     
    return result;    
  endfunction

  function automatic instr_trace_t get_trace_issued (int ir_sel);
    instr_trace_t  result; 
    logic [31:0]   insn32;
    opcode_e       opcode;
    logic [32:0]   tmp33_0, tmp33_1;

    op_data2_t ir0_op_data2_fwd, ir1_op_data2_fwd;

    ir0_op_data2_fwd = `ISSUER_PATH.ira_is0_i ? `ISSUER_PATH.ira_op_data2_fwd : `ISSUER_PATH.irb_op_data2_fwd; 
    ir1_op_data2_fwd = `ISSUER_PATH.ira_is0_i ? `ISSUER_PATH.irb_op_data2_fwd : `ISSUER_PATH.ira_op_data2_fwd; 

    result.rvfi.order  = 0;     // not used for now
    result.rvfi.halt   = 1'b0;
    result.rvfi.intr   = 1'b0;
    result.rvfi.mode   = 1'b0;
    result.rvfi.ixl    = 1'b0;

    if (ir_sel == 0) begin    // IR0
      insn32                 = `ISSUER_PATH.ir0_dec.insn;
      result.pl              = `ISSUER_PATH.ir0_pl_sel;
      result.ir_dec          = `ISSUER_PATH.ir0_dec;
      result.is_ex           = (| `ISSUER_PATH.ir0_pl_sel[4:1]) || `ISSUER_PATH.ir0_amo_issued;  // AMO defers sbdfifo writes
      result.is_amo          = `ISSUER_PATH.ir0_amo_issued;
      result.rvfi.valid      = `ISSUER_PATH.ir0_issued | `ISSUER_PATH.ir0_trap_event | `ISSUER_PATH.intr_event;     
      result.rvfi.insn       = `ISSUER_PATH.ir0_dec.is_comp ?  `ISSUER_PATH.ir0_dec.c_insn : `ISSUER_PATH.ir0_dec.insn;
      result.rvfi.trap       = `ISSUER_PATH.ir0_trap_event;
      result.rvfi.rs1_addr   = `ISSUER_PATH.ir0_dec.rs1;
      result.rvfi.rs2_addr   = `ISSUER_PATH.ir0_dec.rs2;
      result.rvfi.rs3_addr   = 0;
      result.rvfi.rs1_rdata  = reg2mcap(ir0_op_data2_fwd.d0);
      result.rvfi.rs2_rdata  = reg2mcap(ir0_op_data2_fwd.d1);
      result.rvfi.rs3_rdata  = 0;
      result.rvfi.pc_rdata   = `ISSUER_PATH.ir0_dec.pc;
      result.rvfi.pc_wdata   = get_pc_wdata(0);
      result.rvfi.intr       = `ISSUER_PATH.intr_event;
    end else begin            // IR1
      insn32                 = `ISSUER_PATH.ir1_dec.insn;
      result.pl              = `ISSUER_PATH.ir1_pl_sel;
      result.ir_dec          = `ISSUER_PATH.ir1_dec;
      result.is_ex           = (| `ISSUER_PATH.ir1_pl_sel[4:1]);
      result.is_amo          = 1'b0;        // AMO can only be issued on IR0
      result.rvfi.valid      = `ISSUER_PATH.ir1_issued;     
      result.rvfi.insn       = `ISSUER_PATH.ir1_dec.is_comp ?  `ISSUER_PATH.ir1_dec.c_insn : `ISSUER_PATH.ir1_dec.insn;
      result.rvfi.trap       = 1'b0;    // trap can only happen on IR0
      result.rvfi.rs1_addr   = `ISSUER_PATH.ir1_dec.rs1;
      result.rvfi.rs2_addr   = `ISSUER_PATH.ir1_dec.rs2;
      result.rvfi.rs3_addr   = 0;
      result.rvfi.rs1_rdata  = reg2mcap(ir1_op_data2_fwd.d0);
      result.rvfi.rs2_rdata  = reg2mcap(ir1_op_data2_fwd.d1);
      result.rvfi.rs3_rdata  = 0;
      result.rvfi.pc_rdata   = `ISSUER_PATH.ir1_dec.pc;
      result.rvfi.pc_wdata   = get_pc_wdata(1);
    end

    opcode                 = opcode_e'(insn32[6:0]);

    result.rvfi.mem_rmask = 0;
    result.rvfi.mem_wmask = 0;

    if (opcode == OPCODE_LOAD) begin
      if (insn32[13:12] == 2'b00) 
        result.rvfi.mem_rmask = 4'b0001;        // byte
      else if  (insn32[13:12] == 2'b01)
        result.rvfi.mem_rmask = 4'b0011;        // half word 
      else
        result.rvfi.mem_rmask = 4'b1111;        // word 
    end else if (opcode == OPCODE_STORE) begin   
      if (insn32[13:12] == 2'b00) 
        result.rvfi.mem_wmask = 4'b0001;        // byte
      else if  (insn32[13:12] == 2'b01)
        result.rvfi.mem_wmask = 4'b0011;        // half word 
      else
        result.rvfi.mem_wmask = 4'b1111;        // word 
    end else if (opcode == OPCODE_AMO) begin
      if (insn32[31:27] == 5'h2)
        result.rvfi.mem_rmask = 4'b1111;        // LR.w
      else if (insn32[31:27] == 5'h3)
        result.rvfi.mem_wmask = 4'b1111;        // SC.w
    end        

    // fill later at the committer side
    result.rvfi.rd_addr    = 0;
    result.rvfi.rd_wdata   = 0;
    result.rvfi.mem_addr   = 0;
    result.rvfi.mem_wdata  = 0;
    result.rvfi.mem_rdata  = 0;
    result.rvfi.mem_is_cap = 1'b0;

    return result;
  endfunction

  function automatic instr_trace_t fill_cmt_info (instr_trace_t instr_in, logic is_cmt0, logic amo_state);
    instr_trace_t result;

    logic            is_load, is_sc;
    logic [MemW-1:0] mem_wdata;
    logic [RegW-1:0] reg_wdata;
    logic [31:0]     mem_addr;
    logic [2:0]      rf_we_vec;
    logic            rf_we, load_waddr_conflict;
    logic [RegW-1:0] tr0, tr1;
    

    result = instr_in;

    is_load    = `TOP_PATH.lspl_output.we;
    is_sc      = (instr_in.rvfi.insn[6:0] === OPCODE_AMO) &&  (instr_in.rvfi.insn[31:27] === 5'h3); 

    mem_addr   = `TOP_PATH.ls_pipeline_i.rvfi_mem_addr;
    mem_wdata  = `TOP_PATH.ls_pipeline_i.rvfi_mem_wdata;
    reg_wdata  = `TOP_PATH.lspl_output.wdata;

    // figure out the rf_we status for instr_b
    // RVFI requires to set rd_addr to 0 if rf_we is deasserted (trap, etc)
    // if there is a load address conflict (load result over written by a subsequent isntr 
    // commmited in the same cycle), display the trace as if the reg write from the load
    // actually happened
 
    rf_we_vec  = {`COMMITTER_PATH.rf_we2_o, `COMMITTER_PATH.rf_we1_o, `COMMITTER_PATH.rf_we0_o};

    load_waddr_conflict = `COMMITTER_PATH.load_waddr_conflict;

 
    // fill EX instruction info using pipeline outputs
    if (instr_in.is_ex && ~instr_in.is_amo) begin
      rf_we = instr_in.pl[3] ? (rf_we_vec[2] | load_waddr_conflict) : (is_cmt0 ? rf_we_vec[0] : rf_we_vec[1]);

      if (instr_in.pl[1]) begin
        tr0                    = `TOP_PATH.alupl0_output.wdata;
        result.rvfi.rd_addr    = rf_we ? `TOP_PATH.alupl0_output.waddr : 0;
        result.rvfi.rd_wdata   = reg2mcap(tr0);
        result.rvfi.trap       = instr_in.rvfi.trap | `TOP_PATH.alupl0_output.err;
      end else if (instr_in.pl[2]) begin
        tr0                    = `TOP_PATH.alupl1_output.wdata;
        result.rvfi.rd_addr    = rf_we ? `TOP_PATH.alupl1_output.waddr : 0;
        result.rvfi.rd_wdata   = reg2mcap(tr0);
        result.rvfi.trap       = instr_in.rvfi.trap | `TOP_PATH.alupl1_output.err;
      end else if (instr_in.pl[3]) begin
        tr0                    = is_load ? reg_wdata : 0;
        result.rvfi.rd_addr    = rf_we ? `TOP_PATH.lspl_output.waddr : 0;
        result.rvfi.rd_wdata   = reg2mcap(tr0);
        result.rvfi.mem_addr   = mem_addr;
        result.rvfi.mem_wdata  = (is_load & ~is_sc) ? 0 : mem_wdata;
        result.rvfi.mem_rdata  = reg2mcap(tr0);
        result.rvfi.trap       = instr_in.rvfi.trap | `TOP_PATH.lspl_output.err;
      end else if (instr_in.pl[4]) begin
        tr0                    = `TOP_PATH.multpl_output.wdata;
        result.rvfi.rd_addr    = rf_we ? `TOP_PATH.multpl_output.waddr : 0;
        result.rvfi.rd_wdata   = reg2mcap(tr0);;
        result.rvfi.trap       = instr_in.rvfi.trap | `TOP_PATH.multpl_output.err;
      end
    end else if (instr_in.is_ex) begin   // AMO
      rf_we = rf_we_vec[2];         // AMO load/store are handled serially

      if (amo_state == 0) begin     // AMO is rv32 only, no cap load/store
        result.rvfi.mem_addr   = mem_addr;
        result.rvfi.trap       = instr_in.rvfi.trap | `TOP_PATH.lspl_output.err;
        result.rvfi.rd_addr    = rf_we ? `TOP_PATH.lspl_output.waddr : 0;
        result.rvfi.mem_rmask  = 4'b1111;
        result.rvfi.mem_rdata  = reg_wdata;
        result.rvfi.rd_wdata   = reg_wdata;
      end else if (amo_state == 1) begin
        result.rvfi.mem_wdata  = mem_wdata;    // accumulate from amo_state_0
        result.rvfi.mem_wmask  = 4'b1111;
      end  
    end

    // match ibex RVFI implementation
    if (result.rvfi.rd_addr == 0) result.rvfi.rd_wdata = 0;
    if (result.rvfi.rd_addr == 0) result.rvfi.mem_rdata = 0; 
    if (result.rvfi.trap) result.rvfi.mem_rmask = 0;
    if (result.rvfi.trap) result.rvfi.mem_wmask = 0;


    return result;
  endfunction

  int          trace_file_handle, rvfi_file_handle;

  int unsigned cycle;
  logic        insn_is_compressed;

  function automatic void print_line(input instr_trace_t instr_in);
    string disp_str;

`ifdef TraceDPI
    disp_str = decode_rvfi_instr_dpi(instr_in.rvfi, cheri_pmode_i);
`else
    disp_str = decode_rvfi_instr_vlog(instr_in.rvfi, cheri_pmode_i);
`endif
    //$display("%x: %x", instr_in.rvfi.pc_rdata, instr_in.rvfi.insn);

    $fwrite(trace_file_handle, "%15t\t%d\t%s\n", $time, cycle, disp_str);
  endfunction

  function automatic void print_rvfi_packet(
    input rvfi_t           rvfi,
    input longint unsigned packet_num
  );
    int unsigned rbyte_count;
    int unsigned wbyte_count;

    rbyte_count = $countones(rvfi.mem_rmask);
    wbyte_count = $countones(rvfi.mem_wmask);

    $fdisplay(rvfi_file_handle,"# --- RVFI packet %0d ---", packet_num);
    $fdisplay(rvfi_file_handle,"order     : %0d",                  rvfi.order);
    $fdisplay(rvfi_file_handle,"halt      : 0x%02h",               rvfi.halt);
    $fdisplay(rvfi_file_handle,"trap      : 0x%02h",               rvfi.trap);
    $fdisplay(rvfi_file_handle,"intr      : 0x%02h",               rvfi.intr);
    $fdisplay(rvfi_file_handle,"pc_rdata  : 0x%08h",               rvfi.pc_rdata);
    $fdisplay(rvfi_file_handle,"pc_wdata  : 0x%08h",               rvfi.pc_wdata);
    $fdisplay(rvfi_file_handle,"insn      : 0x%08h",               rvfi.insn);
    $fdisplay(rvfi_file_handle,"rs1       : x%02d  rdata=0x%017h", rvfi.rs1_addr, rvfi.rs1_rdata);
    $fdisplay(rvfi_file_handle,"rs1       : x%02d  rdata=0x%017h", rvfi.rs2_addr, rvfi.rs2_rdata);
    $fdisplay(rvfi_file_handle,"rd        : x%02d  wdata=0x%017h", rvfi.rd_addr,  rvfi.rd_wdata);
    $fdisplay(rvfi_file_handle,"mem_addr  : 0x%08h",              rvfi.mem_addr);
    $fdisplay(rvfi_file_handle,"mem_rmask : 0b%08b (%0d byte(s))", rvfi.mem_rmask, rbyte_count);
    $fdisplay(rvfi_file_handle,"mem_rdata : 0x%017h",              
                              ((rvfi.mem_rmask == 0) ? '0 : rvfi.mem_rdata));
    $fdisplay(rvfi_file_handle,"mem_wmask : 0b%08b (%0d byte(s))", rvfi.mem_wmask, wbyte_count);
    $fdisplay(rvfi_file_handle,"mem_wdata : 0x%017h",               
                              ((rvfi.mem_wmask == 0) ? '0 : rvfi.mem_wdata)); 
    $fdisplay(rvfi_file_handle,"");               
        
  endfunction

  // case 0: normal ex/commit
  // case 1: branch. ir_rdy, don't go to ex/commit.
  // case 2: jal. ir_rdy, set pc, also go to ex/commit
  // case 3: issue side error (illegal, fetch errs). no ir_rdy. directly flush IF

  typedef enum logic [1:0] {
    AMO_T_IDLE,
    AMO_T_WAIT0,
    AMO_T_WAIT1
  } amo_state_e;


  instr_trace_t instr_trace_fifo[16];
  logic [3:0]   wr_ptr;
  logic [3:0]   rd_ptr, rd_ptr_nxt;

  instr_trace_t [1:0] issued_instr;
  instr_trace_t       amo_instr_q;
  
  logic [1:0]      cmt_good;
  logic            cmt_flush;
  logic [4:0]      cmt_pl0, cmt_pl1;
  logic [31:0]     cmt_pc0, cmt_pc1;
  logic            issue_cmplx;
  amo_state_e      amo_state;

  logic [15:0]     ex_flag, is_cmt0;

  assign cmt_pl0     = `TOP_PATH.sbdfifo_rdata0.pl;
  assign cmt_pl1     = `TOP_PATH.sbdfifo_rdata1.pl;
  assign cmt_pc0     = `TOP_PATH.sbdfifo_rdata0.pc;
  assign cmt_pc1     = `TOP_PATH.sbdfifo_rdata1.pc;

  // note in committer if instr0 is erred we still dequeue instr1 from SBD fifo but won't write regfile
  assign cmt_good[0] = `TOP_PATH.sbdfifo_rd_valid[0] & `TOP_PATH.sbdfifo_rd_rdy[0];
  assign cmt_good[1] = `TOP_PATH.sbdfifo_rd_valid[1] & `TOP_PATH.sbdfifo_rd_rdy[1] & ~`COMMITTER_PATH.instr_err[0];

  assign issue_cmplx = `ISSUER_PATH.cmplx_instr_start_o;

  assign cmt_flush   = `TOP_PATH.cmt_flush;

  // for some reason in VCS the following concurrent assignments doesn't work, have to use always_comb
  // assign  issued_instr[0] =  get_trace_issued(0);
  // assign  issued_instr[1] =  get_trace_issued(1);
  always_comb begin
    issued_instr[0] =  get_trace_issued(0);
    issued_instr[1] =  get_trace_issued(1);
  end

  always_comb begin
    int   ex_cnt, cmt_cnt;
    logic rd_flag;

    rd_ptr_nxt = rd_ptr;
    is_cmt0    = 16'h0;
    ex_cnt     = 0;
    cmt_cnt    = cmt_good[1] ? 2 : (cmt_good[0] ? 1 : 0);
    
    for (int i = 0; i < 16; i++) begin
      ex_flag[i] = instr_trace_fifo[i].is_ex;
    end

    for (int i = rd_ptr; i != wr_ptr; i = (i+1) %16) begin
      if (ex_flag[i]) ex_cnt = ex_cnt + 1;
      rd_flag    = (ex_cnt <= cmt_cnt) ? 1'b1 : 1'b0;
      rd_ptr_nxt = rd_ptr_nxt + rd_flag;
      is_cmt0[i] = ex_flag[i] && (ex_cnt <= 1);
    end
    
  end

  //
  // writing issued instructions into FIFO, read committed instructions out
  //
  int unsigned rvfi_pkt_cnt;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      wr_ptr       <= '0;
      rd_ptr       <= '0;
      amo_state    <= AMO_T_IDLE;  
      rvfi_pkt_cnt <= 0;
      for (int i = 0; i < 16; i++) instr_trace_fifo [i] <= '0;  // not really necessary ??
    end else begin
      int unsigned nxt_rvfi_pkt_cnt;

      if (cmt_flush) begin
        wr_ptr <= 0;
      end else if (~issue_cmplx & issued_instr[0].rvfi.valid & issued_instr[1].rvfi.valid) begin
        wr_ptr <= wr_ptr + 2;
        instr_trace_fifo[wr_ptr]        <= issued_instr[0];
        instr_trace_fifo[(wr_ptr+1)%16] <= issued_instr[1];
      end else if (~issue_cmplx & issued_instr[0].rvfi.valid) begin
        wr_ptr <= wr_ptr + 1;
        instr_trace_fifo[wr_ptr]        <= issued_instr[0];
      end 

      if (cmt_flush) 
        rd_ptr <= 0;
      else
        rd_ptr <= rd_ptr_nxt;

      nxt_rvfi_pkt_cnt = rvfi_pkt_cnt;

      for (int i = rd_ptr; i != rd_ptr_nxt; i = (i+1) %16) begin
        if (~instr_trace_fifo[i].is_amo) begin
          instr_trace_t instr_tmp;
          instr_tmp = fill_cmt_info(instr_trace_fifo[i], is_cmt0[i], 1'b0);
          print_line (instr_tmp);
          if (RvfiDumpEn) print_rvfi_packet(instr_tmp.rvfi, nxt_rvfi_pkt_cnt);
          nxt_rvfi_pkt_cnt += 1;
        end
      end

      if (issue_cmplx) begin
        // complex case is serialized and handled separatedly
        amo_state   <= AMO_T_WAIT0;
        amo_instr_q <=  issued_instr[0];
      end else if ((amo_state == AMO_T_WAIT0) && cmt_good[0]) begin
        amo_state   <= AMO_T_WAIT1;
        amo_instr_q <= fill_cmt_info(amo_instr_q, 1'b1, 1'b0);
      end else if ((amo_state == AMO_T_WAIT1) && cmt_good[0]) begin
        instr_trace_t instr_tmp;
        amo_state   <= AMO_T_IDLE;
        instr_tmp    = fill_cmt_info(amo_instr_q, 1'b1, 1'b1);
        print_line (instr_tmp);
        if (RvfiDumpEn) print_rvfi_packet(instr_tmp.rvfi, nxt_rvfi_pkt_cnt);
        nxt_rvfi_pkt_cnt += 1;
      end

      rvfi_pkt_cnt <= nxt_rvfi_pkt_cnt;
    end
  end

  // Data items accessed during this instruction

  initial begin
    $display("%m: Writing execution trace to %s", TraceLogFile);
    trace_file_handle = $fopen(TraceLogFile, "w");
    $fwrite(trace_file_handle,
            "Time\t\t\tCycle\tPC\t\tInsn\tDecoded instruction\tRegister and memory contents\n");
    if (RvfiDumpEn) begin
      $display("%m: Writing rvfi trace to %s", RvfiLogFile);
      rvfi_file_handle = $fopen(RvfiLogFile, "w");
    end
  end

  // cycle counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle <= 0;
    end else begin
      cycle <= cycle + 1;
    end
  end

  // close output file for writing
  final begin
    if (trace_file_handle != 32'h0) begin
      $fclose(trace_file_handle);
    end
    if (rvfi_file_handle != 32'h0) begin
      $fclose(rvfi_file_handle);
    end
  end

// synthesis translate_on



endmodule
