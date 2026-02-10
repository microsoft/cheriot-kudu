// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Dual-issue instruction issuer
//
//  ir0 is always the 1st (earlier) instruction. Fifo logic handles switching.
module cmplx_unit import super_pkg::*; import cheri_pkg::*; import csr_pkg::*; # (
  parameter bit          RV32A      = 1'b1
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  // issuer interface
  input  logic             flush_i,
  input  logic             sel_ira_i,
  input  ir_dec_t          ira_dec_i,
  input  ir_dec_t          irb_dec_i,
  input  full_data2_t      ira_full_data2_i,
  input  full_data2_t      irb_full_data2_i,

  input  logic             cmplx_instr_start_i, 
  output logic             cmplx_instr_done_o, 
  output logic             cmplx_sbd_wr_o,
  output sbd_fifo_t        cmplx_sbd_wdata_o,

  // LS pipeline interface
  input logic              lspl_valid_i,
  input pl_out_t           lspl_output_i,
  input  logic             lspl_rdy_i,
  output logic             cmplx_lsu_req_valid_o,
  output lsu_req_info_t    cmplx_lsu_req_info_o
  );

  typedef enum logic [3:0] {
    IDLE        = 4'h0,
    AMO_READ    = 4'h1,
    AMO_WAIT_RD = 4'h2,
    AMO_WRITE   = 4'h3,
    AMO_WAIT_WR = 4'h4
  } cmplx_fsm_e;

  cmplx_fsm_e  cmplx_fsm_ns, cmplx_fsm_cs;

  full_data2_t ir_full_data2_q;
  ir_dec_t     ir_dec_q;
  full_cap_t   cs1_fcap, cs2_fcap;

  logic        instr_is_amo;
  logic [31:0] amo_rdata_q, amo_wdata;


  assign cs1_fcap     = full_cap_t'(ir_full_data2_q.d0);
  assign cs2_fcap     = full_cap_t'(ir_full_data2_q.d1);

  assign instr_is_amo = (ir_dec_q.insn[6:0] == OPCODE_AMO);  // LR/SC are not considered cmplx

  assign cmplx_instr_done_o   = ((cmplx_fsm_cs == AMO_WAIT_RD) & lspl_valid_i & lspl_output_i.err) ||
                                ((cmplx_fsm_cs == AMO_WAIT_WR) & lspl_valid_i);

  assign cmplx_lsu_req_valid_o = ((cmplx_fsm_cs == IDLE) & cmplx_instr_start_i & instr_is_amo) ||
                                 (cmplx_fsm_cs == AMO_READ) || (cmplx_fsm_cs == AMO_WRITE);

  assign cmplx_sbd_wdata_o = '{5'h1 << 3, ir_dec_q.pc};
  assign cmplx_sbd_wr_o    = cmplx_lsu_req_valid_o & lspl_rdy_i;

  assign cmplx_instr_pc_o  = ir_dec_q.pc;

  always_comb begin 
    cmplx_fsm_ns   = cmplx_fsm_cs;

    if (flush_i) begin
      cmplx_fsm_ns  = IDLE; 
    end else begin 
      case (cmplx_fsm_cs)
        IDLE: begin
          if (cmplx_instr_start_i & instr_is_amo & lspl_rdy_i)
            cmplx_fsm_ns = AMO_WAIT_RD;
          else if (cmplx_instr_start_i & instr_is_amo)
            cmplx_fsm_ns = AMO_READ;
        end
        AMO_READ: begin
          if (lspl_rdy_i) 
            cmplx_fsm_ns = AMO_WAIT_RD;
        end
        AMO_WAIT_RD: begin
          if (lspl_valid_i && lspl_output_i.err)
            cmplx_fsm_ns = IDLE;
          else if (lspl_valid_i)
            cmplx_fsm_ns = AMO_WRITE;
        end
        AMO_WRITE: begin
          if (lspl_rdy_i) 
            cmplx_fsm_ns = AMO_WAIT_WR;    
        end
        AMO_WAIT_WR: begin
          if (lspl_valid_i) 
            cmplx_fsm_ns = IDLE;    
          end
        default: ;
      endcase
     end   // if flush
  end  // always

  always_comb begin
    logic [31:0] rs2_val;
    logic min_flag, minu_flag;

    rs2_val = ir_full_data2_q.d1[31:0];

    min_flag  = ($signed(amo_rdata_q) < $signed(rs2_val)) ? 1'b1 : 1'b0;
    minu_flag = (amo_rdata_q < rs2_val) ? 1'b1 : 1'b0;

    case (ir_dec_q.insn[31:27])
      5'h0:  begin      // AMO_OP_ADD;
        amo_wdata = rs2_val + amo_rdata_q; 
      end
      5'h1:  begin      //  AMO_OP_SWAP;
        amo_wdata = rs2_val; 
      end
      5'h4:  begin      //  AMO_OP_XOR;
        amo_wdata = rs2_val ^ amo_rdata_q; 
      end
      5'h8:  begin      //  AMO_OP_OR;
        amo_wdata = rs2_val | amo_rdata_q; 
      end
      5'hc:  begin      //  AMO_OP_AND;
        amo_wdata = rs2_val & amo_rdata_q; 
      end
      5'h10: begin      //  AMO_OP_MIN;
        amo_wdata = min_flag ? amo_rdata_q : rs2_val;
      end
      5'h14: begin      //  AMO_OP_MAX;
        amo_wdata = min_flag ? rs2_val : amo_rdata_q;
      end
      5'h18: begin      //  AMO_OP_MINU;
        amo_wdata = minu_flag ? amo_rdata_q : rs2_val;
      end
      5'h1c: begin      //  AMO_OP_MAXU;ot considered cmplx
        amo_wdata = minu_flag ? rs2_val : amo_rdata_q;
      end
      default: begin    // AMO_OP_SWAP;
      end
    endcase

  end

  always_comb begin
    cmplx_lsu_req_info_o = NULL_LSU_REQ_INFO;
    cmplx_lsu_req_info_o.is_load   = ~(cmplx_fsm_cs == AMO_WRITE);
    cmplx_lsu_req_info_o.rf_we     = ~(cmplx_fsm_cs == AMO_WRITE);
    cmplx_lsu_req_info_o.pc        = ir_dec_q.pc;
    cmplx_lsu_req_info_o.data_type = 2'b00;
    cmplx_lsu_req_info_o.amo_flag  = ~(cmplx_fsm_cs == AMO_WRITE) ? 4'b0100 : 4'b1000;
    cmplx_lsu_req_info_o.addr      = ir_full_data2_q.d0[31:0];   // rs1
    cmplx_lsu_req_info_o.wdata     = amo_wdata;
    cmplx_lsu_req_info_o.rs1       = ir_dec_q.rs1;
    cmplx_lsu_req_info_o.rd        = ir_dec_q.rd;
    cmplx_lsu_req_info_o.cs1_fcap  = cs1_fcap;
    cmplx_lsu_req_info_o.cs2_valid = cs2_fcap.valid;
    cmplx_lsu_req_info_o.cs2_perms = cs2_fcap.perms;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin 
    if (!rst_ni) begin
      cmplx_fsm_cs       <= IDLE;
      ir_full_data2_q    <= full_data2_t'(0);
      ir_dec_q           <= ir_dec_t'(0);
      amo_rdata_q        <= 32'h0;
    end else begin
      cmplx_fsm_cs   <= cmplx_fsm_ns;

      if ((cmplx_fsm_cs == IDLE) && ~cmplx_instr_start_i) begin
        ir_dec_q        <= sel_ira_i ? ira_dec_i : irb_dec_i;
        ir_full_data2_q <= sel_ira_i ? ira_full_data2_i : irb_full_data2_i;
      end

      if ((cmplx_fsm_cs == AMO_WAIT_RD) && lspl_valid_i) begin
        amo_rdata_q  <= lspl_output_i.wdata[31:0];
      end 

    end
  end

endmodule
