// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Branch Predictor
//
module branch_predict import super_pkg::*; #(
  parameter int unsigned BhtSize    = 16,
  parameter int unsigned JtbSize    = 4,
  parameter bit          UseBtb     = 1'b1, 
  parameter bit          InstrBufEn = 1'b0
) (
  input  logic                clk_i,
  input  logic                rst_ni,

  input  logic                pdt_en_i,
  input  logic [31:0]         tbl_rst_val_i,

  // control signals
  input  logic                ex_bp_init_i,
  input  ex_bp_info_t         ex_bp_info_i, 

  // from instr mem interface
  input  logic                instr_gnt_i,          

  // to IF
  output logic                predict_pc_set_o,
  output logic [31:0]         predict_pc_target_o,    // PC target (after ibuf)
  output logic [31:0]         predict_br_target_o,    // actual branch target
  output logic                predict_ibuf_hit_o,

  // interface to prefetcher
  input  logic [1:0]          fetch_valid_i,
  input  ir_reg_t             fetch_instr0_i, 
  input  ir_reg_t             fetch_instr1_i,
  input  logic [31:0]         instr1_pc_spec0_i,
  input  logic [31:0]         instr1_pc_spec1_i,

  // interface to IR
  input  logic [1:0]          ds_rdy_i,
  output logic [1:0]          pdt_valid_o,
  output ir_reg_t             pdt_instr0_o, 
  output ir_reg_t             pdt_instr1_o
);

  localparam int unsigned BhtAW = $clog2(BhtSize);
  localparam int unsigned JtbAW = $clog2(JtbSize);
  localparam int unsigned BhtLo = 1;
  localparam int unsigned BhtHi = BhtLo + BhtAW -1;
  localparam int unsigned JtbLo = 1;
  localparam int unsigned JtbHi = JtbLo + JtbAW -1;

  // bit 1: NT(1)/T(0), bit 0: Weak(1)/Strong(0)
  typedef enum integer {
    StrongT = 0,       
    WeakT   = 1,
    WeakN   = 3,
    StrongN = 2
  } bht_e;

  typedef struct packed {
    logic         valid;
    logic [31:0]  target;
  } btb_t;

  function automatic btb_t dec_target(ir_reg_t instr_i);
    btb_t        result;
    logic [31:0] offset, insn32, imm_j_type, imm_b_type;
    logic [15:0] insn16;

    insn16 = instr_i.insn[15:0];

    if (instr_i.is_branch && (instr_i.insn[1:0] == 2'b01) && (instr_i.insn[15:14] == 2'b11))
      // C1, c.beqz, c.bnez
      insn32 = {{4 {insn16[12]}}, insn16[6:5], insn16[2], 5'b0, 2'b01,
                insn16[9:7], 2'b00, insn16[13], insn16[11:10], insn16[4:3],
                insn16[12], {OPCODE_BRANCH}};
    else if (instr_i.is_jal && (instr_i.insn[1:0] == 2'b01) && (instr_i.insn[14:13] == 2'b01))
      // C1, c.jal, c.j
      insn32 = {insn16[12], insn16[8], insn16[10:9], insn16[6],
                insn16[7], insn16[2], insn16[11], insn16[5:3],
                {9 {insn16[12]}}, 4'b0, ~insn16[15], {OPCODE_JAL}};
    else
      insn32 = instr_i.insn;

    imm_j_type = { {12{insn32[31]}}, insn32[19:12], insn32[20], insn32[30:21], 1'b0 };
    imm_b_type = { {19{insn32[31]}}, insn32[31], insn32[7], insn32[30:25], insn32[11:8], 1'b0 };

    offset = instr_i.is_branch ? imm_b_type : imm_j_type;

    result.valid = 1'b1;
    result.target = instr_i.pc + offset;

    return result;
  endfunction

  function automatic bht_e update_bht(bht_e cur_bht, logic branch_taken);
    bht_e result;

    result = cur_bht;
    if ((cur_bht == StrongT) && ~branch_taken)
      result = WeakT;
    else if ((cur_bht == WeakT) && branch_taken)
      result = StrongT;
    else if ((cur_bht == WeakT) && ~branch_taken)
      result = WeakN;
    else if ((cur_bht == WeakN) && branch_taken)
      result = WeakT;
    else if ((cur_bht == WeakN) && ~branch_taken)
      result = StrongN;
    else if ((cur_bht == StrongN) && branch_taken)
      result = WeakN;
    
    return result;
  endfunction

  bht_e   bht[BhtSize];
  btb_t   btb[BhtSize];            
  btb_t   jtb[JtbSize];

  logic [1:0] is_branch, is_jal;

  logic [BhtAW-1:0] bht_index0, bht_index1_spec0, bht_index1_spec1;

  bht_e  bht_rdata[2];
  btb_t  btb_rdata[2];
  btb_t  jtb_rdata[2];
  
  logic [1:0]  pdt_branch_go, pdt_jal_go;
  logic [31:0] predict_target, predict_pc;
  logic        use_ibuf;

  ir_reg_t     pdt_instr0, pdt_instr1;
  ir_reg_t     ibuf_instr;
  logic [31:0] ibuf_pc_nxt;
  logic        ibuf_valid;

  assign predict_ibuf_hit_o  = use_ibuf & ds_rdy_i[1];
  assign predict_br_target_o = predict_target;
  assign predict_pc_target_o = predict_pc;

  assign bht_index0       = fetch_instr0_i.pc[BhtHi:BhtLo];
  assign bht_index1_spec0 = instr1_pc_spec0_i[BhtHi:BhtLo];
  assign bht_index1_spec1 = instr1_pc_spec1_i[BhtHi:BhtLo];

  assign is_branch[0] = fetch_instr0_i.is_branch;
  assign is_branch[1] = fetch_instr1_i.is_branch;

  assign is_jal[0] = fetch_instr0_i.is_jal;
  assign is_jal[1] = fetch_instr1_i.is_jal;

  // update bht table and btb buffer based on information from EX stage only
  logic [JtbAW-1:0] jtb_index0, jtb_index1_spec0, jtb_index1_spec1;
  assign jtb_index0       = fetch_instr0_i.pc[JtbHi:JtbLo];
  assign jtb_index1_spec0 = instr1_pc_spec0_i[JtbHi:JtbLo];
  assign jtb_index1_spec1 = instr1_pc_spec1_i[JtbHi:JtbLo];

  for (genvar i = 0; i < BhtSize; i++) begin : gen_bht
    logic [1:0]  bht_entry_sel;
    logic        ex_branch_taken_muxed;
    logic [31:0] ex_branch_target_muxed;

    assign bht_entry_sel[0] = ex_bp_info_i.is_branch[0] && (ex_bp_info_i.pc0[BhtHi:BhtLo] == i);
    assign bht_entry_sel[1] = ex_bp_info_i.is_branch[1] && (ex_bp_info_i.pc1[BhtHi:BhtLo] == i);
    assign ex_branch_taken_muxed = bht_entry_sel[0] ? ex_bp_info_i.taken[0] : 
                                                      ex_bp_info_i.taken[1];
    assign ex_branch_target_muxed = bht_entry_sel[0] ? ex_bp_info_i.target0 : ex_bp_info_i.target1;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        bht[i] <= WeakT;
        btb[i] <= '{0, 0};
      end else begin
        if (ex_bp_init_i) begin
          btb[i] <= '{0, tbl_rst_val_i};
        end else if (|bht_entry_sel) begin 
          bht[i] <= update_bht(bht[i], ex_branch_taken_muxed);
          if (ex_branch_taken_muxed) btb[i] <= '{1'b1, ex_branch_target_muxed};
        end
      end
    end
  end  // gen_bht

  // update jump target buffer based on information from EX stage only
  for (genvar i = 0; i < JtbSize; i++) begin : gen_jtb
    logic [1:0]  jtb_entry_sel;
    logic [31:0] ex_jump_target_muxed;

    assign jtb_entry_sel[0] = ex_bp_info_i.is_jal[0] && (ex_bp_info_i.pc0[JtbHi:JtbLo] == i);
    assign jtb_entry_sel[1] = ex_bp_info_i.is_jal[1] && (ex_bp_info_i.pc1[JtbHi:JtbLo] == i);
    assign ex_jump_target_muxed = jtb_entry_sel[0] ? ex_bp_info_i.target0 : ex_bp_info_i.target1;
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        jtb[i] <= '{0, 0};
      end else begin
        if (ex_bp_init_i) 
          jtb[i] <= '{0, tbl_rst_val_i};
        else if (|jtb_entry_sel) 
          jtb[i] <= '{1'b1, ex_jump_target_muxed};
      end
    end
  end  // gen_jtb

    // spec0/spec1 helps timing (otherwise have to wait for adder before indexing table)
  if (UseBtb) begin : gen_btb_read
    assign btb_rdata[0] = btb[bht_index0];
    assign btb_rdata[1] = fetch_instr0_i.is_comp ? btb[bht_index1_spec0] : btb[bht_index1_spec1];

    assign jtb_rdata[0] = jtb[jtb_index0];
    assign jtb_rdata[1] = fetch_instr0_i.is_comp ? jtb[jtb_index1_spec0] : jtb[jtb_index1_spec1];

  end else begin : gen_dec      // use decoded targets directly
    assign btb_rdata[0] = dec_target(fetch_instr0_i);
    assign btb_rdata[1] = dec_target(fetch_instr1_i);
    assign jtb_rdata[0] = btb_rdata[0];
    assign jtb_rdata[1] = btb_rdata[1];
  end  // gen_dec

  // generate prediction decision
  assign bht_rdata[0] = bht[bht_index0];
  assign bht_rdata[1] = fetch_instr0_i.is_comp ? bht[bht_index1_spec0] : bht[bht_index1_spec1];


  // Note we don't really need the valid flag in BTB here (table entry will settle after a
  // short initial period)
  assign pdt_branch_go[0] = is_branch[0] && ~bht_rdata[0][1];
  assign pdt_branch_go[1] = is_branch[1] && ~bht_rdata[1][1];

  assign pdt_jal_go[0] = is_jal[0];
  assign pdt_jal_go[1] = is_jal[1];

  assign predict_pc_set_o = pdt_en_i &
                            ((fetch_valid_i[0] & ds_rdy_i[0] & (pdt_branch_go[0] | pdt_jal_go[0])) ||
                             (fetch_valid_i[1] & ds_rdy_i[1] & (pdt_branch_go[1] | pdt_jal_go[1]))); 

  assign pdt_valid_o[0] = fetch_valid_i[0];
  assign pdt_valid_o[1] = pdt_en_i ? (use_ibuf | (fetch_valid_i[1] & ~(pdt_branch_go[0]| pdt_jal_go[0]))) :
                          fetch_valid_i[1];

  // can only select ibuf_pc_nxt if downstream is ready to accept instr1
  assign predict_pc    = pdt_en_i ? ((use_ibuf & ds_rdy_i[1])? ibuf_pc_nxt : predict_target) : 32'h0;
  assign pdt_instr0_o  = pdt_en_i ? pdt_instr0 : fetch_instr0_i;
  assign pdt_instr1_o  = pdt_en_i ? (use_ibuf ? ibuf_instr : pdt_instr1) : fetch_instr1_i;

  // generate output based on valdi/rdy status and pass on to next pipe stages
  always_comb begin
    pdt_instr0 = fetch_instr0_i;
    pdt_instr1 = fetch_instr1_i;

    pdt_instr0.ptaken  = 1'b0;
    pdt_instr0.ptarget = 32'h0;

    pdt_instr1.ptaken  = 1'b0;
    pdt_instr1.ptarget = 32'h0;

    // predict_target = btb_rdata[0].target;

    if (pdt_branch_go[0])
      predict_target     = btb_rdata[0].target;
    else if (pdt_jal_go[0]) 
      predict_target     = jtb_rdata[0].target;
    else if (pdt_branch_go[1])
      predict_target     = btb_rdata[1].target;
    else
      predict_target     = jtb_rdata[1].target;

    if (pdt_branch_go[0]) begin
      pdt_instr0.ptaken  = 1'b1;
      pdt_instr0.ptarget = btb_rdata[0].target;
    end else if (pdt_jal_go[0]) begin
      pdt_instr0.ptaken  = 1'b1;
      pdt_instr0.ptarget = jtb_rdata[0].target;
    end else if (pdt_branch_go[1]) begin
      pdt_instr1.ptaken  = 1'b1;
      pdt_instr1.ptarget = btb_rdata[1].target;
    end else if (pdt_jal_go[1]) begin 
      pdt_instr1.ptaken  = 1'b1;
      pdt_instr1.ptarget = jtb_rdata[1].target;
    end
  end


  // 
  //  Single instruction buffer/cache for branch target
  //

  // We may use either the branch target or the PC of then branching instructions as the
  // Ibuf tag (the latter has better timing results). 
  // However, if we use the PC of branching instruction as IBUF tags, must make sure we 
  // also use computed branch targets (not BTB). Otherwise IBUF won't work since BTB is
  // not uniquely mapped.
  //
  localparam bit IbufUseTarget = UseBtb;  

  if (InstrBufEn) begin : gen_ibuf
    logic [31:0] ibuf_tag, lookup_tag;
    logic [31:0] ibuf_tag_q, update_tag_q, target_q;
    logic        update_req, update_st, update_resp, update_valid; 

    assign lookup_tag   = IbufUseTarget ? predict_target : fetch_instr0_i.pc;
    assign ibuf_tag     = IbufUseTarget ? ibuf_instr.pc : ibuf_tag_q;
                        
    assign use_ibuf     = ibuf_valid & pdt_branch_go[0] & (lookup_tag == ibuf_tag);
    assign update_req   = IbufUseTarget ? (pdt_branch_go[0] & ~use_ibuf) :
                          (pdt_branch_go[0] & ~(use_ibuf & ds_rdy_i[1]));
    assign update_resp  = update_st & fetch_valid_i[0];
    assign update_valid = IbufUseTarget ? 1'b1 : (fetch_instr0_i.pc == target_q);

    always_ff @(posedge clk_i or negedge rst_ni) begin
       if (!rst_ni) begin
         ibuf_instr     <= NULL_IR_REG;
         ibuf_valid     <= 1'b0;
         update_st      <= 1'b0;
         ibuf_pc_nxt    <= 32'h0;
         update_tag_q   <= 32'h0;
         ibuf_tag_q     <= 32'h0;
         target_q       <= 32'h0;
       end else begin
         if (~update_st & update_req) begin
          update_st     <= 1'b1;
          update_tag_q  <= fetch_instr0_i.pc;
          target_q      <= predict_target;
         end else if (update_resp) begin
          update_st     <= 1'b0;
         end

         // note when use_ibuf, instruction always predicted as NOT taken since ibuf_instr
         // is from fetch_instr. this is the correct behavior since IBUF is after BP decision.
         // needs FV? QQQ
         if (update_resp & update_valid) begin
           ibuf_valid  <= 1'b1;
           ibuf_tag_q  <= update_tag_q;
           ibuf_instr  <= fetch_instr0_i;   
           ibuf_pc_nxt <= fetch_instr0_i.pc + (fetch_instr0_i.is_comp ? 2 : 4);
         end
       end
    end
  end else begin : gen_no_instr_buffer
    assign use_ibuf    = 1'b0;
    assign ibuf_instr  = NULL_IR_REG;
    assign ibuf_valid  = 1'b0;
  end

endmodule
