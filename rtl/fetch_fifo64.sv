// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Fetch Fifo for 32 bit memory interface
 *
 * input port: send address and data to the FIFO
 * clear_i clears the FIFO for the following cycle, including any new request
 */

module fetch_fifo64 import super_pkg::*; #(
  parameter int unsigned NUM_REQS       = 2,
  parameter bit          UnalignedFetch = 1'b1,
  parameter bit          AltEnable      = 1'b0
) (
  input  logic                clk_i,
  input  logic                rst_ni,

  // configuration
  input  logic                cheri_const_fetch_i,

  // control signals
  // clears the contents of the FIFO. 
  // apply_alt/set_alt implies clear_i, but cancel_alt is standalone
  input  logic                clear_i,   
  input  logic [31:0]         in_addr_i,

  input  ex_alt_ctrl_t        ex_alt_ctrl_i,
  input  logic                alloc_alt_i, 
  input  logic                bp_instr0_i,
  output logic                apply_alt_ok_o,
  output logic [31:0]         alt_nxt_addr_o,   // to instruction fetch address generation logic
  output logic                alt_has_free_o,   // status signal to branch predictor
  output logic [1:0]          alt_free_id_o,     

  output logic [NUM_REQS-1:0] busy_o,

  // input from memory fetch side
  input  logic                in_valid_i,
  input  logic                in_valid_alt_i,
  input  logic [63:0]         in_rdata_i,
  input  logic                in_err_i,
  input  logic                in_rdata_align64_i,

  // aligned instruction output
  input  logic [1:0]          out_ready_i,
  output logic [1:0]          out_valid_o,

  output ir_reg_t             out_instr0_o, 
  output ir_reg_t             out_instr1_o,
  output logic [31:0]         out_instr1_pc_spec0_o,
  output logic [31:0]         out_instr1_pc_spec1_o
);

  // deeper FIFOs to accomodate ALT for now
  localparam int unsigned DEPTH  = AltEnable ? NUM_REQS+4 : NUM_REQS+1; 
  localparam int unsigned NumAlt = 2;
  localparam bit          AltUpdateEn = 1'b0;

  function automatic logic dec_branch(logic [15:0] insn16);
    logic result;
 
    if ((insn16[1:0] == 2'b01) && (insn16[15:14] == 2'b11))
      result = 1'b1;         // C1, c.beqz, c.bnez
    else if (insn16[6:0] == OPCODE_BRANCH)
      result = 1'b1;
    else
      result = 1'b0;
 
    return result;
  endfunction

  function automatic logic dec_jal(logic [15:0] insn16);
    logic result;

    if ((insn16[1:0] == 2'b01) && (insn16[14:13] == 2'b01))
      result = 1'b1;          // C1, c.jal, c.j
    else if (insn16[6:0] == OPCODE_JAL)
      result = 1'b1;
    else
      result = 1'b0;

    return result;
  endfunction

  function automatic logic [1:0] find_zero(logic [3:0] vec);
    logic [1:0] result;
    logic [3:0] nvec;

    case (NumAlt) 
      1: nvec = ~{3'b111, vec[0]};
      2: nvec = ~{2'b11, vec[1:0]};
      3: nvec = ~{1'b1, vec[2:0]};
      4: nvec = ~{vec[3:0]};
      default: nvec = ~vec;
    endcase
    result = { (nvec[2] | nvec[3]),  (nvec[3] | (~nvec[2] & nvec[1])) };
    return result;
  endfunction

  // index 0 is used for output
  logic [DEPTH-1:0] [64:0]  rdata_d,   rdata_q;
  logic [DEPTH-1:0]         err_d,     err_q;
  logic [DEPTH-1:0]         valid_d,   valid_q;
  logic [DEPTH-1:0]         lowest_free_entry;
  logic [DEPTH-1:0]         valid_pushed, valid_popped;
  logic [DEPTH-1:0]         entry_en;

  logic                     pop_fifo, pop_alt;
  //logic                     err,   err_unaligned, err_plus2;

  logic [31:1]              instr_addr_next;
  logic [31:1]              instr_addr_d, instr_addr_q;
  logic [31:1]              instr_addrp2_q, instr_addrp4_q;
  logic                     instr_addr_en;
  logic                     unused_addr_in;

  logic [1:0]   instr_xfr;
  logic [7:0]   comp_flag, branch_flag, jal_flag;
  logic [1:0]   instr_addr16;
  logic [127:0] rdata128;
  logic [2:0]   addr16_incr;
  logic [1:0]   out_is_comp, out_is_branch, out_is_jal;
  logic [31:0]  out_addr0;
  logic [31:0]  out_rdata0;
  logic [31:0]  out_addr1;
  logic [31:0]  out_rdata1;
  logic         rdata_align64;
  logic [1:0]   fetch_err;

  // ALT logic outputs
  logic         apply_alt, alloc_alt, flush_alt;
  logic [1:0]   cancel_alt;

  logic [DEPTH-1:0][63:0] alt_rd_rdata;
  logic [DEPTH-1:0]       alt_rd_valid, alt_rd_err;
  logic [31:0]            alt_rd_nxt_addr;

  logic [DEPTH-1:0] valid_alt_popped;
  logic [DEPTH-1:0] [63:0]  rdata_alt_d;
  logic [DEPTH-1:0]         err_alt_d;

  /////////////////
  // Output port //
  /////////////////
  assign out_instr0_o.insn      = out_rdata0;
  assign out_instr0_o.pc        = out_addr0;
  assign out_instr0_o.is_comp   = out_is_comp[0];
  assign out_instr0_o.is_branch = out_is_branch[0];
  assign out_instr0_o.is_jal    = out_is_jal[0];
  assign out_instr0_o.errs      = ir_errs_t'({4'h0, fetch_err[0]});

  assign out_instr0_o.ptaken    = 1'b0;
  assign out_instr0_o.ptarget   = 32'h0;

  assign out_instr1_o.insn      = out_rdata1;
  assign out_instr1_o.pc        = out_addr1;
  assign out_instr1_o.is_comp   = out_is_comp[1];
  assign out_instr1_o.is_branch = out_is_branch[1];
  assign out_instr1_o.is_jal    = out_is_jal[1];
  assign out_instr1_o.errs      = ir_errs_t'({4'h0, fetch_err[1]});

  assign out_instr1_o.ptaken    = 1'b0;
  assign out_instr1_o.ptarget   = 32'h0;


  ////////////////////////////////////////
  // Instruction aligner (if unaligned) //
  ////////////////////////////////////////
  
  for (genvar i = 0; i < 8; i++) begin : gen_comp_flag
    assign comp_flag[i]   = (rdata128[i*16+:2] != 2'b11);
    assign branch_flag[i] = dec_branch(rdata128[i*16+:16]);  // pre-decode to help timing
    assign jal_flag[i]    = dec_jal(rdata128[i*16+:16]);
  end

  // rdata 128 can be either
  // {dont_care,  in_rdata_i}, if valid_q[0] == 0, in_valid_i == 1
  // {in_rdata_i, data_q[0]},  if valid_q[0] == 1, valid_q[1] == 0, in_valid_i == 1
  // {data_q[1],  data_q[0]},  if valid_q[0] == 1, valid_q[1] == 1
  // -- note valid_q[1] == 1 implies valid_q[0] == 1

  assign rdata128[63:0]   = valid_q[0] ? rdata_q[0][63:0] : in_rdata_i[63:0];
  assign rdata128[127:64] = valid_q[1] ? rdata_q[1][63:0] : in_rdata_i[63:0];

  assign rdata_align64   = valid_q[0] ? rdata_q[0][64] : in_rdata_align64_i;
  assign instr_addr16    = (UnalignedFetch && ~rdata_align64) ? {~instr_addr_q[2], instr_addr_q[1]} : 
                           instr_addr_q[2:1];

  assign instr_xfr = out_valid_o & out_ready_i;

  logic first_word_err, second_word_err;

  always_comb begin

    // after 1st word err, delination is lost so we really only need to send one instruction out 
    // so that the EX stages can trap properly.
    first_word_err  = 0;
    second_word_err = 0;

    // QQQ note we don't completely handle fetch_err for unalignedFetch case here yet
    if ((~in_valid_i & ~valid_q[1] & valid_q[0]) | (in_valid_i & ~valid_q[0])) begin   // 1 entry available
      first_word_err = (~valid_q[0] & in_err_i) || (valid_q[0] & err_q[0]);

      // cheri_const_fetch: if current fetch_pc is at bit 48, always assume it's 32-bit regardless of comp_flag, 
      // and wait for the next word before popping the instruction

      if (first_word_err) 
        out_valid_o = 2'b01;
      else if (instr_addr16 == 2'h0) 
        out_valid_o = 2'b11;
      else if ((instr_addr16 == 2'h1) && (comp_flag[1] | comp_flag[3])) 
        out_valid_o = 2'b11;
      else if (instr_addr16 == 2'h1) 
        out_valid_o = 2'b01;
      else if ((instr_addr16 == 2'h2) && comp_flag[2] && comp_flag[3]) 
        out_valid_o = 2'b11;
      else if (instr_addr16 == 2'h2)
        out_valid_o = 2'b01;
      else if ((instr_addr16 == 2'h3) && comp_flag[3] && ~cheri_const_fetch_i) 
        out_valid_o = 2'b01;
      else 
        out_valid_o = 2'b00;

      if (first_word_err) 
        fetch_err = 2'b01;
      else
        fetch_err = 2'b00;

    end else if ((in_valid_i & valid_q[0]) | valid_q[1]) begin       // more than 1 entry available
      first_word_err  = err_q[0];
      second_word_err = valid_q[1] ? err_q[1] : in_err_i;

      out_valid_o = 2'b11;

      if (first_word_err) 
        fetch_err  = 2'b11;
      else if (second_word_err && (instr_addr16 == 2'h3) && ~comp_flag[3])
        fetch_err = 2'b01;   // 32-bit instruction stradles word boundary
      else
        fetch_err = 2'b00;
    end else begin
      out_valid_o = 2'b00;
      fetch_err   = 2'b00;
    end

    if (instr_addr16 == 2'h0) begin
      out_rdata0    = rdata128[31:0];
      out_rdata1    = comp_flag[0] ? rdata128[47:16] : rdata128[63:32]; 
      out_is_comp   = {(comp_flag[0] ? comp_flag[1] : comp_flag[2]), comp_flag[0]};
      out_is_branch = {(comp_flag[0] ? branch_flag[1] : branch_flag[2]), branch_flag[0]};
      out_is_jal    = {(comp_flag[0] ? jal_flag[1] : jal_flag[2]), jal_flag[0]};
    end else if (instr_addr16 == 2'h1) begin
      out_rdata0    = rdata128[47:16];
      out_rdata1    = comp_flag[1] ? rdata128[63:32] : rdata128[79:48];
      out_is_comp   = {(comp_flag[1] ? comp_flag[2] : comp_flag[3]), comp_flag[1]};
      out_is_branch = {(comp_flag[1] ? branch_flag[2] : branch_flag[3]), branch_flag[1]};
      out_is_jal    = {(comp_flag[1] ? jal_flag[2] : jal_flag[3]), jal_flag[1]};
    end else if (instr_addr16 == 2'h2) begin
      out_rdata0    = rdata128[63:32];
      out_rdata1    = comp_flag[2] ? rdata128[79:48] : rdata128[95:64];
      out_is_comp   = {(comp_flag[2] ? comp_flag[3] : comp_flag[4]), comp_flag[2]};
      out_is_branch = {(comp_flag[2] ? branch_flag[3] : branch_flag[4]), branch_flag[2]};
      out_is_jal    = {(comp_flag[2] ? jal_flag[3] : jal_flag[4]), jal_flag[2]};
    end else begin
      out_rdata0    = rdata128[79:48];
      out_rdata1    = comp_flag[3] ? rdata128[95:64] : rdata128[111:80];
      out_is_comp   = {(comp_flag[3] ? comp_flag[4] : comp_flag[5]), comp_flag[3]};
      out_is_branch = {(comp_flag[3] ? branch_flag[4] : branch_flag[5]), branch_flag[3]};
      out_is_jal    = {(comp_flag[3] ? jal_flag[4] : jal_flag[5]), jal_flag[3]};
    end

    // only increase outgoing pc if instruction transferred (valid & ready)
    if ((instr_xfr == 2'b01) && out_is_comp[0]) begin
      addr16_incr = 1;
      pop_fifo    = (instr_addr16 == 2'h3);
    end else if (((instr_xfr == 2'b01) && ~out_is_comp[0]) || ((instr_xfr == 2'b11) && (out_is_comp == 2'b11))) begin
      addr16_incr = 2;
      pop_fifo    = (instr_addr16 == 2'h2) || (instr_addr16 == 2'h3);
    end else if ((instr_xfr == 2'b11) && (out_is_comp == 2'b00)) begin
      addr16_incr = 4;
      pop_fifo    = 1'b1;
    end else if (instr_xfr == 2'b11) begin
      addr16_incr = 3;
      pop_fifo    = (instr_addr16 != 2'h0);
    end else begin
      addr16_incr = 0;
      pop_fifo    = 1'b0;
    end

    // decide how we should create ALT entry and save its data. 
    // If 2 entries are transfered from the main FIFO, but a branch is predicted on instr0, 
    // we should still save the word containing instr1 to ALT
    // QQQ this is equivalent to gating instr_xfr[1] with ~bp_instr0_i, assertion?
    if ((instr_xfr == 2'b11) & bp_instr0_i & out_is_comp[0])
      pop_alt = (instr_addr16 == 2'h3);
    else if ((instr_xfr == 2'b11) & bp_instr0_i & ~out_is_comp[0])
      pop_alt = (instr_addr16 == 2'h2) || (instr_addr16 == 2'h3);
    else
      pop_alt = pop_fifo;
  end

  /////////////////////////
  // Instruction address //
  /////////////////////////

  // Update the address on branches and every time either 1 or 2 instruction is driven 
  assign instr_addr_en = clear_i | (|(out_ready_i & out_valid_o)); 

  // Increment the address by two every time a compressed instruction is popped
  assign instr_addr_next = instr_addr_q[31:1] + addr16_incr;

  assign instr_addr_d = clear_i ? in_addr_i[31:1] : instr_addr_next;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_addr_q   <= '0;
    end else if (instr_addr_en) begin
      instr_addr_q   <= instr_addr_d;
    end
  end

  // parallelizing/precompute adders to help timing a bit..
  logic [31:1] instr_addrp2_d, instr_addrp4_d;
  assign instr_addrp2_d = clear_i ? (in_addr_i[31:1] + 1) : (instr_addr_next + 1);
  assign instr_addrp4_d = clear_i ? (in_addr_i[31:1] + 2) : (instr_addr_next + 2);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_addrp2_q <= '0;
      instr_addrp4_q <= '0;
    end else if (instr_addr_en) begin
      instr_addrp2_q <= instr_addrp2_d;
      instr_addrp4_q <= instr_addrp4_d;
    end
  end

  // Output PC of current instruction
  assign out_addr0  = {instr_addr_q, 1'b0};
  assign out_addr1  = {(out_is_comp[0] ? instr_addrp2_q : instr_addrp4_q), 1'b0} ;

  assign out_instr1_pc_spec0_o = {instr_addrp2_q, 1'b0};
  assign out_instr1_pc_spec1_o = {instr_addrp4_q, 1'b0};

  // The LSB of the address is unused, since all addresses are halfword aligned
  assign unused_addr_in = in_addr_i[0];

  /////////////////
  // FIFO status //
  /////////////////

  // Indicate the fill level of fifo-entries. This is used to determine when a new request can be
  // made on the bus. The prefetch buffer only needs to know about the upper entries which overlap
  // with NUM_REQS.
  assign busy_o = valid_q[DEPTH-1:DEPTH-NUM_REQS];

  /////////////////////
  // FIFO management //
  /////////////////////

  // Since an entry can contain unaligned instructions, popping an entry can leave the entry valid

  for (genvar i = 0; i < (DEPTH - 1); i++) begin : g_fifo_next
    // Calculate lowest free entry (write pointer)
    if (i == 0) begin : g_ent0
      assign lowest_free_entry[i] = ~valid_q[i];
    end else begin : g_ent_others
      assign lowest_free_entry[i] = ~valid_q[i] & valid_q[i-1];
    end

    // An entry is set when an incoming request chooses the lowest available entry
    assign valid_pushed[i] = (in_valid_i & lowest_free_entry[i]) |
                             valid_q[i];
    // Popping the FIFO shifts all entries down
    assign valid_popped[i] = pop_fifo ? valid_pushed[i+1] : valid_pushed[i];

    // All entries are wiped out on a clear
    assign valid_d[i] = ~clear_i ? valid_popped[i] :                  // no clear
                        apply_alt ? alt_rd_valid[i] :                    // clear/aplly alt
                        1'b0;                                         // clear/no alt

    // data flops are enabled if there is new data to shift into it, or
    assign entry_en[i] = (valid_pushed[i+1] & pop_fifo) |
                         // a new request is incoming and this is the lowest free entry
                         (in_valid_i & lowest_free_entry[i] & ~pop_fifo) |
                         apply_alt;

    // take the next entry or the incoming data, or ALT data
    assign rdata_d[i]  = apply_alt ? alt_rd_rdata[i] :
                         valid_q[i+1] ? rdata_q[i+1] : {in_rdata_align64_i, in_rdata_i} ;

    assign err_d[i]    = apply_alt ? alt_rd_err[i] :
                         valid_q[i+1] ? err_q[i+1] : in_err_i;  

    // ALT version of control signals used for SAVE_ALT
    assign valid_alt_popped[i] = pop_alt ? valid_pushed[i+1] : valid_pushed[i];

    assign rdata_alt_d[i] = pop_alt ? (valid_q[i+1] ? rdata_q[i+1] : {in_rdata_align64_i, in_rdata_i}) :
                                      (valid_q[i] ? rdata_q[i] : {in_rdata_align64_i, in_rdata_i}); 
    assign err_alt_d[i]   = pop_alt ? (valid_q[i+1] ? err_q[i+1] : in_err_i) : 
                                      (valid_q[i] ? err_q[i] : in_err_i);
  end

  // The top entry is similar but with simpler muxing
  // note clear_i will clear valid for all main fifo entries, so rdata_d and err_d can be simplified
  assign lowest_free_entry[DEPTH-1] = ~valid_q[DEPTH-1] & valid_q[DEPTH-2];
  assign valid_pushed     [DEPTH-1] = valid_q[DEPTH-1] | (in_valid_i & lowest_free_entry[DEPTH-1]);
  assign valid_popped     [DEPTH-1] = pop_fifo ? 1'b0 : valid_pushed[DEPTH-1];
  assign valid_d [DEPTH-1]          = valid_popped[DEPTH-1] & ~clear_i;
  assign entry_en[DEPTH-1]          = in_valid_i & lowest_free_entry[DEPTH-1] | apply_alt;
  assign rdata_d [DEPTH-1]          = {in_rdata_align64_i, in_rdata_i};
  assign err_d   [DEPTH-1]          = in_err_i; 

  assign valid_alt_popped[DEPTH-1]  = pop_alt ? 1'b0 : valid_pushed[DEPTH-1];
  assign rdata_alt_d     [DEPTH-1]  = {in_rdata_align64_i, in_rdata_i};
  assign err_alt_d       [DEPTH-1]  = in_err_i; 

  ////////////////////
  // FIFO registers //
  ////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= '0;
    end else begin
      valid_q <= valid_d;
    end
  end

  for (genvar i = 0; i < DEPTH; i++) begin : g_fifo_regs
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rdata_q[i] <= '0;
        err_q[i]   <= '0;
      end else if (entry_en[i]) begin
        rdata_q[i] <= rdata_d[i];
        err_q[i]   <= err_d[i];
      end
    end
  end

  //////////////////////
  // ALT data entries //
  //////////////////////

  logic [NumAlt-1:0] alt_status;
  logic [1:0]        alt_apply_id, alt_free_id, alt_update_id;
  logic              updating_alt;
  logic              alt_err_event;;

  // Note that flush_alt == ir_flush. If table entries are invalidated by flushing,
  // all outstanding instructions linked to those table entries (in IR) are also flushed,
  // As such apply_alt will never points to an invali entry in ALT table
  assign flush_alt  = AltEnable & ex_alt_ctrl_i.flush;
  assign apply_alt  = AltEnable & clear_i & ex_alt_ctrl_i.apply;
  assign cancel_alt = AltEnable ? ex_alt_ctrl_i.cancel : 2'b00;
  assign alloc_alt  = AltEnable & clear_i & alloc_alt_i;

  assign alt_has_free_o  =  ~(&alt_status);    // at least one free entry
  assign alt_free_id_o   = alt_free_id;
  assign apply_alt_ok_o  = apply_alt;
  assign alt_nxt_addr_o  = alt_rd_nxt_addr;

  assign alt_apply_id  = ex_alt_ctrl_i.ir_sel ? ex_alt_ctrl_i.id1 : ex_alt_ctrl_i.id0;

  assign alt_err_event = apply_alt & ~(alt_status[alt_apply_id]);

  if (~AltEnable) begin : gen_no_alt

    assign alt_rd_valid    = '0;
    assign alt_rd_rdata    = '0;
    assign alt_rd_err      = '0;
    assign alt_rd_nxt_addr = 32'h0;
    assign alt_status      = '0;
    assign alt_free_id     = '0;

  end else begin : gen_alt

    typedef struct packed {
      logic [31:0]      nxt_addr;            
      logic [2:0][63:0] rdata;
      logic [2:0]       err;
      logic [2:0]       valid;
     } alt_entry_t;

    alt_entry_t [NumAlt-1: 0] alt_table;

    alt_entry_t  alt_rdout;
    logic [31:0] alt_nxt_addr_d;
    logic [2:0]  alt_valid_cnt;
    
    // ALT table read interface
    assign alt_rdout = ex_alt_ctrl_i.ir_sel ? alt_table[ex_alt_ctrl_i.id1] : 
                                              alt_table[ex_alt_ctrl_i.id0];

    assign alt_rd_valid    = alt_rdout.valid;
    assign alt_rd_rdata    = alt_rdout.rdata;
    assign alt_rd_err      = alt_rdout.err;
    assign alt_rd_nxt_addr = alt_rdout.nxt_addr;

    // ALT alloc/update interface
    
    assign alt_free_id    = find_zero(alt_status);
    assign alt_valid_cnt  = valid_alt_popped[2] ? (pop_alt ? 3'h4 : 3'h3) : 
                            valid_alt_popped[1] ? (pop_alt ? 3'h3 : 3'h2) :
                            valid_alt_popped[0] ? (pop_alt ? 3'h2 : 3'h1) : 
                                                  (pop_alt ? 3'h1 : 3'h0) ;

    assign alt_nxt_addr_d = {instr_addr_q[31:3], 3'b000} + {alt_valid_cnt, 3'b000};

    if (AltUpdateEn) begin : gen_alt_update
    // Keep updating the newly created ALT entry with rdata from instr memory
      logic stop_update;
      assign stop_update = (apply_alt && (alt_apply_id == alt_update_id)) ||
                           (cancel_alt[0] && (ex_alt_ctrl_i.id0 == alt_update_id)) ||
                           (cancel_alt[1] && (ex_alt_ctrl_i.id1 == alt_update_id));

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          alt_update_id <= '0;
          updating_alt  <= 1'b0;
        end else begin
          // it's possible to have back-to-back create_ALT actions
          if (alloc_alt) begin
            alt_update_id <= alt_free_id;
            updating_alt  <= 1'b0;
          end else if (in_valid_i | stop_update) begin
          updating_alt  <= 1'b0;
          end
        end 
      end
    end else begin : gen_alt_no_update
      assign updating_alt  = 1'b0;
      assign alt_update_id = 2'b00;
    end

    for (genvar i = 0; i < NumAlt; i++) begin : gen_alt_entries
      logic       alloc_entry, updating_entry, cancel_entry;

      assign cancel_entry = (cancel_alt[0] && (ex_alt_ctrl_i.id0 == i)) || 
                            (cancel_alt[1] && (ex_alt_ctrl_i.id1 == i));  

      assign alloc_entry  = alloc_alt && (alt_free_id == i);

      assign updating_entry = updating_alt & (alt_update_id == i);
         
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          alt_table[i]  <= '{'0, '{'0, '0 ,'0}, '0, '0};
          alt_status[i] <= 1'b0;
        end else begin
          // there could be errs in the later incoming data so we still need to record errs in ALT
          if (flush_alt | cancel_entry)
            alt_status[i] <= 1'b0;
          else if (alloc_entry)
            alt_status[i] <= 1'b1;
         
          // create a new ALT entry by dumping the main FIFO content (including in_rdata)  
          if (alloc_entry) begin 
            alt_table[i].valid    <= valid_alt_popped[2:0];
            alt_table[i].rdata    <= rdata_alt_d[2:0];
            alt_table[i].err      <= err_alt_d[2:0];
            alt_table[i].nxt_addr <= alt_nxt_addr_d;
          end else if (updating_entry & ~(flush_alt | cancel_entry) & 
                       in_valid_alt_i & ~alt_table[i].valid[2]) begin
            // continue update the entry until data from the predicted branch comes in, till the entry is full
            alt_table[i].valid[0] <= 1'b1;  
            alt_table[i].valid[1] <= alt_table[i].valid[0];  
            alt_table[i].valid[2] <= alt_table[i].valid[0] & alt_table[i].valid[1];  
            if (~alt_table[i].valid[0]) begin
              alt_table[i].rdata[0] <= in_rdata_i;
              alt_table[i].err[0]   <= in_err_i;
            end else  if (~alt_table[i].valid[1]) begin
              alt_table[i].rdata[1] <= in_rdata_i;
              alt_table[i].err[1]   <= in_err_i;
            end else begin
              alt_table[i].rdata[2] <= in_rdata_i;
              alt_table[i].err[2]   <= in_err_i;
            end

            alt_table[i].nxt_addr <= alt_table[i].nxt_addr + 8;
          end
        end
      end

    end
  end

endmodule
