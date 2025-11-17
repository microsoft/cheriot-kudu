// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Arithmetic logic unit
 */
module rv32_alu import super_pkg::*; #(
  parameter bit  RV32B             = 1'b1
) (
  input  alu_op_e      operator_i,
  input  op_a_sel_e    alu_op_a_mux_sel_i,
  input  op_b_sel_e    alu_op_b_mux_sel_i,
  input  logic[31:0]   rf_rdata_a_i,
  input  logic[31:0]   rf_rdata_b_i,
  input  logic[31:0]   pc_i,
  input  logic[31:0]   imm_i,
  output logic [31:0]  result_o
);

  logic [31:0]  operand_a;
  logic [31:0]  operand_b;

  logic [31:0] operand_a_rev;
  logic [31:0] operand_b_rev;
  logic [32:0] operand_b_neg;

  //
  // ALU operand MUX
  //
  assign operand_a = (alu_op_a_mux_sel_i == OP_A_REG_A) ? rf_rdata_a_i :
                     ((alu_op_a_mux_sel_i == OP_A_CURRPC) ?  pc_i : 32'h0);
  assign operand_b = (alu_op_b_mux_sel_i == OP_B_IMM) ? imm_i : rf_rdata_b_i;

  // bit reverse operand_a for left shifts and bit counting
  for (genvar k = 0; k < 32; k++) begin : gen_rev_operand_a
    assign operand_a_rev[k] = operand_a[31-k];
    assign operand_b_rev[k] = operand_b[31-k];
  end

  ///////////
  // Adder //
  ///////////

  logic        adder_op_b_negate;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;
  logic [33:0] adder_result_ext;

  always_comb begin
    adder_op_b_negate = 1'b0;
    unique case (operator_i)
      // Adder OPs
      ALU_SUB,
      // Comparator OPs
      ALU_SLT,  ALU_SLTU,
      // MinMax OPs (RV32B Ops)
      ALU_MIN,  ALU_MINU,
      ALU_MAX,  ALU_MAXU: adder_op_b_negate = 1'b1;

      default:;
    endcase
  end

  // prepare operands

  assign operand_b_neg = {operand_b,1'b0} ^ {33{1'b1}};

  always_comb begin
    unique case (operator_i)
      ALU_SH1ADD: adder_in_a = {operand_a[30:0], 1'b0,   1'b1};
      ALU_SH2ADD: adder_in_a = {operand_a[29:0], 2'b00,  1'b1};
      ALU_SH3ADD: adder_in_a = {operand_a[28:0], 3'b000, 1'b1};
      default : adder_in_a = {operand_a,1'b1};
    endcase

    unique case (1'b1)
      adder_op_b_negate: adder_in_b = operand_b_neg;
      default:           adder_in_b = {operand_b, 1'b0};
    endcase
  end

  // actual adder
  assign adder_result_ext = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  assign adder_result     = adder_result_ext[32:1];

  ////////////////
  // Comparison //
  ////////////////

  logic is_equal;
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb begin
    unique case (operator_i)
      ALU_SLT, 
      ALU_MIN, ALU_MAX: cmp_signed = 1'b1;

      default: cmp_signed = 1'b0;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);

  // Is greater equal
  always_comb begin
    if ((operand_a[31] ^ operand_b[31]) == 1'b0) begin
      is_greater_equal = (adder_result[31] == 1'b0);
    end else begin
      is_greater_equal = operand_a[31] ^ (cmp_signed);
    end
  end

  // GTE unsigned:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 1
  // (a[31] == 0 && b[31] == 1) => 0

  // GTE signed:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 0
  // (a[31] == 0 && b[31] == 1) => 1

  // generate comparison result
  logic cmp_result;

  always_comb begin
    unique case (operator_i)
      ALU_MAX,  ALU_MAXU: cmp_result = is_greater_equal; // RV32B only
      ALU_MIN,  ALU_MINU, //RV32B only
      ALU_SLT,  ALU_SLTU: cmp_result = ~is_greater_equal;

      default: cmp_result = is_equal;
    endcase
  end

  ///////////
  // Shift //
  ///////////

  // shift logic is used for
  //  - RV32I shift instructions
  //  - RV32 ZBB rotation instructions
  //  - RV32 ZBS bit extraction instructions

  logic       shift_left, shift_arith, shift_rotate;
  logic [4:0] shift_amt, shift_amt_n;
  logic [4:0] shift_left_amt, shift_right_amt;
  
  logic        [31:0] shift_operand, shift_result;
  logic        [32:0] shift_right_result_ext;
  logic        [31:0] shift_left_result, shift_right_result;

  assign shift_amt   = operand_b[4:0];
  assign shift_amt_n = ~shift_amt + 5'h1;   // 32 - shift_amt

  always_comb begin
    if ((operator_i == ALU_SLL)  || (operator_i == ALU_ROL)  ||
        (operator_i == ALU_BCLR) || (operator_i == ALU_BINV) || (operator_i == ALU_BSET)) begin
      shift_left      = 1'b1;
      shift_left_amt  = shift_amt;
      shift_right_amt = shift_amt_n; 
    end else begin
      shift_left      = 1'b0;
      shift_left_amt  = shift_amt_n;
      shift_right_amt = shift_amt; 
    end

    if (RV32B & ((operator_i == ALU_ROL) || (operator_i == ALU_ROR))) 
      shift_rotate = 1'b1;
    else
      shift_rotate = 1'b0;

  end

  assign shift_arith  = (operator_i == ALU_SRA);

  // shifter structure.
  always_comb begin
    unique case (operator_i)
      ALU_BSET, ALU_BCLR, ALU_BINV: shift_operand = 32'h1;
      default: shift_operand = operand_a;
    endcase;

    // actual shifters
    shift_right_result_ext = $unsigned($signed({(shift_arith & shift_operand[31]), shift_operand}) >>> 
                                       shift_right_amt[4:0]);
    shift_right_result     = shift_right_result_ext[31:0];
    shift_left_result      = shift_operand << shift_left_amt[4:0];

    shift_result = shift_rotate ? (shift_left_result | shift_right_result) :
                   shift_left ? shift_left_result : shift_right_result;
  end

  ///////////////////
  // Bitwise Logic //
  ///////////////////

  logic bwlogic_or;
  logic bwlogic_and;
  logic [31:0] bwlogic_operand_b;
  logic [31:0] bwlogic_or_result;
  logic [31:0] bwlogic_and_result;
  logic [31:0] bwlogic_xor_result;
  logic [31:0] bwlogic_result;

  logic bwlogic_op_b_negate;

  always_comb begin
    unique case (operator_i)
      // Logic-with-negate OPs (RV32B zbb Ops)
      ALU_XNOR,
      ALU_ORN,
      ALU_ANDN: bwlogic_op_b_negate = RV32B ? 1'b1 : 1'b0;
      default:  bwlogic_op_b_negate = 1'b0;
    endcase
  end

  assign bwlogic_operand_b = bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b;

  assign bwlogic_or_result  = operand_a | bwlogic_operand_b;
  assign bwlogic_and_result = operand_a & bwlogic_operand_b;
  assign bwlogic_xor_result = operand_a ^ bwlogic_operand_b;

  assign bwlogic_or  = (operator_i == ALU_OR) || (operator_i == ALU_ORN);
  assign bwlogic_and = (operator_i == ALU_AND) || (operator_i == ALU_ANDN);

  always_comb begin
    unique case (1'b1)
      bwlogic_or:  bwlogic_result = bwlogic_or_result;
      bwlogic_and: bwlogic_result = bwlogic_and_result;
      default:     bwlogic_result = bwlogic_xor_result;
    endcase
  end

  // RV32B-specific logic
  logic [5:0]  bitcnt_result;
  logic [31:0] minmax_result;
  logic [31:0] ext_result;
  logic [31:0] singlebit_result;
  logic [31:0] rev_result;
  logic [31:0] clmul_result;


  if (RV32B) begin : g_alu_rvb

    /////////////////
    // Bitcounting //
    /////////////////
    
    logic        bitcnt_ctz;
    logic        bitcnt_clz;
    logic        bitcnt_cz;
    logic [31:0] bitcnt_bits;
    logic [31:0] bitcnt_mask_op;
    logic [31:0] bitcnt_bit_mask;
    logic [ 5:0] bitcnt_partial [32];
    logic [31:0] bitcnt_partial_lsb_d;
    logic [31:0] bitcnt_partial_msb_d;
    
    assign bitcnt_ctz    = operator_i == ALU_CTZ;
    assign bitcnt_clz    = operator_i == ALU_CLZ;
    assign bitcnt_cz     = bitcnt_ctz | bitcnt_clz;
    assign bitcnt_result = bitcnt_partial[31];

    // Bit-mask generation for clz and ctz:
    // The bit mask is generated by spreading the lowest-order set bit in the operand to all
    // higher order bits. The resulting mask is inverted to cover the lowest order zeros. In order
    // to create the bit mask for leading zeros, the input operand needs to be reversed.
    assign bitcnt_mask_op = bitcnt_clz ? operand_a_rev : operand_a;

    always_comb begin
      bitcnt_bit_mask = bitcnt_mask_op;
      bitcnt_bit_mask |= bitcnt_bit_mask << 1;
      bitcnt_bit_mask |= bitcnt_bit_mask << 2;
      bitcnt_bit_mask |= bitcnt_bit_mask << 4;
      bitcnt_bit_mask |= bitcnt_bit_mask << 8;
      bitcnt_bit_mask |= bitcnt_bit_mask << 16;
      bitcnt_bit_mask = ~bitcnt_bit_mask;
     
      if (bitcnt_cz)
        bitcnt_bits = bitcnt_bit_mask & ~bitcnt_mask_op; // clz / ctz
      else
        bitcnt_bits = operand_a; // cpop
    end

   always_comb begin
      bitcnt_partial = '{default: '0};
      // stage 1
      for (int unsigned i = 1; i < 32; i += 2) begin
        bitcnt_partial[i] = {5'h0, bitcnt_bits[i]} + {5'h0, bitcnt_bits[i-1]};
      end
      // stage 2
      for (int unsigned i = 3; i < 32; i += 4) begin
        bitcnt_partial[i] = bitcnt_partial[i-2] + bitcnt_partial[i];
      end
      // stage 3
      for (int unsigned i = 7; i < 32; i += 8) begin
        bitcnt_partial[i] = bitcnt_partial[i-4] + bitcnt_partial[i];
      end
      // stage 4
      for (int unsigned i = 15; i < 32; i += 16) begin
        bitcnt_partial[i] = bitcnt_partial[i-8] + bitcnt_partial[i];
      end
      // stage 5
      bitcnt_partial[31] = bitcnt_partial[15] + bitcnt_partial[31];
      // ^- primary adder tree
      // -------------------------------
      // ,-intermediate value adder tree
      bitcnt_partial[23] = bitcnt_partial[15] + bitcnt_partial[23];

      // stage 6
      for (int unsigned i = 11; i < 32; i += 8) begin
        bitcnt_partial[i] = bitcnt_partial[i-4] + bitcnt_partial[i];
      end

      // stage 7
      for (int unsigned i = 5; i < 32; i += 4) begin
        bitcnt_partial[i] = bitcnt_partial[i-2] + bitcnt_partial[i];
      end
      // stage 8
      bitcnt_partial[0] = {5'h0, bitcnt_bits[0]};
      for (int unsigned i = 2; i < 32; i += 2) begin
        bitcnt_partial[i] = bitcnt_partial[i-1] + {5'h0, bitcnt_bits[i]};
      end
    end

    ///////////////
    // Min / Max //
    ///////////////

    assign minmax_result = cmp_result ? operand_a : operand_b;

    ///////////////
    // Sext/Zext //
    ///////////////

    assign ext_result = (operator_i == ALU_SEXTB) ? { {24{operand_a[7]}}, operand_a[7:0]} : 
                        (operator_i == ALU_SEXTH) ? { {16{operand_a[15]}}, operand_a[15:0]} :
                        {16'h0, operand_a[15:0]};

    ////////////////////////////////////
    // Reverse and Or-combine //
    ////////////////////////////////////
    logic [31:0] rev8_result, orcb_result;

    assign orcb_result = { {8{|operand_a[31:24]}},  {8{|operand_a[23:16]}}, 
                           {8{|operand_a[15:8]}},   {8{|operand_a[7:0]}} };

    assign rev8_result[31:24] = operand_a[7:0];
    assign rev8_result[23:16] = operand_a[15:8];
    assign rev8_result[15:8]  = operand_a[23:16];
    assign rev8_result[7:0]   = operand_a[31:24];

    assign rev_result = (operator_i == ALU_ORCB) ? orcb_result : rev8_result; 

    /////////////////////////////
    // Single-bit Instructions //
    /////////////////////////////

    always_comb begin
      unique case (operator_i)
        ALU_BSET: singlebit_result = operand_a | shift_result;
        ALU_BCLR: singlebit_result = operand_a & ~shift_result;
        ALU_BINV: singlebit_result = operand_a ^ shift_result;
        default:  singlebit_result = {31'h0, shift_result[0]}; // ALU_BEXT
      endcase
    end

    ///////////////////////////////
    // Polynomial Multiplication //
    ///////////////////////////////
    logic [63:0] clmul64;
    logic [31:0] clmul_input_a, clmul_input_b;
    logic [31:0] clmul_result_rev, clmul_result_raw;

    assign clmul_input_a = (operator_i == ALU_CLMULR) ? operand_a_rev : operand_a;
    assign clmul_input_b = (operator_i == ALU_CLMULR) ? operand_b_rev : operand_b;

    always_comb begin
      int i, j;

      clmul64 = 64'h0;

      for (i = 0; i < 32; i++) begin
        for (j = 0; j < 32; j++) begin
          clmul64[i+j] ^= clmul_input_a[j] & clmul_input_b[i];
        end
      end
    end

    assign clmul_result_raw = (operator_i == ALU_CLMULH) ? clmul64[63:32] : clmul64[31:0];

    for (genvar i = 0; i < 32; i++) begin : gen_rev_clmul_result
      assign clmul_result_rev[i] = clmul_result_raw[31-i];
    end

    assign clmul_result = (operator_i == ALU_CLMULR) ? clmul_result_rev : clmul_result_raw;
   
  end else begin : g_no_alu_rvb
    assign bitcnt_result       = '0;
    assign minmax_result       = '0;
    assign sext_result         = '0;
    assign singlebit_result    = '0;
    assign rev_result          = '0;
    assign clmul_result        = '0;

  end

  ////////////////
  // Result mux //
  ////////////////

  always_comb begin
    result_o   = '0;

    unique case (operator_i)
      // Bitwise Logic Operations (negate: RV32B ZBB)
      ALU_XOR, ALU_OR, ALU_AND,
      ALU_XNOR, ALU_ORN, ALU_ANDN: result_o = bwlogic_result;

      // Adder Operations
      ALU_ADD,  ALU_SUB,
      // RV32B ZBA
      ALU_SH1ADD, ALU_SH2ADD,
      ALU_SH3ADD: result_o = adder_result;

      // Shift Operations and RV32 ZBB rotation
      ALU_SLL,  ALU_SRL,
      ALU_SRA,
      ALU_ROL,  ALU_ROR: result_o = shift_result;

      // Comparison Operations
      ALU_SLT,  ALU_SLTU: result_o = {31'h0,cmp_result};

      // Bitcount Operations (RV32B ZBB)
      ALU_CLZ, ALU_CTZ,
      ALU_CPOP: result_o = {26'h0, bitcnt_result};

      // MinMax Operations (RV32B ZBB)
      ALU_MIN,  ALU_MAX,
      ALU_MINU, ALU_MAXU: result_o = minmax_result;

      // Sign-Extend (RV32B ZBB)
      ALU_SEXTB, ALU_SEXTH, ALU_ZEXTH: result_o = ext_result;

      // Rev/combine (RV32B ZBB)
      ALU_ORCB, ALU_REV8: result_o = rev_result;

      // Single-Bit Bitmanip Operations (RV32B ZBS)
      ALU_BSET, ALU_BCLR,
      ALU_BINV, ALU_BEXT: result_o = singlebit_result;

      // Carry-less Multiply Operations (RV32B ZBC)
      ALU_CLMUL, ALU_CLMULR,
      ALU_CLMULH: result_o = clmul_result;

      default: ;
    endcase
  end

endmodule
