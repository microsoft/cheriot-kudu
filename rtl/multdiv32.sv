// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define OP_L 15:0
`define OP_H 31:16

/**
 * Fast Multiplier and Division
 *
 * Pipelined 32x32 multiplier and Long Division
 */

//`include "prim_assert.sv"

module signed_mult_33x33_wallace #(
    parameter int plStageNum = 0
) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    input  logic signed [32:0]      a,
    input  logic signed [32:0]      b,
    output logic signed [65:0]      product
);

    localparam int W = 66;

    /*
     * A 3:2 compressor returns:
     *
     *     x + y + z = result.sum + result.carry
     *
     * result.carry is already shifted left by one bit.
     */
    typedef struct packed {
        logic [W-1:0] carry;
        logic [W-1:0] sum;
    } csa_result_t;

    function automatic csa_result_t compress_3to2 (
        input logic [W-1:0] x,
        input logic [W-1:0] y,
        input logic [W-1:0] z
    );
        csa_result_t result;

        begin
            result.sum = x ^ y ^ z;
            result.carry = ((x & y) | (x & z) | (y & z)) << 1;
            return result;
        end
    endfunction

    /*
     * Sign-extended multiplicand.
     */
    logic [W-1:0] a_ext;

    assign a_ext = {{33{a[32]}}, a};

    /*
     * Two's-complement partial products.
     *
     * b = sum(b[i] * 2^i), i=0..31
     *     - b[32] * 2^32
     */
    logic [W-1:0] partial_product [0:32];

    genvar i;

    generate
        for (i = 0; i < 32; i++) begin : gen_positive_partial_products
            assign partial_product[i] = b[i] ? (a_ext << i) : '0;
        end
    endgenerate

    logic [W-1:0] sign_partial_product;

    assign sign_partial_product = a_ext << 32;

    assign partial_product[32] = b[32] ? (~sign_partial_product + {{W-1{1'b0}}, 1'b1}) : '0;


    /*
     * Stage 1: 33 rows -> 22 rows
     */

    logic [W-1:0] stage1_comb [0:21];
    logic [W-1:0] stage1      [0:21];

    generate
        for (i = 0; i < 11; i++) begin : gen_stage1_compressors
            csa_result_t csa_result;

            always_comb begin
                csa_result = compress_3to2(
                    partial_product[3*i],
                    partial_product[3*i + 1],
                    partial_product[3*i + 2]
                );

                stage1_comb[2*i]     = csa_result.sum;
                stage1_comb[2*i + 1] = csa_result.carry;
            end
        end
    endgenerate

    generate
        if (plStageNum == 1) begin : gen_stage1_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 22; k++) begin
                        stage1[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 22; k++) begin
                        stage1[k] <= stage1_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage1_bypass
            for (i = 0; i < 22; i++) begin
                assign stage1[i] = stage1_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 2: 22 rows -> 15 rows
     */

    logic [W-1:0] stage2_comb [0:14];
    logic [W-1:0] stage2      [0:14];

    generate
        for (i = 0; i < 7; i++) begin : gen_stage2_compressors
            csa_result_t csa_result;

            always_comb begin
                csa_result = compress_3to2( stage1[3*i], stage1[3*i + 1], stage1[3*i + 2]);

                stage2_comb[2*i]     = csa_result.sum;
                stage2_comb[2*i + 1] = csa_result.carry;
            end
        end
    endgenerate

    assign stage2_comb[14] = stage1[21];

    generate
        if (plStageNum == 2) begin : gen_stage2_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 15; k++) begin
                        stage2[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 15; k++) begin
                        stage2[k] <= stage2_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage2_bypass
            for (i = 0; i < 15; i++) begin
                assign stage2[i] = stage2_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 3: 15 rows -> 10 rows
     */

    logic [W-1:0] stage3_comb [0:9];
    logic [W-1:0] stage3      [0:9];

    generate
        for (i = 0; i < 5; i++) begin : gen_stage3_compressors
            csa_result_t csa_result;

            always_comb begin
                csa_result = compress_3to2( stage2[3*i], stage2[3*i + 1], stage2[3*i + 2]);

                stage3_comb[2*i]     = csa_result.sum;
                stage3_comb[2*i + 1] = csa_result.carry;
            end
        end
    endgenerate

    generate
        if (plStageNum == 3) begin : gen_stage3_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 10; k++) begin
                        stage3[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 10; k++) begin
                        stage3[k] <= stage3_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage3_bypass
            for (i = 0; i < 10; i++) begin
                assign stage3[i] = stage3_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 4: 10 rows -> 7 rows
     */

    logic [W-1:0] stage4_comb [0:6];
    logic [W-1:0] stage4      [0:6];

    generate
        for (i = 0; i < 3; i++) begin : gen_stage4_compressors
            csa_result_t csa_result;

            always_comb begin
                csa_result = compress_3to2( stage3[3*i], stage3[3*i + 1], stage3[3*i + 2]);

                stage4_comb[2*i]     = csa_result.sum;
                stage4_comb[2*i + 1] = csa_result.carry;
            end
        end
    endgenerate

    assign stage4_comb[6] = stage3[9];

    generate
        if (plStageNum == 4) begin : gen_stage4_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 7; k++) begin
                        stage4[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 7; k++) begin
                        stage4[k] <= stage4_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage4_bypass
            for (i = 0; i < 7; i++) begin
                assign stage4[i] = stage4_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 5: 7 rows -> 5 rows
     */

    logic [W-1:0] stage5_comb [0:4];
    logic [W-1:0] stage5      [0:4];

    generate
        for (i = 0; i < 2; i++) begin : gen_stage5_compressors
            csa_result_t csa_result;

            always_comb begin
                csa_result = compress_3to2( stage4[3*i], stage4[3*i + 1], stage4[3*i + 2]);

                stage5_comb[2*i]     = csa_result.sum;
                stage5_comb[2*i + 1] = csa_result.carry;
            end
        end
    endgenerate

    assign stage5_comb[4] = stage4[6];

    generate
        if (plStageNum == 5) begin : gen_stage5_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 5; k++) begin
                        stage5[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 5; k++) begin
                        stage5[k] <= stage5_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage5_bypass
            for (i = 0; i < 5; i++) begin
                assign stage5[i] = stage5_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 6: 5 rows -> 4 rows
     */

    logic [W-1:0] stage6_comb [0:3];
    logic [W-1:0] stage6      [0:3];

    always_comb begin : stage6_compressor
        csa_result_t csa_result;

        csa_result = compress_3to2(
            stage5[0],
            stage5[1],
            stage5[2]
        );

        stage6_comb[0] = csa_result.sum;
        stage6_comb[1] = csa_result.carry;
    end

    assign stage6_comb[2] = stage5[3];
    assign stage6_comb[3] = stage5[4];

    generate
        if (plStageNum == 6) begin : gen_stage6_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 4; k++) begin
                        stage6[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 4; k++) begin
                        stage6[k] <= stage6_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage6_bypass
            for (i = 0; i < 4; i++) begin
                assign stage6[i] = stage6_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 7: 4 rows -> 3 rows
     */

    logic [W-1:0] stage7_comb [0:2];
    logic [W-1:0] stage7      [0:2];

    always_comb begin : stage7_compressor
        csa_result_t csa_result;

        csa_result = compress_3to2( stage6[0], stage6[1], stage6[2]);

        stage7_comb[0] = csa_result.sum;
        stage7_comb[1] = csa_result.carry;
    end

    assign stage7_comb[2] = stage6[3];

    generate
        if (plStageNum == 7) begin : gen_stage7_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 3; k++) begin
                        stage7[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 3; k++) begin
                        stage7[k] <= stage7_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage7_bypass
            for (i = 0; i < 3; i++) begin
                assign stage7[i] = stage7_comb[i];
            end
        end
    endgenerate


    /*
     * Stage 8: 3 rows -> 2 rows
     */

    logic [W-1:0] stage8_comb [0:1];
    logic [W-1:0] stage8      [0:1];

    always_comb begin : stage8_compressor
        csa_result_t csa_result;

        csa_result = compress_3to2( stage7[0], stage7[1], stage7[2]);

        stage8_comb[0] = csa_result.sum;
        stage8_comb[1] = csa_result.carry;
    end

    generate
        if (plStageNum == 8) begin : gen_stage8_pipeline
            integer k;

            always_ff @(posedge clk_i or negedge rst_ni) begin
                if (!rst_ni) begin
                    for (k = 0; k < 2; k++) begin
                        stage8[k] <= '0;
                    end
                end
                else begin
                    for (k = 0; k < 2; k++) begin
                        stage8[k] <= stage8_comb[k];
                    end
                end
            end
        end
        else begin : gen_stage8_bypass
            for (i = 0; i < 2; i++) begin
                assign stage8[i] = stage8_comb[i];
            end
        end
    endgenerate


    /*
     * Final carry-propagate addition.
     */
    assign product = $signed(stage8[0] + stage8[1]);


endmodule


module multdiv32 # (parameter bit UseDWMult = 1'b0) (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  logic              mult_en_i,  // dynamic enable signal, for FSM control
  input  logic              div_en_i,   // dynamic enable signal, for FSM control
  input  super_pkg::md_op_e operator_i,
  input  logic  [1:0]       signed_mode_i,
  input  logic [31:0]       op_a_i,
  input  logic [31:0]       op_b_i,
  input  logic              data_ind_timing_i,
  output logic [31:0]       mult_result_o,
  output logic [31:0]       div_result_o,
  output logic              mult_valid_o,
  output logic              div_valid_o
);

  import super_pkg::*;

  logic [32:0] alu_operand_a;
  logic [32:0] alu_operand_b;
  logic [33:0] md_adder_ext;
  logic [31:0] md_adder_out;
  logic        md_equal_to_zero;

  logic [33:0] imd_val_q[2];
  logic [33:0] imd_val_d[2];
  logic [1:0]  imd_val_we;

  // Results that become intermediate value depending on whether mul or div is being calculated
  logic [33:0] op_remainder_d;
  // Raw output of MAC calculation

  // Divider signals
  logic        div_sign_a, div_sign_b;
  md_op_e      operator_q;
  logic [31:0] op_a_q, op_b_q;

  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;
  logic [31:0] one_shift;
  logic [31:0] op_denominator_q;
  logic [31:0] op_numerator_q;
  logic [31:0] op_quotient_q;
  logic [31:0] op_denominator_d;
  logic [31:0] op_numerator_d;
  logic [31:0] op_quotient_d;
  logic [31:0] next_remainder;
  logic [32:0] next_quotient;
  logic [31:0] res_adder_h;
  logic        div_valid;
  logic [ 4:0] div_counter_q, div_counter_d;
  logic        div_by_zero_d, div_by_zero_q;

  logic        div_en_internal;

  typedef enum logic [2:0] {
    MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
  } md_fsm_e;
  md_fsm_e md_state_q, md_state_d;

  // 
  
  // The 2-staged pipelined multipler 
  //  (if you can't use a DW component like dw_mult_pipe)
  logic signed [65:0] mult_result;
  logic               mult_sign_a, mult_sign_b;
  md_op_e             mult_op;
  assign mult_sign_a  = op_a_i[31] & signed_mode_i[0];
  assign mult_sign_b  = op_b_i[31] & signed_mode_i[1];

  if (UseDWMult) begin : gen_dw_mult
    DW_mult_pipe #(
      .a_width   (33),
      .b_width   (33),
      .num_stages(2),
      .stall_mode(1),    // allow stalling
      .rst_mode  (1)     // async reset
    ) dw_mut_pipe_i (
      .clk   (clk_i),
      .rst_n (rst_ni),
      .en    (mult_en_i),
      .tc    (1'b1),     // 0: unsigned mode, 1: signed mode
      .a     ({mult_sign_a, op_a_i}),
      .b     ({mult_sign_b, op_b_i}),
      .product (mult_result)
    );
  end else begin : gen_no_dw_mult
    logic signed [32:0] mult_a, mult_b;
    
    assign mult_a = {mult_sign_a, op_a_i[31:0]};
    assign mult_b = {mult_sign_b, op_b_i[31:0]};

    signed_mult_33x33_wallace #( .plStageNum (5)) mult33_i (
        .clk_i   (clk_i),
        .rst_ni  (rst_ni),
        .a       (mult_a),
        .b       (mult_b),
        .product (mult_result)
    );
    
  end // gen_no_dw_mult

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mult_op      <= MD_OP_MULL;
      mult_valid_o <= 1'b0;
    end else begin 
      if (mult_en_i) mult_op  <= operator_i;
      mult_valid_o <= mult_en_i;
    end
  end

  assign mult_result_o = (mult_op == MD_OP_MULL) ? mult_result[31:0] :  mult_result[63:32]; 

  //
  // Divider
  // 

  assign op_denominator_q = imd_val_q[1][31:0];

  assign div_result_o = imd_val_q[0][31:0];

  assign res_adder_h    = md_adder_ext[32:1];
  assign next_remainder = is_greater_equal ? res_adder_h[31:0] : imd_val_q[0][31:0];
  assign next_quotient  = is_greater_equal ? {1'b0, op_quotient_q} | {1'b0, one_shift} :
                                             {1'b0, op_quotient_q};

  assign one_shift      = {31'b0, 1'b1} << div_counter_q;

  assign md_adder_ext     = $unsigned(alu_operand_a) + $unsigned(alu_operand_b);
  assign md_adder_out     = md_adder_ext[32:1];
  assign md_equal_to_zero = (alu_operand_a == alu_operand_b);

  // Intermediate value register for DIV only
  assign imd_val_d[0]  = op_remainder_d;
  assign imd_val_we[0] = div_en_internal;

  assign imd_val_d[1]  = {2'b0, op_denominator_d};
  assign imd_val_we[1] = div_en_internal;

  for (genvar i = 0; i < 2; i++) begin : gen_intermediate_val_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : intermediate_val_reg
      if (!rst_ni) begin
        imd_val_q[i] <= '0;
      end else if (imd_val_we[i]) begin
        imd_val_q[i] <= imd_val_d[i];
      end
    end
  end

  assign div_en_internal  = div_en_i | (md_state_q != MD_IDLE);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      div_counter_q    <= '0;
      md_state_q       <= MD_IDLE;
      op_numerator_q   <= '0;
      op_quotient_q    <= '0;
      div_by_zero_q    <= '0;
      div_sign_a       <= 1'b0;
      div_sign_b       <= 1'b0;
      operator_q       <= MD_OP_MULL;
      op_a_q           <= 32'h0;
      op_b_q           <= 32'h0;
    end else begin 
      if (div_en_internal) begin
        div_counter_q    <= div_counter_d;
        op_numerator_q   <= op_numerator_d;
        op_quotient_q    <= op_quotient_d;
        md_state_q       <= md_state_d;
        div_by_zero_q    <= div_by_zero_d;
      end
      // latch inputs for div operations
      if (md_state_q == MD_IDLE) begin
        div_sign_a  <= op_a_i[31] & signed_mode_i[0];
        div_sign_b  <= op_b_i[31] & signed_mode_i[1];
        operator_q  <= operator_i;
        op_a_q      <= op_a_i;
        op_b_q      <= op_b_i;
      end
    end
  end

  // The adder in the ALU computes alu_operand_a + alu_operand_b which means
  // Remainder - Divisor. If Remainder - Divisor >= 0, is_greater_equal is equal to 1,
  // the next Remainder is Remainder - Divisor contained in res_adder_h and the
  always_comb begin
    if ((imd_val_q[0][31] ^ op_denominator_q[31]) == 1'b0) begin
      is_greater_equal = (res_adder_h[31] == 1'b0);
    end else begin
      is_greater_equal = imd_val_q[0][31];
    end
  end

  assign div_change_sign = (div_sign_a ^ div_sign_b) & ~div_by_zero_q;
  assign rem_change_sign = div_sign_a;


  always_comb begin
    div_counter_d    = div_counter_q - 5'h1;
    op_remainder_d   = imd_val_q[0];
    op_quotient_d    = op_quotient_q;
    md_state_d       = md_state_q;
    op_numerator_d   = op_numerator_q;
    op_denominator_d = op_denominator_q;
    alu_operand_a  = {32'h0  , 1'b1};
    alu_operand_b  = {~op_b_i, 1'b1};
    div_valid        = 1'b0;
    div_by_zero_d    = div_by_zero_q;

    unique case (md_state_q)
      MD_IDLE: begin
        if (operator_i == MD_OP_DIV) begin
          // Check if the Denominator is 0
          // quotient for division by 0 is specified to be -1
          // Note with data-independent time option, the full divide operation will proceed as
          // normal and will naturally return -1
          op_remainder_d = '1;
          md_state_d     = (!data_ind_timing_i && md_equal_to_zero) ? MD_FINISH : MD_ABS_A;
          // Record that this is a div by zero to stop the sign change at the end of the
          // division (in data_ind_timing mode).
          div_by_zero_d  = md_equal_to_zero;
        end else begin
          // Check if the Denominator is 0
          // remainder for division by 0 is specified to be the numerator (operand a)
          // Note with data-independent time option, the full divide operation will proceed as
          // normal and will naturally return operand a
          op_remainder_d = {2'b0, op_a_i};
          md_state_d     = (!data_ind_timing_i && md_equal_to_zero) ? MD_FINISH : MD_ABS_A;
        end
        // 0 - B = 0 iff B == 0
        alu_operand_a  = {32'h0  , 1'b1};
        alu_operand_b  = {~op_b_i, 1'b1};
        div_counter_d    = 5'd31;
      end

      MD_ABS_A: begin
        // quotient
        op_quotient_d   = '0;
        // A abs value
        op_numerator_d  = div_sign_a ? md_adder_out : op_a_q;
        md_state_d      = MD_ABS_B;
        div_counter_d   = 5'd31;
        // ABS(A) = 0 - A
        alu_operand_a = {32'h0  , 1'b1};
        alu_operand_b = {~op_a_q, 1'b1};
      end

      MD_ABS_B: begin
        // remainder
        op_remainder_d   = { 33'h0, op_numerator_q[31]};
        // B abs value
        op_denominator_d = div_sign_b ? md_adder_out : op_b_q;
        md_state_d       = MD_COMP;
        div_counter_d    = 5'd31;
        // ABS(B) = 0 - B
        alu_operand_a  = {32'h0  , 1'b1};
        alu_operand_b  = {~op_b_q, 1'b1};
      end

      MD_COMP: begin
        op_remainder_d  = {1'b0, next_remainder[31:0], op_numerator_q[div_counter_d]};
        op_quotient_d   = next_quotient[31:0];
        md_state_d      = (div_counter_q == 5'd1) ? MD_LAST : MD_COMP;
        // Division
        alu_operand_a = {imd_val_q[0][31:0], 1'b1}; // it contains the remainder
        alu_operand_b = {~op_denominator_q[31:0], 1'b1};  // -denominator two's compliment
      end

      MD_LAST: begin
        if (operator_q == MD_OP_DIV) begin
          // this time we save the quotient in op_remainder_d (i.e. imd_val_q[0]) since
          // we do not need anymore the remainder
          op_remainder_d = {1'b0, next_quotient};
        end else begin
          // this time we do not save the quotient anymore since we need only the remainder
          op_remainder_d = {2'b0, next_remainder[31:0]};
        end
        // Division
        alu_operand_a  = {imd_val_q[0][31:0], 1'b1}; // it contains the remainder
        alu_operand_b  = {~op_denominator_q[31:0], 1'b1};  // -denominator two's compliment

        md_state_d = MD_CHANGE_SIGN;
      end

      MD_CHANGE_SIGN: begin
        md_state_d  = MD_FINISH;
        if (operator_q == MD_OP_DIV) begin
          op_remainder_d = (div_change_sign) ? {2'h0, md_adder_out} : imd_val_q[0];
        end else begin
          op_remainder_d = (rem_change_sign) ? {2'h0, md_adder_out} : imd_val_q[0];
        end
        // ABS(Quotient) = 0 - Quotient (or Remainder)
        alu_operand_a  = {32'h0  , 1'b1};
        alu_operand_b  = {~imd_val_q[0][31:0], 1'b1};
      end

      MD_FINISH: begin
        md_state_d = MD_IDLE;
        div_valid   = 1'b1;
      end

      default: begin
        md_state_d = MD_IDLE;
      end
    endcase // md_state_q
  end

  assign div_valid_o = div_valid;


endmodule // multdiv32
