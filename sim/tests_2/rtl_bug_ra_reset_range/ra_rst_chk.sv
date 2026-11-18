// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Checker for rtl_bug_ra_reset_range (KUDU-049). Compiled as an extra
// top-level module (no ports, hierarchical references into tb_kudu_top.dut).
//  - Counts front-end return predictions (branch_predict predicts a jalr-ra
//    with target cur_ra32) and records their targets.
//  - Flags every instruction fetch outside populated memory (DRAM
//    0x8000_0000 + 256 KB, debug ROM 0x8400_0000 + 8 KB).
// The final block prints "RA_RST FAIL KUDU-049 ..." if a fetch left
// populated memory, "RA_RST FAIL no return predicted ..." if the program did
// not exercise RA prediction, and "RA_RST PASS ..." otherwise.
module ra_rst_chk;
  int n_pred, n_oob, n_pred_reset;
  logic [31:0] first_target;

  initial begin
    n_pred = 0; n_oob = 0; n_pred_reset = 0; first_target = '0;
  end

  always @(negedge tb_kudu_top.clk) begin
    logic [31:0] fa, tgt;
    if (tb_kudu_top.dut.rst_ni) begin
      if ((tb_kudu_top.dut.if_stage_i.branch_predict_i.predict_pc_set_o === 1'b1) &&
          (|(tb_kudu_top.dut.if_stage_i.branch_predict_i.pdt_pc_set &
             tb_kudu_top.dut.if_stage_i.branch_predict_i.pdt_jalr_go)) &&
          (tb_kudu_top.dut.if_stage_i.branch_predict_i.predict_target ===
           tb_kudu_top.dut.ir_stage_i.cur_ra32_o)) begin
        tgt = tb_kudu_top.dut.ir_stage_i.cur_ra32_o;
        if (n_pred == 0) first_target = tgt;
        if (n_pred < 4) $display("RA_RST predicted return @%0t target=%08x", $time, tgt);
        n_pred++;
        // x1 has never held an in-range value in this program before the final puts
        if (tb_kudu_top.dut.regfile_i.rf_reg_q[1][31:0] inside {32'h0, 32'h2000}) n_pred_reset++;
      end
      if (tb_kudu_top.dut.instr_req_o === 1'b1) begin
        fa = tb_kudu_top.dut.instr_addr_o;
        if (!((fa >= 32'h8000_0000 && fa < 32'h8004_0000) ||
              (fa >= 32'h8400_0000 && fa < 32'h8400_2000))) begin
          n_oob++;
          if (n_oob <= 5)
            $display("RA_RST fetch outside memory @%0t addr=%08x cur_ra32=%08x", $time, fa,
                     tb_kudu_top.dut.ir_stage_i.cur_ra32_o);
        end
      end
    end
  end

  final begin
    $display("RA_RST SUMMARY ra_predictions=%0d before_in_range_x1=%0d first_target=%08x fetch_oob=%0d",
             n_pred, n_pred_reset, first_target, n_oob);
    if (n_oob > 0)
      $display("RA_RST FAIL KUDU-049 fetch_oob=%0d (return predicted to the cur_ra32 reset value)", n_oob);
    if (n_pred_reset == 0)
      $display("RA_RST FAIL no return predicted before x1 held an in-range value (test not exercised)");
    if (n_oob == 0 && n_pred_reset > 0)
      $display("RA_RST PASS ra_predictions=%0d before_in_range_x1=%0d", n_pred, n_pred_reset);
  end
endmodule
