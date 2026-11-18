// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RA-prediction / predicted-PCC checker for rtl_bug_ra_pred_conf2 (KUDU-048).
// Instantiated as an extra top-level module (no ports, hierarchical refs into
// tb_kudu_top.dut).
//  X:  ir_cjalr_pcc_set / ir_cjalr_rcap must not be X (KUDU-048: undriven in conf2).
//  C1: every instruction that issues (or traps/sysctl at IR0) in PMODE=1 was bound/perm
//      checked at IR against a PCC equal to the architectural ex1_pcc_cap_q at issue.
//  C3: instruction fetch addresses outside populated memory (DRAM 0x8000_0000+256KB, debug ROM).
//  Statistics: cjalr issue / mispredict / IR-predicted counts.
// The final block prints "RA_CHK FAIL KUDU-048 ..." for X cycles, "RA_CHK FAIL ..." for
// other errors or when no cjalr issued (test not exercised), and "RA_CHK PASS" otherwise.
`ifndef KUDU_PPL_CFG
  `define KUDU_PPL_CFG 1
`endif

module ra_chk;
  import super_pkg::*;
  import cheri_pkg::*;

  localparam bit HasStage1 = (`KUDU_PPL_CFG != 2);

  logic clk;
  assign clk = tb_kudu_top.clk;

  int n_c1_err, n_c3_err, n_x_err;
  int n_issue_chk, n_cjalr_issue, n_cjalr_mis, n_cjalr_ok, n_ir_pcc_set;
  int n_ret_ok, n_ret_mis, n_ret_ptaken_issue;
  int n_exc_ir_chk;

`ifdef CHERIoT
  pcc_cap_t    shadow[2];
  logic [1:0]  s1_wr_en;
  logic        s1_wr_addr[2];
  if (`KUDU_PPL_CFG != 2) begin : g_s1
    assign s1_wr_en      = tb_kudu_top.dut.ir_stage_i.gen_stage1.s1_fifo.wr_data_en;
    assign s1_wr_addr[0] = tb_kudu_top.dut.ir_stage_i.gen_stage1.s1_fifo.wr_mem_addr[0];
    assign s1_wr_addr[1] = tb_kudu_top.dut.ir_stage_i.gen_stage1.s1_fifo.wr_mem_addr[1];
  end else begin : g_nos1
    assign s1_wr_en      = 2'b00;
    assign s1_wr_addr[0] = 1'b0;
    assign s1_wr_addr[1] = 1'b0;
  end
  logic        shadow_dbg[2];

  task automatic chk_one(input int slot, input string what, input logic [31:0] pc);
    pcc_cap_t ex1, irp;
    ex1 = tb_kudu_top.dut.cs_registers_i.ex1_pcc_cap_q;
    n_issue_chk++;
    if (HasStage1) begin
      if (!shadow_dbg[slot] && (shadow[slot] !== ex1)) begin
        n_c1_err++;
        if (n_c1_err <= 20)
          $display("RA_CHK C1 ERROR @%0t %s pc=%08x decoded_with pcc(v=%0d b=%08x t=%09x p=%03x o=%0d) != ex1(v=%0d b=%08x t=%09x p=%03x o=%0d)",
                   $time, what, pc, shadow[slot].valid, shadow[slot].base32, shadow[slot].top33,
                   shadow[slot].perms, shadow[slot].otype, ex1.valid, ex1.base32, ex1.top33, ex1.perms, ex1.otype);
      end
    end else begin
      irp = tb_kudu_top.dut.cs_registers_i.ir_pcc_cap_o;
      if (irp !== ex1) begin
        n_c1_err++;
        if (n_c1_err <= 20)
          $display("RA_CHK C1 ERROR(conf2) @%0t %s pc=%08x ir_pcc(b=%08x t=%09x p=%03x) != ex1(b=%08x t=%09x p=%03x)",
                   $time, what, pc, irp.base32, irp.top33, irp.perms, ex1.base32, ex1.top33, ex1.perms);
      end
    end
  endtask

  always @(negedge clk) begin
    logic pmode, dbg, ir0_is_a, is_ret;
    ir_dec_t d0, d1, dj;
    int s0, s1, a;
    if (tb_kudu_top.dut.rst_ni) begin
      pmode    = tb_kudu_top.dut.cheri_pmode_i;
      dbg      = tb_kudu_top.dut.issuer_i.debug_mode_q;
      ir0_is_a = tb_kudu_top.dut.ira_is0;
      s0 = ir0_is_a ? 0 : 1;
      s1 = 1 - s0;
      d0 = tb_kudu_top.dut.issuer_i.ir0_dec;
      d1 = tb_kudu_top.dut.issuer_i.ir1_dec;

      // ---- C1 (check before updating the shadow with this cycle's writes)
      if (pmode && !dbg) begin
        if (tb_kudu_top.dut.issuer_i.ir0_normal_issued)
          chk_one(s0, "issue0", d0.pc);
        if (tb_kudu_top.dut.issuer_i.ir1_issued)
          chk_one(s1, "issue1", d1.pc);
        if (tb_kudu_top.dut.issuer_i.ctrl_fsm_cs[CSM_ISSUE_SPECIAL] &&
            tb_kudu_top.dut.issuer_i.ir_valid_i[0] &&
            ((tb_kudu_top.dut.issuer_i.special_case_q == EXEC) ||
             (tb_kudu_top.dut.issuer_i.special_case_q == SYSCTL) ||
             (tb_kudu_top.dut.issuer_i.special_case_q == CMPLX))) begin
          n_exc_ir_chk++;
          chk_one(s0, "special", d0.pc);
        end
      end

      // ---- shadow update (stage-1 configurations)
      if (HasStage1 && !tb_kudu_top.dut.ex_ir_flush) begin
        for (int k = 0; k < 2; k++) begin
          if (s1_wr_en[k]) begin
            a = s1_wr_addr[k];
            shadow[a]     = tb_kudu_top.dut.cs_registers_i.ir_pcc_cap_o;
            shadow_dbg[a] = dbg;
          end
        end
      end

      // ---- statistics
      if (pmode) begin
        if (tb_kudu_top.dut.ex1_cjalr_pcc_set === 1'b1) begin
          n_cjalr_issue++;
          dj = d0.is_jalr ? d0 : d1;
          is_ret = (dj.rs1 == 5'd1) && (dj.rd == 5'd0);
          if (is_ret && dj.ptaken) n_ret_ptaken_issue++;
          if (tb_kudu_top.dut.ex1_mispredict === 1'b1) begin
            n_cjalr_mis++;
            if (is_ret) n_ret_mis++;
          end else begin
            n_cjalr_ok++;
            if (is_ret) n_ret_ok++;
          end
        end
        if ($isunknown(tb_kudu_top.dut.ir_cjalr_pcc_set) && ($time > 1000)) begin
          n_x_err++;
          if (n_x_err <= 3)
            $display("RA_CHK X @%0t ir_cjalr_pcc_set=%b ir_cjalr_rcap=%x (undriven)", $time,
                     tb_kudu_top.dut.ir_cjalr_pcc_set, tb_kudu_top.dut.ir_cjalr_rcap);
        end else if (tb_kudu_top.dut.ir_cjalr_pcc_set && !tb_kudu_top.dut.ex_ir_flush)
          n_ir_pcc_set++;
      end

    end
  end
`endif

  // ---- C3: fetch address range
  always @(negedge clk) begin
    logic [31:0] fa;
    if (tb_kudu_top.dut.rst_ni && tb_kudu_top.dut.instr_req_o) begin
      fa = tb_kudu_top.dut.instr_addr_o;
      if (!((fa >= 32'h8000_0000 && fa < 32'h8004_0000) || (fa >= 32'h8400_0000 && fa < 32'h8400_2000))) begin
        n_c3_err++;
        if (n_c3_err <= 10)
          $display("RA_CHK C3 fetch outside memory @%0t addr=%08x cur_ra32=%08x pdt_set=%0b", $time, fa,
                   tb_kudu_top.dut.ir_stage_i.cur_ra32_o, tb_kudu_top.dut.if_stage_i.predict_pc_set);
      end
    end
  end

  final begin
    $display("RA_CHK SUMMARY cfg=%0d c1_err=%0d c3_fetch_oob=%0d x_err=%0d issue_chk=%0d special_chk=%0d cjalr_issued=%0d cjalr_mispredict=%0d cjalr_ok=%0d ret_ok=%0d ret_mis=%0d ret_ptaken=%0d ir_pcc_set=%0d",
             `KUDU_PPL_CFG, n_c1_err, n_c3_err, n_x_err, n_issue_chk, n_exc_ir_chk,
             n_cjalr_issue, n_cjalr_mis, n_cjalr_ok, n_ret_ok, n_ret_mis, n_ret_ptaken_issue, n_ir_pcc_set);
    if (n_x_err > 0)
      $display("RA_CHK FAIL KUDU-048 x_err=%0d (ir_cjalr_pcc_set/ir_cjalr_rcap undriven)", n_x_err);
    if (n_c1_err > 0) $display("RA_CHK FAIL C1 c1_err=%0d", n_c1_err);
    if (n_c3_err > 0) $display("RA_CHK FAIL C3 c3_fetch_oob=%0d", n_c3_err);
    if (n_cjalr_issue == 0) $display("RA_CHK FAIL no cjalr issued in PMODE=1 (test not exercised)");
    if (n_x_err == 0 && n_c1_err == 0 && n_c3_err == 0 && n_cjalr_issue > 0)
      $display("RA_CHK PASS cjalr_issued=%0d issue_chk=%0d", n_cjalr_issue, n_issue_chk);
  end
endmodule
