// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module accuracy_lsif;
  localparam IDLE = 0, DLY0_WGNT = 1, DLY1 = 2, DLY1_WGNT = 3;
  logic [2:0] lsif_fsm_q = IDLE;
  logic lsif_rdy_local = 0, xfr2hold0 = 0, xfr2hold1 = 0;
  logic req_dly_valid = 0, lsu_req_o = 0, lsu_req_done_i = 0;
endmodule

module accuracy_fifo;
  logic signed [7:0] fifo_level = 0;
  logic fifo_empty = 1, wr_data_en = 0, wr_valid_i = 0, wr_rdy = 0;
  logic [1:0] rd_mem_addr = 0, wr_mem_addr = 0;
  logic rd_valid = 0, rd_rdy_i = 0, waw_match_head = 0;
  logic [5:0] fifo_head_data = 0;
endmodule

module accuracy_lsu;
  import super_pkg::*;
  lsu_req_info_t lsu_req_info_q = '0;
  pl_out_t lsu_resp_info = '0;
  cheri_pkg::mem_cap_t data_rdata_i = '0;
  logic data_rvalid_i = 0, data_err_i = 0, pmp_err_q = 0;
  logic ls_go = 0, csr_go = 0, resp_wait = 0, ds_rdy_i = 1;
  logic rdata_update = 0, csr_go_q = 0;
  logic csr_cheri_asr_err = 0;
  cheri_pkg::lschk_err_t lschk_err_final = '0;
  logic [5:0] ls_err_cause = 0;
  logic [11:0] csr_addr = 0;
  logic illegal_csr_insn_i = 0, csr_cheri = 0, csr_cheri_always_ok = 0;
  logic pcc_asr_bit = 1, csr_lsu_wr_req_o = 0;
endmodule

module dcache;
  import super_pkg::*;
  logic clk_i = 0, rst_ni = 1, flush_i = 0;
  logic cache_enable_i = 0, lsu_req_i = 0;
  pl_fwd_t fwd_info_o = '0;
  logic [3:0] line_valid = 0, rd_tag_match = 0, wr_tag_match = 0;
  logic cache_rd_hit = 0, cache_rd_match_ok = 0, rd_hit_q = 0;
  logic byp_tag_match = 0, byp_data_good = 0, unaligned_access = 0;
  logic unaligned_access_q = 0, resp_full_word = 0, resp_partial_word = 0;
  logic resp_invalidate = 0, waw_act_match = 0;
  logic [3:0] repl_sel = 0, update_valid = 0, update_invalid = 0;
  accuracy_fifo waw_fifo_i();
  logic lsu_req_done_i = 0, lsu_req_q = 0;
  lsu_req_info_t lsu_req_info_i = '0, lsu_req_info_q = '0;
  kudu_fcov_dcache monitor(.*);
endmodule

module ls_pipeline;
  import super_pkg::*;
  import csr_pkg::*;
  import cheri_pkg::*;
`ifdef CHERIoT
  localparam bit CHERIoTEn = 1;
`else
  localparam bit CHERIoTEn = 0;
`endif
  logic clk_i = 0, rst_ni = 0;
  logic us_valid_i = 0, lspl_rdy_o = 0, ds_rdy_i = 1, lspl_valid_o = 0;
  logic flush_i = 0, sel_ira_i = 0, cmplx_lsu_req_valid_i = 0;
  lsu_req_info_t lsu_req_info = '0;
  logic lsu_req = 0, lsu_req_done = 0, lsu_resp_valid = 0, lsu_resp_err = 0;
  pl_out_t lspl_output_o = '0;
  logic lsu_err_active = 0, resp_err_latched = 0, lr_insn = 0, sc_insn = 0;
  logic data_sc_fail_i = 0, data_req_o = 0, data_gnt_i = 0, data_rvalid_i = 0;
  logic data_we_o = 0, data_err_i = 0, data_is_cap_o = 0;
  logic [3:0] data_be_o = 0, data_amo_flag_o = 0;
  logic [31:0] data_addr_o = 0;
  ls_fsm_e ls_fsm_cs = IDLE;
  logic split_misaligned_access = 0, handle_misaligned_q = 0;
  logic addr_incr_req = 0, lsu_busy = 0, trvk_en_o = 0;
  logic trvk_outstanding_o = 0, tsafe_en_i = 0, debug_mode_i = 0, cheri_pmode_i = 0;
  accuracy_lsif lsu_if_i();
  accuracy_lsu load_store_unit_i();
  accuracy_fifo waw_fifo_i();
  accuracy_fifo wb_fifo_i();
  kudu_fcov_lsu u_fcov_lsu(.*);

  task automatic tick;
    #5; clk_i = 1; #5; clk_i = 0;
  endtask

  task automatic save_mode(input bit mode);
    cheri_pmode_i = mode;
    load_store_unit_i.ls_go = 1;
    tick();
    load_store_unit_i.ls_go = 0;
  endtask

  task automatic cap_response(input mem_cap_t mem, input logic [3:0] clr);
    save_mode(1);
    cheri_pmode_i = 1;
    lsu_resp_valid = 1;
    load_store_unit_i.data_rvalid_i = 1;
    load_store_unit_i.data_err_i = 0;
    lsu_resp_err = 0;
    load_store_unit_i.lsu_req_info_q.is_load = 1;
    load_store_unit_i.lsu_req_info_q.clrperm = clr;
    load_store_unit_i.lsu_resp_info.is_cap = 1;
    load_store_unit_i.data_rdata_i = mem;
    load_store_unit_i.lsu_resp_info.wdata = mem2regcap(mem, clr);
    tick();
    lsu_resp_valid = 0;
    load_store_unit_i.data_rvalid_i = 0;
  endtask

  task automatic split_case(input bit is_load, first_err, second_err);
    split_misaligned_access = 1;
    load_store_unit_i.ls_go = 1;
    tick();
    load_store_unit_i.ls_go = 0;
    split_misaligned_access = 0;
    ls_fsm_cs = WAIT_RVALID_MIS;
    data_rvalid_i = 1;
    data_err_i = first_err;
    load_store_unit_i.pmp_err_q = 0;
    tick();
    data_rvalid_i = 0;
    data_err_i = 0;
    ls_fsm_cs = IDLE;
    load_store_unit_i.lsu_req_info_q.is_load = is_load;
    lsu_resp_valid = 1;
    data_err_i = second_err;
    tick();
    lsu_resp_valid = 0;
    data_err_i = 0;
  endtask

  task automatic exercise;
    mem_cap_t mem;
    tick(); rst_ni = 1;
    for (int cause = 0; cause < 7; cause++) begin
      cheri_pmode_i = 1;
      lsu_req = 1;
      lsu_req_info.lschk_err = '0;
      lsu_req_info.lschk_err.any_fault = 1;
      // Drive check_ls_err fields so vio_cause_enc yields each cause.
      case (cause)
        0: lsu_req_info.lschk_err.align = 1;   // 5'h00, alignment only
        1: lsu_req_info.lschk_err.bound = 1;   // 5'h01
        2: lsu_req_info.lschk_err.tag   = 1;   // 5'h02
        3: lsu_req_info.lschk_err.seal  = 1;   // 5'h03
        4: lsu_req_info.lschk_err.ld    = 1;   // 5'h12
        5: lsu_req_info.lschk_err.sd    = 1;   // 5'h13
        default: lsu_req_info.lschk_err.sc = 1; // 5'h15
      endcase
      tick();
    end
    cheri_pmode_i = 0; tick();
    lsu_req = 0; lsu_req_info = '0;

    for (int cause = 0; cause < 7; cause++) begin
      save_mode(1);
      cheri_pmode_i = 1;
      lsu_resp_valid = 1;
      load_store_unit_i.lschk_err_final = '0;
      load_store_unit_i.lschk_err_final.any_fault = 1;
      load_store_unit_i.lsu_req_info_q.lschk_err = '0;
      case (cause)
        0: load_store_unit_i.ls_err_cause = 6'h20;   // align_only, 5'h00
        1: load_store_unit_i.ls_err_cause = 6'h01;
        2: load_store_unit_i.ls_err_cause = 6'h02;
        3: load_store_unit_i.ls_err_cause = 6'h03;
        4: load_store_unit_i.ls_err_cause = 6'h12;
        5: load_store_unit_i.ls_err_cause = 6'h13;
        default: load_store_unit_i.ls_err_cause = 6'h15;
      endcase
      tick();
      lsu_resp_valid = 0;
      load_store_unit_i.lschk_err_final = '0;
    end

    mem = '0; mem.valid = 1; mem.cperms = 6'b111111; mem.otype = 0;
    for (int p = 0; p < 8; p++) begin
      mem.cexp = p[2] ? 5'd0 : 5'd7;
      mem.base9 = {p[1], 8'h80};
      mem.top8 = p[0] ? 8'h40 : 8'hc0;
      cap_response(mem, 4'h0);
    end
    mem.valid = 1; mem.cexp = 5'd1; mem.top8 = 8'hc0; mem.base9 = 9'h080;
    mem.cperms = 6'b111111; mem.otype = 0; cap_response(mem, 4'h1);
    cap_response(mem, 4'h2); cap_response(mem, 4'h3);
    mem.otype = 1; cap_response(mem, 4'h2); cap_response(mem, 4'h3);
    cap_response(mem, 4'h8);
    mem.valid = 0; cap_response(mem, 4'h0);

    for (int load = 0; load < 2; load++)
      for (int phase = 0; phase < 4; phase++)
        split_case(load[0], phase[1], phase[0]);
  endtask
endmodule

`ifdef CHERIoT
module cheri_trvk_stage;
  import cheri_pkg::*;
  parameter int unsigned HeapBase  = 32'h2001_0000;
  parameter int unsigned TSMapSize = 1024;
  logic clk_i = 0, rst_ni = 0;
  logic clc_valid_i = 0, clc_err_i = 0;
  logic [4:0] clc_rd_i = 0, trvk_addr_o = 0;
  logic trvk_en_o = 0, trvk_clrtag_o = 0, trvk_outstanding_o = 0, tsmap_cs_o = 0;
  logic [15:0] tsmap_addr_o = 0;
  logic [31:0] tsmap_rdata_i = 0;
  logic [31:0] base32 = HeapBase, tsmap_ptr = 0;
  logic [2:0] clc_valid_q = 0, cap_good_q = 0;
  logic [4:0] bitpos_q = 0;
  logic trvk_status = 0, range_ok = 1;
  logic [2:1] range_ok_q = 0;
  kudu_fcov_trvk monitor(.*);
  task automatic tick;
    #5; clk_i = 1; #5; clk_i = 0;
  endtask
  task automatic exercise;
    tick(); rst_ni = 1;
    for (int b = 0; b < 32; b++) begin
      for (int v = 0; v < 2; v++) begin
        tsmap_ptr = b;
        base32 = HeapBase + (b << 3);
        clc_valid_i = 1;
        clc_rd_i = b[3:0];
        tick();
        clc_valid_i = 0;
        tick();
        trvk_status = v[0];
        trvk_en_o = 1;
        trvk_clrtag_o = v[0];
        cap_good_q[2] = 1;
        range_ok_q[2] = 1;
        tick();
        trvk_en_o = 0;
      end
    end
    range_case(HeapBase, 0);
    range_case(HeapBase + (TSMapSize << 8), TSMapSize << 5);
    range_case(HeapBase + ((TSMapSize + 1) << 8), (TSMapSize + 1) << 5);
    range_case(HeapBase - 8, 32'h1fffffff);
    range_case(HeapBase + (5 << 8), 5 << 5);
    prev_pair(0, 1);
    prev_pair(1, 0);
  endtask
  // trvk_cheri_mode_q[0] is clc_valid_i registered, so present the CLC one
  // cycle before the stage-0 values are sampled.
  task automatic range_case(input logic [31:0] base, ptr);
    clc_valid_i = 1; tick();
    clc_valid_i = 0;
    base32 = base; tsmap_ptr = ptr; cap_good_q[0] = 1; clc_valid_q[0] = 1; tick();
    cap_good_q[0] = 0; clc_valid_q[0] = 0;
  endtask
  // The b2b point needs trvk_cheri_mode_q[2] on both checks, i.e. CLCs
  // three and four cycles before the second check.
  task automatic prev_pair(input bit a, b);
    clc_valid_i = 1; tick(); tick();
    clc_valid_i = 0; tick();
    trvk_en_o = 1; trvk_clrtag_o = a; tick();
    trvk_clrtag_o = b; tick();
    trvk_en_o = 0;
  endtask
endmodule
`endif

module tb;
  ls_pipeline lspl();
  dcache cache();
`ifdef CHERIoT
  cheri_trvk_stage trvk();
`endif
  initial begin
    lspl.exercise();
`ifdef CHERIoT
    lspl.save_mode(1);
    trvk.exercise();
`endif
    $display("PASS LSU semantics HW=%0d", lspl.CHERIoTEn);
    $finish;
  end
endmodule
