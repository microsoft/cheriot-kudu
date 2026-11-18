// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ALT checker for rtl_bug_alt_tag_x (KUDU-044). Bound into fetch_fifo64; uses
// upward hierarchical references (fetch_fifo64.*, prefetch_buffer64.*,
// if_stage.*). Besides checking ALT save/apply/cancel against a shadow of the
// instruction bus, it counts cycles where the issuer's ALT cancel/apply
// controls or the alt_valid tag entering IR are X. The first RstSettle cycles
// after reset release are not counted. The final block prints
// "ALT_CHK FAIL KUDU-044 ..." for any X cycle, "ALT_CHK FAIL errors=N" for
// checker errors, and "ALT_CHK PASS" otherwise.
module alt_chk;
  localparam int NA = 2;

  logic clk;
  assign clk = fetch_fifo64.clk_i;

  // shadow of what the instruction bus returned per 64-bit word: {err, data}
  logic [64:0]  shadow [int unsigned];
  int unsigned  addr_q [$];

  logic [31:0]  rec_ft   [NA];     // fall-through PC recorded at alloc
  logic [31:0]  rec_bpc  [NA];     // branch PC recorded at alloc
  int           n_alloc, n_apply, n_cancel, n_flush_live, n_err, n_xcancel, n_apply_req;
  int           n_cancel_free, n_save_words[5], n_apply_words[4];
  int           n_tag_noalloc, n_xtag, n_alloc_i0_xfr11;
  int           max_err = 50;
  int           n_apply_err, n_alloc_err, age[2], max_age;
  localparam int RstSettle = 8;
  int           n_cyc;

  initial begin
    n_alloc = 0; n_apply = 0; n_cancel = 0; n_flush_live = 0; n_err = 0; n_xcancel = 0;
    n_cancel_free = 0; n_apply_req = 0; n_tag_noalloc = 0; n_xtag = 0; n_alloc_i0_xfr11 = 0;
    foreach (n_save_words[i]) n_save_words[i] = 0;
    n_apply_err = 0; n_alloc_err = 0; age[0] = 0; age[1] = 0; max_age = 0;
    n_cyc = 0;
    foreach (n_apply_words[i]) n_apply_words[i] = 0;
  end

  function automatic void err(string s);
    n_err++;
    if (n_err <= max_err) $display("ALT_CHK ERROR @%0t: %s", $time, s);
  endfunction

  function automatic logic [64:0] shd(int unsigned a);
    if (shadow.exists(a)) return shadow[a];
    else return {1'b1, 64'hDEAD_BEEF_DEAD_BEEF};
  endfunction

  // compare one saved/restored word against the bus shadow
  function automatic void cmp_word(string what, int id, int k, int unsigned a,
                                   logic [63:0] d, logic e, logic [31:0] bpc);
    logic [64:0] s;
    s = shd(a);
    if (e !== s[64])
      err($sformatf("%s entry %0d word %0d @%h err %b != bus %b (bpc=%h)", what, id, k, a, e, s[64], bpc));
    else if (!e && (d !== s[63:0]))
      err($sformatf("%s entry %0d word %0d @%h data %h != bus %h (bpc=%h)", what, id, k, a, d, s[63:0], bpc));
  endfunction

  always @(negedge clk) begin
    if (fetch_fifo64.rst_ni) begin
      n_cyc++;
      // ---------- bus shadow ----------
      if (prefetch_buffer64.instr_req_o & prefetch_buffer64.instr_gnt_i)
        addr_q.push_back(prefetch_buffer64.instr_addr_o);
      if (prefetch_buffer64.instr_rvalid_i) begin
        if (addr_q.size() == 0) err("rvalid without outstanding addr");
        else begin
          int unsigned a;
          a = addr_q.pop_front();
          shadow[a] = {prefetch_buffer64.instr_err_i, prefetch_buffer64.instr_rdata_i};
        end
      end

      // ---------- apply requested but not done ----------
      if (fetch_fifo64.ex_alt_ctrl_i.apply === 1'b1) begin
        n_apply_req++;
        if (fetch_fifo64.clear_i !== 1'b1) err("ex_alt_ctrl.apply without clear_i");
      end

      if ((n_cyc > RstSettle) &&
          ($isunknown(fetch_fifo64.ex_alt_ctrl_i.cancel) || $isunknown(fetch_fifo64.ex_alt_ctrl_i.apply))) begin
        if (n_xcancel < 5)
          $display("ALT_CHK X @%0t: ex_alt_ctrl cancel=%b apply=%b", $time,
                   fetch_fifo64.ex_alt_ctrl_i.cancel, fetch_fifo64.ex_alt_ctrl_i.apply);
        n_xcancel++;
      end

      // ---------- tag without allocation ----------
      begin
        logic [1:0] tag;
        tag[0] = if_stage.if_valid_o[0] & if_stage.ds_rdy_i[0] & if_stage.pdt_instr0.alt_valid;
        tag[1] = if_stage.if_valid_o[1] & if_stage.ds_rdy_i[1] & if_stage.pdt_instr1.alt_valid;
        if ((n_cyc > RstSettle) && $isunknown(tag)) begin
          if (n_xtag < 5) $display("ALT_CHK X @%0t: alt_valid tag=%b", $time, tag);
          n_xtag++;
        end
        if ((|tag === 1'b1) && ~if_stage.ex_pc_set_i && (fetch_fifo64.alloc_alt !== 1'b1)) begin
          n_tag_noalloc++;
          err($sformatf("instr tagged alt_valid enters IR without ALT alloc (tag=%b)", tag));
        end
      end

      // ---------- apply ----------
      if (fetch_fifo64.apply_alt === 1'b1) begin
        int id, nv;
        logic [31:0] fb;
        n_apply++;
        id = fetch_fifo64.alt_apply_id;
        if (fetch_fifo64.alt_status[id] !== 1'b1)
          err($sformatf("apply of non-live ALT entry %0d (in_addr=%h)", id, fetch_fifo64.in_addr_i));
        if (fetch_fifo64.in_addr_i !== rec_ft[id])
          err($sformatf("apply entry %0d: restart pc %h != recorded fall-through %h (branch %h)",
                        id, fetch_fifo64.in_addr_i, rec_ft[id], rec_bpc[id]));
        fb = {fetch_fifo64.in_addr_i[31:3], 3'b000};
        nv = 0;
        for (int k = 0; k < 3; k++) begin
          if (fetch_fifo64.alt_rd_valid[k]) begin
            if (k != nv) err($sformatf("apply entry %0d: non-contiguous valid %b", id, fetch_fifo64.alt_rd_valid[2:0]));
            nv++;
            cmp_word("apply", id, k, fb+8*k, fetch_fifo64.alt_rd_rdata[k], fetch_fifo64.alt_rd_err[k], rec_bpc[id]);
          end
        end
        if (|(fetch_fifo64.alt_rd_valid[2:0] & fetch_fifo64.alt_rd_err[2:0])) n_apply_err++;
        n_apply_words[nv]++;
        if (fetch_fifo64.alt_rd_nxt_addr !== fb + 8*nv)
          err($sformatf("apply entry %0d: nxt_addr %h != %h (valid=%b, pc=%h)", id,
                        fetch_fifo64.alt_rd_nxt_addr, fb + 8*nv, fetch_fifo64.alt_rd_valid[2:0],
                        fetch_fifo64.in_addr_i));
      end

      // ---------- cancel ----------
      for (int j = 0; j < 2; j++) begin
        if (fetch_fifo64.cancel_alt[j] === 1'b1) begin
          int id;
          n_cancel++;
          id = j ? fetch_fifo64.ex_alt_ctrl_i.id1 : fetch_fifo64.ex_alt_ctrl_i.id0;
          if (fetch_fifo64.alt_status[id] !== 1'b1) begin
            n_cancel_free++;
            err($sformatf("cancel[%0d] of non-live ALT entry %0d", j, id));
          end
        end
      end

      for (int j = 0; j < 2; j++) begin
        if (fetch_fifo64.alt_status[j] === 1'b1) begin age[j]++; if (age[j] > max_age) max_age = age[j]; end
        else age[j] = 0;
      end
      if ((fetch_fifo64.flush_alt === 1'b1) && (|fetch_fifo64.alt_status) && (fetch_fifo64.apply_alt !== 1'b1))
        n_flush_live++;

      // ---------- alloc ----------
      if (fetch_fifo64.alloc_alt === 1'b1) begin
        int id, nv;
        logic [31:0] ft, bpc, fb;
        n_alloc++;
        id = fetch_fifo64.alt_free_id;
        if (fetch_fifo64.alt_status[id] !== 1'b0) err($sformatf("alloc of live ALT entry %0d", id));
        if (fetch_fifo64.apply_alt === 1'b1) err("alloc and apply in same cycle");
        if (fetch_fifo64.bp_instr0_i) begin
          bpc = fetch_fifo64.out_addr0;
          ft  = fetch_fifo64.out_addr0 + (fetch_fifo64.out_is_comp[0] ? 2 : 4);
          if (fetch_fifo64.instr_xfr == 2'b11) n_alloc_i0_xfr11++;
        end else begin
          bpc = fetch_fifo64.out_addr1;
          ft  = fetch_fifo64.out_addr1 + (fetch_fifo64.out_is_comp[1] ? 2 : 4);
          if (fetch_fifo64.instr_xfr !== 2'b11) err("alloc for instr1 without instr_xfr==11");
        end
        rec_ft[id]  = ft;
        rec_bpc[id] = bpc;
        fb = {ft[31:3], 3'b000};
        nv = 0;
        for (int k = 0; k < 3; k++) begin
          if (fetch_fifo64.valid_alt_popped[k]) begin
            if (k != nv) err("alloc: non-contiguous valid");
            nv++;
            cmp_word("alloc", id, k, fb+8*k, fetch_fifo64.rdata_alt_d[k][63:0], fetch_fifo64.err_alt_d[k], bpc);
            if (fetch_fifo64.err_alt_d[k]) n_alloc_err++;
          end
        end
        n_save_words[nv]++;
        if (fetch_fifo64.gen_alt.alt_nxt_addr_d !== fb + 8*nv)
          err($sformatf("alloc entry %0d: nxt_addr_d %h != %h (bpc=%h ft=%h valid=%b pop_alt=%b xfr=%b a16=%0d)",
                        id, fetch_fifo64.gen_alt.alt_nxt_addr_d, fb + 8*nv, bpc, ft,
                        fetch_fifo64.valid_alt_popped[2:0], fetch_fifo64.pop_alt,
                        fetch_fifo64.instr_xfr, fetch_fifo64.instr_addr16));
      end
    end
  end

  final begin
    $display("ALT_CHK SUMMARY: alloc=%0d (i0_xfr11=%0d) apply=%0d apply_req=%0d cancel=%0d cancel_free=%0d flush_live=%0d xcancel_cycles=%0d xtag_cycles=%0d tag_noalloc=%0d errors=%0d",
             n_alloc, n_alloc_i0_xfr11, n_apply, n_apply_req, n_cancel, n_cancel_free, n_flush_live, n_xcancel, n_xtag,
             n_tag_noalloc, n_err);
    $display("ALT_CHK SUMMARY: saved words 0..3 = %0d %0d %0d %0d ; applied words 0..3 = %0d %0d %0d %0d",
             n_save_words[0], n_save_words[1], n_save_words[2], n_save_words[3],
             n_apply_words[0], n_apply_words[1], n_apply_words[2], n_apply_words[3]);
    $display("ALT_CHK SUMMARY: alloc_with_err_word=%0d apply_with_err_word=%0d max_entry_age_cycles=%0d",
             n_alloc_err, n_apply_err, max_age);
    if (n_xcancel > 0 || n_xtag > 0)
      $display("ALT_CHK FAIL KUDU-044 xcancel_cycles=%0d xtag_cycles=%0d", n_xcancel, n_xtag);
    if (n_err > 0)
      $display("ALT_CHK FAIL errors=%0d", n_err);
    if (n_cyc <= RstSettle)
      $display("ALT_CHK FAIL no cycles checked");
    if (n_xcancel == 0 && n_xtag == 0 && n_err == 0 && n_cyc > RstSettle)
      $display("ALT_CHK PASS cycles=%0d alloc=%0d apply=%0d cancel=%0d", n_cyc, n_alloc, n_apply, n_cancel);
  end
endmodule

bind fetch_fifo64 alt_chk u_alt_chk();
