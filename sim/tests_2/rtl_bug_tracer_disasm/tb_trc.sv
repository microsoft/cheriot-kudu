// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Differential tracer testbench: tracer_pkg::decode_rvfi_instr_vlog (SV
// tracer) vs tracer_dpi.cpp decode_rvfi_instr (DPI-C tracer, +define+TraceDPI)
// on the same rvfi_t packet, plus a directed table of encodings whose
// disassembly must match a known-good reference on both sides.
//
// Output (one line per finding, at most +maxlog per class):
//   TRC FAIL MISMATCH class=<c> ...   the two formatters disagree
//   TRC FAIL GOLDEN class=<c> ...     a formatter disagrees with the reference
//   TRACER DISASM PASS build=<b> ...  no mismatch and no golden failure
// class (bug): cebreak (KUDU-058), amo (KUDU-057/064), clcsp (KUDU-065),
// load_f3 (KUDU-066), system/cheri1op/fencei (KUDU-067), csr/scr (KUDU-068),
// other (no known bug).
module tb_trc import cheri_pkg::*; import super_pkg::*; import tracer_pkg::*; ();
`include "tracer_dpi_wrapper.sv"
  int nmis, ntot, ngold, nfail;
  int unsigned seed;
  int unsigned maxlog;
  int mis_by_class[string];
`ifdef CHERIoT
  localparam string Build = "cheri";
  localparam int NPm = 2;
`else
  localparam string Build = "rv32";
  localparam int NPm = 1;
`endif

  function automatic logic [MemW-1:0] rnd_reg();
    logic [MemW-1:0] v;
    v = {$urandom, $urandom, $urandom};
    case ($urandom_range(0,5))
      0: v = '0;
      1: v = MemW'($urandom);
      default: ;
    endcase
    return v;
  endfunction

  function automatic logic [3:0] rnd_mask();
    case ($urandom_range(0,4))
      0,1: return 4'h0;
      2: return 4'h1 << $urandom_range(0,3);
      3: return 4'h3 << (2*$urandom_range(0,1));
      default: return 4'hf;
    endcase
  endfunction

  function automatic string classify(input logic [31:0] insn);
    logic [6:0] op;
    logic [2:0] f3;
    op = insn[6:0];
    f3 = insn[14:12];
    if (insn[1:0] != 2'b11) begin
      if (insn[15:0] == 16'h9002) return "cebreak";
      if (insn[1:0] == 2'b10 && insn[14:13] == 2'b11) return "clcsp";
      return "other";
    end
    if (op == 7'h2f) return "amo";
    if (op == 7'h03 && f3[2:1] == 2'b11) return "load_f3";
    if (op == 7'h0f && f3 == 3'b001) return "fencei";
    if (op == 7'h73 && f3 == 3'b000) return "system";
    if (op == 7'h73) return "csr";
    if (op == 7'h5b && f3 == 3'b000 && insn[31:25] == 7'h7f) return "cheri1op";
    if (op == 7'h5b && f3 == 3'b000 && insn[31:25] == 7'h01) return "scr";
    return "other";
  endfunction

  function automatic void split_tabs(input string s, ref string f[$]);
    int st;
    f.delete();
    st = 0;
    for (int i = 0; i <= s.len(); i++)
      if (i == s.len() || s[i] == "\t") begin
        f.push_back(i > st ? s.substr(st, i-1) : "");
        st = i + 1;
      end
  endfunction

  function automatic string trim(input string s);
    int a, b;
    a = 0; b = s.len() - 1;
    while (a <= b && (s[a] == " ")) a++;
    while (b >= a && (s[b] == " ")) b--;
    return (a > b) ? "" : s.substr(a, b);
  endfunction

  function automatic bit has_sub(input string s, input string sub);
    if (sub.len() == 0) return 1;
    for (int i = 0; i + sub.len() <= s.len(); i++)
      if (s.substr(i, i + sub.len() - 1) == sub) return 1;
    return 0;
  endfunction

  function automatic rvfi_t mk(input logic [31:0] insn);
    rvfi_t r;
    r = '0;
    r.valid    = 1;
    r.insn     = insn;
    r.rs1_addr = insn[19:15];
    r.rs2_addr = insn[24:20];
    r.rs3_addr = insn[31:27];
    r.rd_addr  = insn[11:7];
    r.pc_rdata = 32'h80001234;
    r.pc_wdata = 32'h80001238;
    return r;
  endfunction

  task automatic check(input logic [31:0] insn);
    rvfi_t r;
    string sv, sc, cls;
    r = mk(insn);
    r.trap     = ($urandom_range(0,9) == 0);
    r.intr     = ($urandom_range(0,39) == 0);
    if ($urandom_range(0,3)==0) begin r.rs1_addr = $urandom; r.rs2_addr = $urandom; end
    r.rs1_rdata = rnd_reg(); r.rs2_rdata = rnd_reg(); r.rs3_rdata = rnd_reg();
    r.rd_addr  = ($urandom_range(0,7)==0) ? 5'd0 : (($urandom_range(0,3)==0) ? 5'($urandom) : insn[11:7]);
    r.rd_wdata = rnd_reg();
    r.pc_rdata = $urandom & ~32'h1;
    r.pc_wdata = ($urandom_range(0,1)) ? r.pc_rdata + 4 : ($urandom & ~32'h1);
    r.mem_addr = $urandom;
    r.mem_rmask = rnd_mask();
    r.mem_wmask = rnd_mask();
    r.mem_rdata = rnd_reg();
    r.mem_wdata = rnd_reg();
    r.mem_is_cap = $urandom_range(0,1);
    for (int p = 0; p < NPm; p++) begin
      sv = decode_rvfi_instr_vlog(r, p[0]);
      sc = decode_rvfi_instr_dpi(r, p[0]);
      ntot++;
      if (sv != sc) begin
        nmis++;
        cls = classify(insn);
        if (!mis_by_class.exists(cls)) mis_by_class[cls] = 0;
        mis_by_class[cls]++;
        if (mis_by_class[cls] <= maxlog) begin
          $display("TRC FAIL MISMATCH class=%s build=%s insn=%08h pm=%0d trap=%0d intr=%0d",
                   cls, Build, insn, p, r.trap, r.intr);
          $display("    SV:[%s]", sv);
          $display("    C :[%s]", sc);
        end
      end
    end
  endtask

  // Directed check: both formatters must print PC, encoding, the expected
  // mnemonic and (if given) an operand field containing `ops`.
  task automatic golden(input logic [31:0] insn, input int pm, input string mnem,
                        input string ops);
    rvfi_t r;
    string s[2], f[$], why, side;
    if (pm >= NPm) return;
    r = mk(insn);
    s[0] = decode_rvfi_instr_vlog(r, pm[0]);
    s[1] = decode_rvfi_instr_dpi(r, pm[0]);
    for (int k = 0; k < 2; k++) begin
      side = k ? "C" : "SV";
      ngold++;
      split_tabs(s[k], f);
      why = "";
      if (f.size() < 3) why = "no PC/encoding fields";
      else if (f[0] != "80001234") why = "PC field wrong";
      else if (trim(f[1]) != (insn[1:0] == 2'b11 ? $sformatf("%08h", insn) : $sformatf("%04h", insn[15:0])))
        why = "encoding field wrong";
      else if (trim(f[2]) != mnem) why = $sformatf("mnemonic '%s' expected '%s'", trim(f[2]), mnem);
      else if (ops != "" && (f.size() < 4 || !has_sub(f[3], ops)))
        why = $sformatf("operands do not contain '%s'", ops);
      if (why != "") begin
        nfail++;
        $display("TRC FAIL GOLDEN class=%s build=%s side=%s insn=%08h pm=%0d: %s", classify(insn),
                 Build, side, insn, pm, why);
        $display("    %s:[%s]", side, s[k]);
      end
    end
  endtask

  initial begin
    logic [31:0] insn;
    if (!$value$plusargs("seed=%d", seed)) seed = 1;
    if (!$value$plusargs("maxlog=%d", maxlog)) maxlog = 3;
    void'($urandom(seed));
    nmis = 0; ntot = 0; ngold = 0; nfail = 0;

    // Directed reference table
    for (int pm = 0; pm < 2; pm++) begin
      golden(32'h00009002, pm, "c.ebreak", "");            // KUDU-058
      golden(32'h6021a0af, pm, "amoand.w", "x1,");         // KUDU-057
      golden(32'h8021a0af, pm, "amomin.w", "x1,");         // KUDU-064
      golden(32'ha021a0af, pm, "amomax.w", "x1,");
      golden(32'hc021a0af, pm, "amominu.w", "x1,");
      golden(32'he021a0af, pm, "amomaxu.w", "x1,");
      golden(32'ha00eafaf, pm, "amomax.w", "x31,");
      golden(32'h000be783, pm, "INVALID", "");             // KUDU-066
      golden(32'h000bf783, pm, "INVALID", "");
      golden(32'h00090e73, pm, "INVALID", "");             // KUDU-067
      golden(32'h0180180f, pm, "fence.i", "");
      golden(32'h00601073, pm, "csrrw", "0x006");          // KUDU-068
    end
    golden(32'h00006016, 1, "c.CH.clcsp", "320(");         // KUDU-065
    golden(32'h00006416, 1, "c.CH.clcsp", "320(");
    golden(32'h0000e226, 1, "c.CH.cscsp", "256(");
    golden(32'hff0b055b, 1, "INVALID", "");                // KUDU-067
    golden(32'h0240005b, 1, "CH.cspecialw", "scr 4");      // KUDU-068

    // Exhaustive / random differential sweep
    for (int i = 0; i < 65536; i++) if (i[1:0] != 2'b11) check(32'(i));
    for (int op = 0; op < 32; op++)
      for (int f3 = 0; f3 < 8; f3++)
        for (int f7 = 0; f7 < 128; f7++)
          for (int r2 = 0; r2 < 32; r2++) begin
            insn = {7'(f7), 5'(r2), 5'($urandom), 3'(f3), 5'($urandom), 5'(op), 2'b11};
            check(insn);
          end
    for (int c = 0; c < 4096; c++)
      for (int f3 = 0; f3 < 8; f3++) begin
        insn = {12'(c), 5'($urandom), 3'(f3), 5'($urandom), 7'h73};
        check(insn);
      end
    for (int k = 0; k < 500000; k++) check($urandom);

    foreach (mis_by_class[k])
      $display("TRC MISMATCH COUNT build=%s class=%s count=%0d", Build, k, mis_by_class[k]);
    $display("TRC SUMMARY build=%s compared=%0d mismatches=%0d golden=%0d golden_failures=%0d",
             Build, ntot, nmis, ngold, nfail);
    if (nmis == 0 && nfail == 0)
      $display("TRACER DISASM PASS build=%s compared=%0d golden=%0d", Build, ntot, ngold);
    $finish;
  end
endmodule
