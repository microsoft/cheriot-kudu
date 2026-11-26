// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Instruction-fetch consistency (README section 4.4, "Instruction fetch").
//
// Sail decodes the bits Kudu issues (insn_bits_of(ir_dec), abs.sv), so the
// rest of the harness would accept a front end that issues the wrong bits for
// a PC (wrong lane, wrong word, stale ALT data). This file ties the issued
// bits to the instruction memory seen on the bus.
//
// Memory model: one frozen symbolic halfword address fch_a (free, never
// changes) holds the frozen symbolic value fch_h. Every fetch response whose
// granted address covers fch_a returns fch_h in that lane; all other data
// stays free. Since fch_a/fch_h are arbitrary, proving the checks below for
// all of them proves that every issued halfword equals the memory halfword
// at its PC, for any memory that is constant while it is fetched (no
// self-modifying code, see README section 6).
//
// Included from top.sv after inv.sv (uses g_s0n, g_s0e, GS0W).

`define FPF `KDUT.if_stage_i.prefetch_buffer_i
`define KFF `FPF.fifo_i

logic [31:1] fch_a;
logic [15:0] fch_h;
always_ff @(posedge clk_i) begin
  fch_a <= fch_a;
  fch_h <= fch_h;
end

// Bus address of the request answered this cycle (one response, the cycle
// after its grant), and of the response held in the prefetch input register
// (IfRdataBypass = 0: instr_rdata_in is instr_rdata_i delayed one cycle).
logic [31:0] fch_rsp_addr, fch_in_addr;
always_ff @(posedge clk_i) begin
  if (instr_req_o && instr_gnt_i)
    fch_rsp_addr <= instr_addr_o;
  fch_in_addr <= fch_rsp_addr;
end

// The 16-bit lane of a 64-bit fetch word at word address w that covers fch_a
// holds fch_h (vacuous for other words).
function automatic logic fch_word_ok(logic [63:0] d, logic [31:3] w);
  logic [63:0] s;
  s = d >> {fch_a[2:1], 4'b0};
  return (w != fch_a[31:3]) || (s[15:0] == fch_h);
endfunction

function automatic logic fch_hw_ok(logic [31:0] pc, logic [15:0] v);
  return (pc[31:1] != fch_a) || (v == fch_h);
endfunction

// Raw fetch-side entry (fetch_fifo64 out_instr / s0 FIFO; IfCompDecEn = 0, so
// insn is the raw 32 bits at pc, upper half is the next parcel).
function automatic logic fch_raw_ok(super_pkg::ir_reg_t r);
  return fch_hw_ok(r.pc, r.insn[15:0]) &&
         (r.is_comp || fch_hw_ok(r.pc + 32'd2, r.insn[31:16]));
endfunction

// Decoded entry: c_insn is the raw compressed parcel; a 32-bit insn passes the
// compressed decoder unchanged. These are exactly Sail's insn_bits_of bits.
function automatic logic fch_dec_ok(super_pkg::ir_dec_t d);
  return d.is_comp ? fch_hw_ok(d.pc, d.c_insn) :
                     (fch_hw_ok(d.pc, d.insn[15:0]) && fch_hw_ok(d.pc + 32'd2, d.insn[31:16]));
endfunction

Env_FetchMem: assume property (instr_rvalid_i |-> fch_word_ok(instr_rdata_i, fch_rsp_addr[31:3]));

////////////////////// Checks: issued bits == memory //////////////////////

Fetch_Iss0: assert property (s0_upd && (s0_mode == MAIN_IDEX) |-> fch_dec_ok(s0_dec));
Fetch_Iss1: assert property (s1_upd |-> fch_dec_ok(s1_dec));

C_FetchIss32:  cover property (s0_upd && (s0_mode == MAIN_IDEX) && !s0_dec.is_comp && (s0_dec.pc[31:1] == fch_a));
C_FetchIssC:   cover property (s0_upd && (s0_mode == MAIN_IDEX) &&  s0_dec.is_comp && (s0_dec.pc[31:1] == fch_a));
C_FetchIssHi:  cover property (s0_upd && (s0_mode == MAIN_IDEX) && !s0_dec.is_comp && (s0_dec.pc[31:1] + 31'd1 == fch_a));
C_FetchIssX:   cover property (s0_upd && (s0_mode == MAIN_IDEX) && !s0_dec.is_comp && (s0_dec.pc[2:1] == 2'd3) &&
                               (s0_dec.pc[31:1] + 31'd1 == fch_a));
C_FetchIss1:   cover property (s1_upd && (s1_dec.pc[31:1] == fch_a));

////////////////////// Group G (fetch data): helper invariants //////////////////////

// Address bookkeeping. W(x) = x[31:3] is a fetch word address. The fifo
// holds words fifo_base + i (i < fifo_cnt); the input register and the bus
// response (when not discarded by a branch) are the next words, then the held
// or next request.
localparam int FFD = int'(KuduE2eCfg.PrefetchDepth) + (KuduE2eCfg.AltEnable ? 4 : 1);
logic [31:3] fch_base, fch_tail, fch_nxt;
logic [3:0]  fch_cnt;
logic        fch_pin, fch_pbus;
assign fch_base = `KFF.instr_addr_q[31:3];
assign fch_cnt  = 4'($countones(`KFF.valid_q));
assign fch_tail = fch_base + 29'(fch_cnt);
assign fch_pin  = `FPF.instr_rvalid_in && !`FPF.branch_discard_q[0];
assign fch_pbus = instr_rsp_due && !`FPF.branch_discard_q[`FPF.instr_rvalid_in ? 1 : 0];
assign fch_nxt  = fch_tail + 29'(fch_pin) + 29'(fch_pbus);

Inv_G_FVThm:  assert property (((`KFF.valid_q + 1'b1) & `KFF.valid_q) == '0);
// Outstanding requests are exactly the input register and the due response.
Inv_G_FOut:   assert property (`FPF.rdata_outstanding_q ==
                               ((`FPF.instr_rvalid_in && instr_rsp_due) ? 3'b011 :
                                (`FPF.instr_rvalid_in || instr_rsp_due) ? 3'b001 : 3'b000));
// fifo_ready only requests while the fifo has room for every outstanding
// (or held) response.
Inv_G_FRoom:  assert property (5'(fch_cnt) + 5'($countones(`FPF.rdata_outstanding_q)) +
                               5'(`FPF.valid_req_q) <= 5'(FFD));
Inv_G_FDisc:  assert property ((`FPF.branch_discard_q & ~`FPF.rdata_outstanding_q) == '0);
Inv_G_FInD:   assert property (`FPF.instr_rvalid_in |-> fch_word_ok(`FPF.instr_rdata_in, fch_in_addr[31:3]));
Inv_G_FInA:   assert property (fch_pin |-> fch_in_addr[31:3] == fch_tail);
Inv_G_FBusA:  assert property (fch_pbus |-> fch_rsp_addr[31:3] == fch_tail + 29'(fch_pin));
Inv_G_FHeld:  assert property (`FPF.valid_req_q && !`FPF.discard_req_q |->
                               (`FPF.stored_addr_q[31:3] == fch_nxt) &&
                               (`FPF.fetch_addr_q[31:3] == fch_nxt + 29'd1));
Inv_G_FNext:  assert property (!(`FPF.valid_req_q && !`FPF.discard_req_q) |->
                               `FPF.fetch_addr_q[31:3] == fch_nxt);
for (genvar i = 0; i < FFD; i++) begin : g_inv_fq
  Inv_G_FQD: assert property (`KFF.valid_q[i] |-> fch_word_ok(`KFF.rdata_q[i][63:0], fch_base + 29'(i)));
end

// ALT table: a live entry holds the words just below nxt_addr; an IR entry
// that owns it falls through to the first of them.
function automatic logic [31:3] fch_alt_base(int unsigned j);
  return `KFF.gen_alt.alt_table[j].nxt_addr[31:3] -
         29'($countones(`KFF.gen_alt.alt_table[j].valid));
endfunction
for (genvar j = 0; j < 2; j++) begin : g_inv_falt
  Inv_G_FAltThm: assert property (`KFF.alt_status[j] |->
                                  ((`KFF.gen_alt.alt_table[j].valid + 1'b1) & `KFF.gen_alt.alt_table[j].valid) == '0);
  for (genvar k = 0; k < 3; k++) begin : g_k
    Inv_G_FAltD: assert property (`KFF.alt_status[j] && `KFF.gen_alt.alt_table[j].valid[k] |->
                                  fch_word_ok(`KFF.gen_alt.alt_table[j].rdata[k][63:0], fch_alt_base(j) + 29'(k)));
  end
end
for (genvar i = 0; i < int'(KuduE2eCfg.IrS0Depth); i++) begin : g_inv_fs0
  Inv_G_FS0D:   assert property (GS0W'(i) < g_s0n |-> fch_raw_ok(g_s0e[i]));
  Inv_G_FS0Alt: assert property (GS0W'(i) < g_s0n && g_s0e[i].alt_valid |->
                                 `KFF.alt_status[g_s0e[i].alt_id[0]] &&
                                 (fch_alt_base(g_s0e[i].alt_id[0]) ==
                                  29'((g_s0e[i].pc + (g_s0e[i].is_comp ? 32'd2 : 32'd4)) >> 3)));
end
// An ALT id has at most one in-flight owner (s0 entries, IR0, IR1): an id is
// freed only by cancel/apply/flush of its owner and re-allocated when free.
localparam int FAO = int'(KuduE2eCfg.IrS0Depth) + 2;
for (genvar j = 0; j < 2; j++) begin : g_inv_faltu
  logic [FAO-1:0] own;
  for (genvar i = 0; i < int'(KuduE2eCfg.IrS0Depth); i++) begin : g_o
    assign own[i] = (GS0W'(i) < g_s0n) && g_s0e[i].alt_valid && (g_s0e[i].alt_id[0] == j[0]);
  end
  assign own[FAO-2] = `KDUT.ir_valid[0] && `KISS.ir0_dec.alt_valid && (`KISS.ir0_dec.alt_id[0] == j[0]);
  assign own[FAO-1] = `KDUT.ir_valid[1] && `KISS.ir1_dec.alt_valid && (`KISS.ir1_dec.alt_id[0] == j[0]);
  Inv_G_FAltU: assert property ($countones(own) <= 1);
end
Inv_G_FIr0D:   assert property (`KDUT.ir_valid[0] |-> fch_dec_ok(`KISS.ir0_dec));
Inv_G_FIr1D:   assert property (`KDUT.ir_valid[1] |-> fch_dec_ok(`KISS.ir1_dec));
Inv_G_FIr0Alt: assert property (`KDUT.ir_valid[0] && `KISS.ir0_dec.alt_valid |->
                                `KFF.alt_status[`KISS.ir0_dec.alt_id[0]] &&
                                (fch_alt_base(`KISS.ir0_dec.alt_id[0]) ==
                                 29'((`KISS.ir0_dec.pc + (`KISS.ir0_dec.is_comp ? 32'd2 : 32'd4)) >> 3)));
Inv_G_FIr1Alt: assert property (`KDUT.ir_valid[1] && `KISS.ir1_dec.alt_valid |->
                                `KFF.alt_status[`KISS.ir1_dec.alt_id[0]] &&
                                (fch_alt_base(`KISS.ir1_dec.alt_id[0]) ==
                                 29'((`KISS.ir1_dec.pc + (`KISS.ir1_dec.is_comp ? 32'd2 : 32'd4)) >> 3)));

`undef KFF
`undef FPF
