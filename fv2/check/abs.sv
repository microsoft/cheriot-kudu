// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abstraction function (README section 4.2): committed Kudu architectural
// state mapped to the Sail types used by kudu_spec_api. Included inside
// kudu_e2e_top. Mirrors cheriot-ibex dv/formal/check/peek/abs.sv.
//
// These values are the spec pre-state for the very first step (before any
// spec_past_* state exists) and the reference for the continuity checks at
// points where Kudu's pipeline is drained (CSM_ISSUE_SPECIAL and the cycle
// after a trap/serialised instruction).

t_Privilege    dut_priv;
kudu_mstatus_t dut_mstatus;
logic [31:0]   dut_mie;
logic [31:0]   dut_mip;
logic [31:0]   dut_mcause;
logic [31:0]   dut_mtval;
logic [31:0]   dut_mscratch;
logic [31:0]   dut_mshwm;
logic [31:0]   dut_mshwmb;
logic [31:0]   dut_misa;
t_Capability   dut_mtvec;
t_Capability   dut_mepc;
t_Capability   dut_mscratchc;
t_Capability   dut_mtdc;

cheri_pkg::reg_cap_t dut_mtvec_rc, dut_mepc_rc, dut_mscratchc_rc, dut_mtdc_rc;

assign dut_mtvec_rc     = cheri_pkg::reg_cap_t'(`KCSR.mtvec_q);
assign dut_mepc_rc      = cheri_pkg::reg_cap_t'(`KCSR.mepc_q);
assign dut_mscratchc_rc = cheri_pkg::reg_cap_t'(`KCSR.mscratchc_q);
assign dut_mtdc_rc      = cheri_pkg::reg_cap_t'(`KCSR.mtdc_q);

assign dut_priv         = priv2sail(`KCSR.priv_lvl_q);
assign dut_mstatus.mie  = `KCSR.mstatus_q.mie;
assign dut_mstatus.mpie = `KCSR.mstatus_q.mpie;
assign dut_mstatus.tw   = `KCSR.mstatus_q.tw;
assign dut_mstatus.mprv = `KCSR.mstatus_q.mprv;
assign dut_mstatus.mpp  = `KCSR.mstatus_q.mpp;
assign dut_mie          = irqsToMInterrupts(`KCSR.mie_q);
assign dut_mip          = irqsToMInterrupts(`KCSR.mip);
assign dut_mcause       = widenMCause(`KCSR.mcause_q);
assign dut_mtval        = `KCSR.mtval_q;
assign dut_mscratch     = `KCSR.mscratch_q;
assign dut_mshwm        = `KCSR.mshwm_q;
assign dut_mshwmb       = `KCSR.mshwmb_q;
assign dut_misa         = `KCSR.misa_value_masked;
assign dut_mtvec        = regcap2sail(dut_mtvec_rc,     dut_mtvec_rc.addr);
assign dut_mepc         = regcap2sail(dut_mepc_rc,      dut_mepc_rc.addr);
assign dut_mscratchc    = regcap2sail(dut_mscratchc_rc, dut_mscratchc_rc.addr);
assign dut_mtdc         = regcap2sail(dut_mtdc_rc,      dut_mtdc_rc.addr);

// The committed PCC (cs_registers ex1_pcc_cap_q) as a Sail capability whose
// address is the given PC.
function automatic t_Capability dut_pcc_at(logic [31:0] pc);
  return pcc2sail(`KCSR.ex1_pcc_cap_q, pc);
endfunction

// A full_cap_t operand (ira/irb_full_data2_fwd) as a Sail capability.
function automatic t_Capability op2sail(cheri_pkg::full_cap_t f);
  return fullcap2sail(f, f[31:0]);
endfunction

// A RegW register-file write value as a Sail capability.
function automatic t_Capability rfw2sail(logic [super_pkg::RegW-1:0] w);
  cheri_pkg::reg_cap_t r;
  r = cheri_pkg::reg_cap_t'(w);
  return regcap2sail(r, r.addr);
endfunction

// Sail instruction bits: the raw (not expanded) instruction, as in Ibex.
function automatic logic [31:0] insn_bits_of(super_pkg::ir_dec_t d);
  return d.is_comp ? {16'h0, d.c_insn} : d.insn;
endfunction
