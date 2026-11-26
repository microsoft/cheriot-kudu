// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Kudu capability formats (cheri_pkg) mapped to the Sail t_Capability type.
// Mirrors cheriot-ibex dv/formal/spec/cheri.sv (lowRISC contributors /
// University of Oxford, Apache-2.0), rewritten for Kudu's cheri_pkg types.
//
// Kudu's register format (reg_cap_t: exp, top9, base9) has the same B/T/E
// shape as t_Capability, so the mapping goes through the Sail decoder
// encCapabilityToCapability (from build/extracted.sv) for the permission and
// otype decoding, and then overrides E with Kudu's expanded exponent. The
// memory format (mem_cap_t, IT8) is first expanded with cheri_pkg::mem2regcap.
// The mapping is semantic: Sail's 64-bit memory encoding is never compared
// bit-for-bit against Kudu's 65-bit IT8 encoding.

function automatic t_Capability dataCap(logic [31:0] address);
  return '{
    B: '0,
    E: '0,
    T: '0,
    access_system_regs: '0,
    address: address,
    zglobal: '0,
    otype: '0,
    perm_user0: '0,
    permit_execute: '0,
    permit_load: '0,
    permit_load_global: '0,
    permit_load_mutable: '0,
    permit_load_store_cap: '0,
    permit_seal: '0,
    permit_store: '0,
    permit_store_local_cap: '0,
    permit_unseal: '0,
    reserved: '0,
    tag: '0
  };
endfunction

function automatic t_Capability nullCap();
  return dataCap(32'h0);
endfunction

// Sail register writes of capabilities go through the compressed-permission
// encoding, as in the Ibex harness.
function automatic t_Capability encodeDecodePermsOf(t_Capability capability);
  return encCapabilityToCapability(capability.tag, capToEncCap(capability));
endfunction

function automatic t_Capability regcap2sail(cheri_pkg::reg_cap_t c, logic [31:0] address);
  t_EncCapability e;
  t_Capability    s;
  e.B        = c.base9;
  e.T        = c.top9;
  e.address  = address;
  e.cE       = 4'h0;
  e.cotype   = c.otype;
  e.cperms   = c.cperms;
  e.reserved = c.rsvd;
  s   = encCapabilityToCapability(c.valid, e);
  // cE=0 makes the decode derive T[8] as a denormal; Kudu holds E and the
  // full 9-bit top explicitly, so override both.
  s.E = c.exp;
  s.T = c.top9;
  return s;
endfunction

function automatic t_Capability fullcap2sail(cheri_pkg::full_cap_t f, logic [31:0] address);
  return regcap2sail(cheri_pkg::reg_cap_t'(f[cheri_pkg::RegCapW-1:0]), address);
endfunction

// Use the _lite expansion: pcc2fullcap's set_address() clears the tag when the
// PC is outside the representable range, but Sail's PCC keeps its tag there
// (the fetch bounds fault is reported separately).
function automatic t_Capability pcc2sail(cheri_pkg::pcc_cap_t p, logic [31:0] address);
  return fullcap2sail(cheri_pkg::pcc2fullcap_lite(p, address), address);
endfunction

// Memory (IT8) format, without load-time permission stripping.
function automatic t_Capability memcap2sail(cheri_pkg::mem_cap_t m);
  cheri_pkg::reg_cap_t r;
  r        = cheri_pkg::mem2regcap(m, 4'h0);
  r.cperms = m.cperms;
  r.valid  = m.valid;
  return regcap2sail(r, m.addr);
endfunction

// A tagged capability that software can derive from the root capabilities:
// E <= cap_max_E (24) and decoded bounds 0 <= base <= top <= 2^32. Mirrors
// Sail getCapBoundsBits without the final truncation. Untagged values always
// pass.
function automatic logic cap_well_formed(t_Capability c);
  longint a_top, a_hi, t_hi, base, top;
  int     e;
  if (!c.tag) return 1'b1;
  if (c.E > 5'd24) return 1'b0;
  e     = int'(c.E);
  a_hi  = (9'((c.address >> e)) < c.B) ? 1 : 0;
  t_hi  = (c.T < c.B) ? 1 : 0;
  a_top = longint'(c.address >> (e + 9));
  base  = ((a_top - a_hi) << (e + 9)) + (longint'(c.B) << e);
  top   = ((a_top + t_hi - a_hi) << (e + 9)) + (longint'(c.T) << e);
  return (base >= 0) && (base <= top) && (top <= 64'sh1_0000_0000);
endfunction

// Field-wise equality, not relying on unpacked-struct ==.
function automatic logic cap_eq_noaddr(t_Capability a, t_Capability b);
  return (a.B == b.B) && (a.E == b.E) && (a.T == b.T) &&
         (a.access_system_regs == b.access_system_regs) &&
         (a.zglobal == b.zglobal) && (a.otype == b.otype) &&
         (a.perm_user0 == b.perm_user0) &&
         (a.permit_execute == b.permit_execute) &&
         (a.permit_load == b.permit_load) &&
         (a.permit_load_global == b.permit_load_global) &&
         (a.permit_load_mutable == b.permit_load_mutable) &&
         (a.permit_load_store_cap == b.permit_load_store_cap) &&
         (a.permit_seal == b.permit_seal) &&
         (a.permit_store == b.permit_store) &&
         (a.permit_store_local_cap == b.permit_store_local_cap) &&
         (a.permit_unseal == b.permit_unseal) &&
         (a.reserved == b.reserved) && (a.tag == b.tag);
endfunction

function automatic logic cap_eq(t_Capability a, t_Capability b);
  return cap_eq_noaddr(a, b) && (a.address == b.address);
endfunction

// Deviation (README 1.1): Kudu's PCC (pcc_cap_t) keeps only decoded
// base32/top33, so an untagged cap with E>24 (e.g. from CSetHigh, installed
// via MTCC) loses its raw B/T/E. An untagged PCC is compared on tag only
// (its address is checked as the PC).
function automatic logic pcc_eq_noaddr(t_Capability a, t_Capability b);
  if (!a.tag && !b.tag) return 1'b1;
  return cap_eq_noaddr(a, b);
endfunction

// MEPCC written by a trap comes from the same lossy PCC; relax only the
// untagged E>24 case so other untagged MEPCC values stay fully checked.
function automatic logic xepc_eq(t_Capability dut, t_Capability spec);
  if (!dut.tag && !spec.tag && spec.E > 5'd24) return dut.address == spec.address;
  return cap_eq(dut, spec);
endfunction

// 'At least as strict': the DUT may clear a tag the spec would keep. The
// relaxation is only for load-time revocation; the default environment ties
// revocation off (Env_NoRevoke), so the comparison is exact unless
// E2E_REVOKE is defined.
function automatic logic alas(t_Capability spec, t_Capability dut);
`ifdef E2E_REVOKE
  if (!dut.tag) spec.tag = 1'b0;
`endif
  return cap_eq(spec, dut);
endfunction

function automatic logic alas_noaddr(t_Capability spec, t_Capability dut);
`ifdef E2E_REVOKE
  if (!dut.tag) spec.tag = 1'b0;
`endif
  return cap_eq_noaddr(spec, dut);
endfunction

function automatic t_Capability revoke(t_Capability cap, logic strip);
  if (strip) cap.tag = 1'b0;
  return cap;
endfunction

function automatic t_Capability with_address(t_Capability cap, logic [31:0] address);
  cap.address = address;
  return cap;
endfunction

// Kudu mie_q/mip (irqs_t) to the RISC-V mie/mip layout.
function automatic logic [31:0] irqsToMInterrupts(csr_pkg::irqs_t i);
  return (32'(i.irq_software) << 3) |
         (32'(i.irq_timer)    << 7) |
         (32'(i.irq_external) << 11) |
         (32'(i.irq_fast)     << 16);
endfunction

// Kudu's 6-bit mcause_q to the 32-bit mcause value.
function automatic logic [31:0] widenMCause(logic [5:0] m);
  return {m[5], 26'b0, m[4:0]};
endfunction

function automatic t_Privilege priv2sail(csr_pkg::priv_lvl_e p);
  return (p == csr_pkg::PRIV_LVL_M) ? Machine : User;
endfunction
