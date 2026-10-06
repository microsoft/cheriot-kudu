// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FC_ISA_CSR -- architectural trap, interrupt, debug and CSR behaviour.
// Bound to rtl/cs_registers.sv.
// See doc/functional_coverage_plan.md section 7.

module kudu_fcov_csr
  import super_pkg::*;
  import csr_pkg::*;
  import cheri_pkg::*;
  import kudu_fcov_pkg::*;
#(
  parameter bit          CHERIoTEn      = 1'b1,
  parameter bit          DbgTriggerEn   = 1'b1,
  parameter bit          PMPEnable      = 1'b0,
  parameter int unsigned MHPMCounterNum = 0
) (
  input logic        clk_i,
  input logic        rst_ni,

  // --- trap entry / return ---------------------------------------------------
  input logic        csr_save_cause_i,
  input logic        csr_restore_mret_i,
  input logic        csr_restore_dret_i,
  input logic [5:0]  mcause_d,
  input logic        mcause_en,
  input logic [31:0] mtval_d,
  input logic        mtval_en,

  // --- mstatus ---------------------------------------------------------------
  input logic        mstatus_mie,
  input logic        mstatus_mpie,
  input logic [1:0]  mstatus_mpp,
  input logic        mstatus_en,
  input logic [1:0]  priv_mode,

  // --- interrupts ------------------------------------------------------------
  input logic        irq_pending_o,
  input irqs_t       irqs_o,

  // --- debug -----------------------------------------------------------------
  input logic        debug_mode_i,
  input logic        debug_mode_entering_i,
  input dbg_cause_e  debug_cause_i,
  input logic        debug_csr_save_i,
  input logic        dcsr_step,
  input logic        dcsr_stepie,
  input logic        dcsr_ebreakm,
  input logic        dcsr_ebreaku,
  input logic        dcsr_nmip,
  input logic [1:0]  dcsr_prv,
  input logic        dcsr_en,
  input logic        tmatch_control,

  // --- CSR access ------------------------------------------------------------
  input logic        csr_access_i,
  input logic        csr_cheri_i,
  input csr_num_e    csr_addr_i,
  input csr_op_e     csr_op_i,
  input logic        csr_op_en_i,
  input logic        illegal_csr_insn_o,
  // cs_registers-internal illegal-access causes (connected by .*)
  input logic        illegal_csr,        // CSR address not implemented/accessible
  input logic        illegal_csr_cheri,  // SCR address not implemented/accessible
  input logic        illegal_csr_priv,   // CSR privilege above current mode
  input logic        illegal_csr_write   // write to a read-only CSR
);

`ifndef KUDU_FCOV_OFF

  // The CSR block already qualifies runtime mode with its CHERIoTEn parameter.
  wire cheri_cov_en = cs_registers.cheri_pmode;

  // One cycle per executed CSR/SCR instruction (csr_op_en_i is the LSU's
  // single-cycle go pulse) that the CSR block accepted as legal.
  wire csr_exec_ok = csr_op_en_i && !illegal_csr_insn_o;
  // Every executed CSR/SCR instruction, legal or not.
  wire csr_exec    = csr_op_en_i && csr_access_i;
  wire csr_is_wr   = csr_op_i inside {CSR_OP_WRITE, CSR_OP_SET, CSR_OP_CLEAR};

  // Addresses cs_registers decodes without raising illegal_csr for this
  // hardware configuration.  Mode/debug-mode legality (MTVEC/MEPC only in
  // RV32 mode, MSHWM* only in CHERI mode, D* only in debug mode) is enforced
  // at runtime by sampling only legal accesses.  Keep in sync with the read
  // mux in rtl/cs_registers.sv.
  function automatic bit fcov_csr_implemented(csr_num_e a);
    unique case (a) inside
      CSR_MVENDORID, CSR_MARCHID, CSR_MIMPID, CSR_MHARTID,
      CSR_MSTATUS, CSR_MISA, CSR_MIE, CSR_MTVEC, CSR_MCOUNTEREN,
      CSR_MSCRATCH, CSR_MEPC, CSR_MCAUSE, CSR_MTVAL, CSR_MIP,
      CSR_DCSR, CSR_DPC, CSR_DSCRATCH0, CSR_DSCRATCH1,
      CSR_MCOUNTINHIBIT, CSR_MCYCLE, CSR_MINSTRET, CSR_MCYCLEH, CSR_MINSTRETH,
      CSR_CPUCTRL, CSR_SECURESEED:
        return 1'b1;
      [CSR_PMPCFG0:CSR_PMPCFG3], [CSR_PMPADDR0:CSR_PMPADDR15],
      CSR_MSECCFG, CSR_MSECCFGH:
        return PMPEnable;
      [CSR_MHPMEVENT3:CSR_MHPMEVENT31], [CSR_MHPMCOUNTER3:CSR_MHPMCOUNTER31],
      [CSR_MHPMCOUNTER3H:CSR_MHPMCOUNTER31H]:
        return 32'(a[4:0]) <= MHPMCounterNum + 2;
      CSR_TSELECT, CSR_TDATA1, CSR_TDATA2, CSR_TDATA3, CSR_MCONTEXT, CSR_SCONTEXT:
        return DbgTriggerEn;
      CSR_MSHWM, CSR_MSHWMB, CSR_CDBG_CTRL:
        return CHERIoTEn;
      default:
        return 1'b0;
    endcase
  endfunction

  // ==========================================================================
  // FC_ISA_CSR - architectural trap, interrupt and CSR state
  // ==========================================================================
  covergroup cg_isa_csr @(posedge clk_i iff rst_ni);
    option.per_instance = 1;
    option.name         = "FC_ISA_CSR";

    // Every architectural trap cause the design can raise.  This is the
    // 100%-required coverpoint of FC_ISA_CSR.
    cp_cause: coverpoint mcause_d iff (mcause_en) {
      bins insn_addr_misa   = {EXC_CAUSE_INSN_ADDR_MISA};
      bins instr_access     = {EXC_CAUSE_INSTR_ACCESS_FAULT};
      bins illegal_insn     = {EXC_CAUSE_ILLEGAL_INSN};
      bins breakpoint       = {EXC_CAUSE_BREAKPOINT};
      bins load_misalign    = {EXC_CAUSE_LOAD_ADDR_MISALIGN};
      bins load_fault       = {EXC_CAUSE_LOAD_ACCESS_FAULT};
      bins store_misalign   = {EXC_CAUSE_STORE_ADDR_MISALIGN};
      bins store_fault      = {EXC_CAUSE_STORE_ACCESS_FAULT};
      bins ecall_u          = {EXC_CAUSE_ECALL_UMODE};
      bins ecall_m          = {EXC_CAUSE_ECALL_MMODE};
      bins cheri_fault      = {EXC_CAUSE_CHERI_FAULT} iff (cheri_cov_en);
      bins irq_software     = {EXC_CAUSE_IRQ_SOFTWARE_M};
      bins irq_timer        = {EXC_CAUSE_IRQ_TIMER_M};
      bins irq_external     = {EXC_CAUSE_IRQ_EXTERNAL_M};
      bins irq_nm           = {EXC_CAUSE_IRQ_NM};
      bins irq_fast         = {[6'h30:6'h3e]};
      bins other            = default;
    }

    cp_save_cause: coverpoint csr_save_cause_i { bins hit = {1'b1}; }
    cp_mret:       coverpoint csr_restore_mret_i { bins hit = {1'b1}; }
    cp_dret:       coverpoint csr_restore_dret_i { bins hit = {1'b1}; }

    // mtval is only meaningful for the faults that define it; a non-zero
    // value must be seen or the fault-address capture path is untested.
    cp_mtval: coverpoint (mtval_d != 32'h0) iff (mtval_en) {
      bins zero     = {1'b0};
      bins non_zero = {1'b1};
    }

    cp_mstatus_mie:  coverpoint mstatus_mie;
    cp_mstatus_mpie: coverpoint mstatus_mpie;
    cp_mstatus_mpp:  coverpoint mstatus_mpp { bins p[] = {[0:3]}; }
    cp_mstatus_en:   coverpoint mstatus_en { bins hit = {1'b1}; }
    cp_priv_mode:    coverpoint priv_mode { bins p[] = {[0:3]}; }

    // Taking a trap while already in a trap handler (interrupts disabled) is
    // the nested-fault case.
    cp_trap_with_mie_clear: coverpoint (csr_save_cause_i & ~mstatus_mie) {
      bins hit = {1'b1};
    }
    cp_pending:  coverpoint irq_pending_o;
    // irqs_o is already qualified by mie, so this is the architectural
    // "interrupt is deliverable" view rather than the raw pin state.
    cp_software: coverpoint irqs_o.irq_software;
    cp_timer:    coverpoint irqs_o.irq_timer;
    cp_external: coverpoint irqs_o.irq_external;
    cp_fast_id: coverpoint irqs_o.irq_fast {
      wildcard bins f0  = {15'b??????????????1};
      wildcard bins f1  = {15'b?????????????1?};
      wildcard bins f2  = {15'b????????????1??};
      wildcard bins f3  = {15'b???????????1???};
      wildcard bins f4  = {15'b??????????1????};
      wildcard bins f5  = {15'b?????????1?????};
      wildcard bins f6  = {15'b????????1??????};
      wildcard bins f7  = {15'b???????1???????};
      wildcard bins f8  = {15'b??????1????????};
      wildcard bins f9  = {15'b?????1?????????};
      wildcard bins f10 = {15'b????1??????????};
      wildcard bins f11 = {15'b???1???????????};
      wildcard bins f12 = {15'b??1????????????};
      wildcard bins f13 = {15'b?1?????????????};
      wildcard bins f14 = {15'b1??????????????};
      bins none = {15'h0};
    }
    // An interrupt pending while MIE is clear must not be taken; both halves
    // of that check need to be seen.
    cp_pending_mie_clear: coverpoint (irq_pending_o & ~mstatus_mie) { bins hit = {1'b1}; }
    cp_debug_mode:  coverpoint debug_mode_i;
    cp_entering:    coverpoint debug_mode_entering_i { bins hit = {1'b1}; }
    // Every architectural debug entry cause.
    cp_dbg_cause: coverpoint debug_cause_i iff (debug_csr_save_i) {
      bins none    = {DBG_CAUSE_NONE};
      bins ebreak  = {DBG_CAUSE_EBREAK};
      bins trigger = {DBG_CAUSE_TRIGGER};
      bins haltreq = {DBG_CAUSE_HALTREQ};
      bins step    = {DBG_CAUSE_STEP};
    }
    cp_step:     coverpoint dcsr_step;
    cp_stepie:   coverpoint dcsr_stepie;
    cp_ebreakm:  coverpoint dcsr_ebreakm;
    cp_ebreaku:  coverpoint dcsr_ebreaku;
    cp_dcsr_nmip: coverpoint dcsr_nmip;
    cp_dcsr_prv: coverpoint dcsr_prv { bins p[] = {[0:3]}; }
    cp_dcsr_en:  coverpoint dcsr_en { bins hit = {1'b1}; }
    cp_trigger_en: coverpoint tmatch_control;

    // Single-stepping with interrupts enabled is the case where an interrupt
    // and the step trap compete (finding F-06).
    cp_step_with_ie: coverpoint (dcsr_step & dcsr_stepie) { bins hit = {1'b1}; }
    // Every implemented CSR address, each crossed with every access kind.
    // READ is CSRRS/CSRRC with rs1 = x0; WRITE/SET/CLEAR are CSRRW[I],
    // CSRRS[I] and CSRRC[I] with a non-zero source.
    cp_csr_addr: coverpoint csr_addr_i iff (csr_exec_ok && !csr_cheri_i) {
      bins csr[] = {
        CSR_MVENDORID, CSR_MARCHID, CSR_MIMPID, CSR_MHARTID,
        CSR_MSTATUS, CSR_MISA, CSR_MIE, CSR_MTVEC, CSR_MCOUNTEREN,
        CSR_MSCRATCH, CSR_MEPC, CSR_MCAUSE, CSR_MTVAL, CSR_MIP,
        [CSR_PMPCFG0:CSR_PMPCFG3], [CSR_PMPADDR0:CSR_PMPADDR15],
        CSR_MSECCFG, CSR_MSECCFGH,
        CSR_TSELECT, CSR_TDATA1, CSR_TDATA2, CSR_TDATA3, CSR_MCONTEXT, CSR_SCONTEXT,
        CSR_DCSR, CSR_DPC, CSR_DSCRATCH0, CSR_DSCRATCH1,
        CSR_MCOUNTINHIBIT, [CSR_MHPMEVENT3:CSR_MHPMEVENT31],
        CSR_MCYCLE, CSR_MINSTRET, [CSR_MHPMCOUNTER3:CSR_MHPMCOUNTER31],
        CSR_MCYCLEH, CSR_MINSTRETH, [CSR_MHPMCOUNTER3H:CSR_MHPMCOUNTER31H],
        CSR_MSHWM, CSR_MSHWMB, CSR_CDBG_CTRL, CSR_CPUCTRL, CSR_SECURESEED
      } with (fcov_csr_implemented(csr_num_e'(item)));
    }
    cp_csr_op: coverpoint csr_op_i iff (csr_exec_ok && !csr_cheri_i) {
      bins read  = {CSR_OP_READ};
      bins write = {CSR_OP_WRITE};
      bins set   = {CSR_OP_SET};
      bins clear = {CSR_OP_CLEAR};
    }
    // Writes to the read-only machine-information CSRs trap (addr[11:10] ==
    // 2'b11) and are therefore never sampled here.
    x_csr_addr_op: cross cp_csr_addr, cp_csr_op {
      ignore_bins ro_write =
        binsof(cp_csr_addr) intersect {CSR_MVENDORID, CSR_MARCHID, CSR_MIMPID, CSR_MHARTID} &&
        binsof(cp_csr_op)   intersect {CSR_OP_WRITE, CSR_OP_SET, CSR_OP_CLEAR};
    }

    // Illegal-access causes, each with read and write accesses.  The
    // causes are not exclusive (e.g. a U-mode access to an unimplemented
    // address sets both illegal_csr and illegal_csr_priv).  illegal_csr is
    // only selected for CSR accesses and illegal_csr_cheri for SCR accesses
    // (cs_registers illegal_csr_addr); SCR addresses are {7'h0, scr} and so
    // never set illegal_csr_priv or illegal_csr_write.
    cp_illegal_csr: coverpoint csr_is_wr
      iff (csr_exec && !csr_cheri_i && illegal_csr) {
      bins read  = {1'b0};
      bins write = {1'b1};
    }
    cp_illegal_scr: coverpoint csr_is_wr
      iff (csr_exec && csr_cheri_i && illegal_csr_cheri) {
      option.weight = CHERIoTEn;
      bins read  = {1'b0};
      bins write = {1'b1};
    }
    cp_illegal_csr_priv: coverpoint csr_is_wr
      iff (csr_exec && !csr_cheri_i && illegal_csr_priv) {
      bins read  = {1'b0};
      bins write = {1'b1};
    }
    // A write (WRITE, or SET/CLEAR with a non-zero source) to a read-only
    // CSR (addr[11:10] == 2'b11); illegal_csr_write already implies a write.
    cp_illegal_csr_write: coverpoint illegal_csr_write
      iff (csr_exec && !csr_cheri_i) {
      bins hit = {1'b1};
    }

    // CHERI special capability registers (CSpecialRW).  The LSU issues READ
    // for rs1 = c0 and WRITE otherwise; there is no set/clear form.
    cp_scr_addr: coverpoint csr_addr_i[4:0] iff (csr_exec_ok && csr_cheri_i) {
      option.weight = CHERIoTEn;
      bins mtcc       = {CHERI_SCR_MTCC};
      bins mtdc       = {CHERI_SCR_MTDC};
      bins mscratchc  = {CHERI_SCR_MSCRATCHC};
      bins mepcc      = {CHERI_SCR_MEPCC};
      bins depcc      = {CHERI_SCR_DEPCC};
      bins dscratchc0 = {CHERI_SCR_DSCRATCHC0};
      bins dscratchc1 = {CHERI_SCR_DSCRATCHC1};
    }
    cp_scr_op: coverpoint csr_op_i iff (csr_exec_ok && csr_cheri_i) {
      option.weight = CHERIoTEn;
      bins read  = {CSR_OP_READ};
      bins write = {CSR_OP_WRITE};
    }
    x_scr_addr_op: cross cp_scr_addr, cp_scr_op {
      option.weight = CHERIoTEn;
    }
    cp_op:   coverpoint csr_op_i iff (csr_access_i);
    cp_op_en: coverpoint csr_op_en_i iff (csr_access_i);
    // A read-only access (rd == x0 for a set/clear, or op_en low) must not
    // have side effects.
    cp_read_only: coverpoint (csr_access_i & ~csr_op_en_i) { bins hit = {1'b1}; }
    cp_illegal: coverpoint illegal_csr_insn_o iff (csr_access_i) {
      bins legal   = {1'b0};
      bins illegal = {1'b1};
    }
    // Accessing a debug CSR outside debug mode is architecturally illegal.
    cp_dbg_csr_outside_dm: coverpoint (csr_access_i & ~debug_mode_i &
                                       (12'(csr_addr_i) >= 12'h7b0) &
                                       (12'(csr_addr_i) <= 12'h7b3)) {
      bins hit = {1'b1};
    }
  endgroup

  cg_isa_csr u_cg_isa_csr = new();

`endif  // KUDU_FCOV_OFF

endmodule
