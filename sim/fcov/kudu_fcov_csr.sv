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
  input logic        illegal_csr_write,  // write to a read-only CSR
  // cs_registers-internal enables/strobes (connected by .*)
  input logic        mepc_en,
  input logic        mshwm_en,
  input logic        mshwmb_en,
  input logic        csr_lsu_wr_req_i,
  input logic        instr_ret_i
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
  // KUDU-022/027: a trap taken in debug mode, or debug entry itself, must not
  // update mcause/mepc (cs_registers.sv save-cause and mepc_en logic). A
  // concurrent CSR write is excluded as it is a separate legal writer.
  wire dm_trap         = csr_save_cause_i && (debug_mode_i || debug_csr_save_i);
  wire dm_trap_m_write = dm_trap && !csr_op_en_i && (mcause_en || mepc_en);

  // KUDU-016: cycles since the last MSHWM/MSHWMB CSR write when a store
  // response requests the LSU MSHWM update (0 = same cycle, saturates at 3).
  logic [1:0] mshwm_wr_age_q;
  wire        mshwm_wr = mshwm_en || mshwmb_en;
  wire [1:0]  mshwm_wr_age = mshwm_wr ? 2'd0 : mshwm_wr_age_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                      mshwm_wr_age_q <= 2'd3;
    else if (mshwm_wr)                mshwm_wr_age_q <= 2'd1;
    else if (mshwm_wr_age_q != 2'd3)  mshwm_wr_age_q <= mshwm_wr_age_q + 2'd1;
  end

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
    // mpp/priv are WARL {U, M} (cs_registers.sv:674-676,766,783,808,818,867);
    // AssertMppLegal / AssertPrivLegal in kudu_sva_csr.
    cp_mstatus_mpp:  coverpoint mstatus_mpp {
      bins         p[]    = {0, 3};
      illegal_bins rsvd   = {1, 2};
    }
    cp_mstatus_en:   coverpoint mstatus_en { bins hit = {1'b1}; }
    cp_priv_mode:    coverpoint priv_mode {
      bins         p[]    = {0, 3};
      illegal_bins rsvd   = {1, 2};
    }

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
    // Tied to 1'b0 at kudu_top.sv:656; AssertDbgEnteringTiedOff.
    cp_entering:    coverpoint debug_mode_entering_i {
      bins         idle = {1'b0};
      illegal_bins hit  = {1'b1};
    }
    // Every architectural debug entry cause.
    cp_dbg_cause: coverpoint debug_cause_i iff (debug_csr_save_i) {
      bins none    = {DBG_CAUSE_NONE};
      bins ebreak  = {DBG_CAUSE_EBREAK};
      bins trigger = {DBG_CAUSE_TRIGGER};
      bins haltreq = {DBG_CAUSE_HALTREQ};
      bins step    = {DBG_CAUSE_STEP};
    }
    cp_step:     coverpoint dcsr_step;
    // dcsr.stepie/nmip are hardwired 0 and dcsr.prv is WARL {U, M}
    // (cs_registers.sv:648,695-697,703,706,771,956-960);
    // AssertDcsrFixedFields / AssertDcsrPrvLegal in kudu_sva_csr.
    cp_stepie:   coverpoint dcsr_stepie { bins zero = {1'b0}; illegal_bins one = {1'b1}; }
    cp_ebreakm:  coverpoint dcsr_ebreakm;
    cp_ebreaku:  coverpoint dcsr_ebreaku;
    cp_dcsr_nmip: coverpoint dcsr_nmip { bins zero = {1'b0}; illegal_bins one = {1'b1}; }
    cp_dcsr_prv: coverpoint dcsr_prv {
      bins         p[]    = {0, 3};
      illegal_bins rsvd   = {1, 2};
    }
    cp_dcsr_en:  coverpoint dcsr_en { bins hit = {1'b1}; }
    cp_trigger_en: coverpoint tmatch_control;

    // Single-stepping with interrupts enabled is the case where an interrupt
    // and the step trap compete (finding F-06). dcsr.stepie is hardwired to 0
    // (cs_registers.sv:703, KUDU-029), so the bin is unreachable
    // (AssertDcsrFixedFields).
    cp_step_with_ie: coverpoint (dcsr_step & dcsr_stepie) {
      option.weight = 0;
      bins         none = {1'b0};
      illegal_bins hit  = {1'b1};
    }
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

    // KUDU-025: dpc/dscratch writes in debug mode, in both pmodes.
    cp_dbg_csr_wr: coverpoint csr_addr_i
        iff (csr_exec_ok && !csr_cheri_i && csr_is_wr && debug_mode_i) {
      bins dpc       = {CSR_DPC};
      bins dscratch0 = {CSR_DSCRATCH0};
      bins dscratch1 = {CSR_DSCRATCH1};
    }
    cp_dbg_wr_pmode: coverpoint cheri_cov_en
        iff (csr_exec_ok && !csr_cheri_i && csr_is_wr && debug_mode_i) {
      option.weight = CHERIoTEn;
      bins rv32  = {1'b0};
      bins pmode = {1'b1};
    }
    // dpc/dscratch0/1 are illegal CSRs in CHERI mode (cs_registers.sv:512-522;
    // DEPCC/DSCRATCHC* replace them); AssertNoDbgCsrWrInPmode.
    x_dbg_csr_pmode: cross cp_dbg_csr_wr, cp_dbg_wr_pmode
        iff (csr_exec_ok && !csr_cheri_i && csr_is_wr && debug_mode_i) {
      option.weight = CHERIoTEn;
      illegal_bins pmode = binsof(cp_dbg_wr_pmode.pmode);
    }

    // KUDU-022/027: which kind of trap entry (M-mode trap, debug entry,
    // exception inside debug mode); the latter two must leave mcause/mepc.
    cp_save_kind: coverpoint {debug_mode_i, debug_csr_save_i} iff (csr_save_cause_i) {
      bins m_trap    = {2'b00};
      bins dbg_entry = {2'b01};
      bins exc_in_dm = {2'b10};
    }
    cp_dm_trap_m_write: coverpoint dm_trap_m_write iff (dm_trap) {
      bins          kept    = {1'b0};
      illegal_bins  written = {1'b1};
    }

    // KUDU-016: CSR write to MSHWM/MSHWMB followed closely by a store.
    cp_mshwm_wr_to_store: coverpoint mshwm_wr_age iff (csr_lsu_wr_req_i && cheri_cov_en) {
      option.weight = CHERIoTEn;
      // A CSR write needs lsu_req_info_q.is_csr, the LSU store update needs
      // !is_csr (load_store_unit.sv:542,686-687); AssertNoMshwmCsrWrWithLsuWr.
      illegal_bins same_cycle = {2'd0};
      bins one        = {2'd1};
      bins two        = {2'd2};
      bins three_plus = {2'd3};
    }

    // Tripwires for open bugs (weight 0; expected empty until the fix).
    // KUDU-019: minstret never increments (instr_ret_i tied off in kudu_top).
    cp_minstret_inc: coverpoint instr_ret_i {
      option.weight = 0;
      bins inc = {1'b1};
    }
    // KUDU-042: mstatush (0x310) is not implemented.
    cp_mstatush: coverpoint illegal_csr_insn_o
        iff (csr_access_i && (12'(csr_addr_i) == 12'h310)) {
      option.weight = 0;
      bins implemented = {1'b0};
    }
  endgroup

  cg_isa_csr u_cg_isa_csr = new();

  AssertNoMTrapCsrWriteInDebug: assert property (
    @(posedge clk_i) disable iff (!rst_ni) dm_trap |-> !dm_trap_m_write)
    else $error("FCOV: trap in/into debug mode wrote mcause/mepc (KUDU-022/027)");

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// kudu_sva_csr -- design properties of the CSR/SCR block (rtl/cs_registers.sv)
// checked as SVA (simulation and FPV):
//  - trap-control interface rules (one trap/return per cycle, debug entry and
//    dret only in the right debug state, no CSR write or cjalr mie update
//    racing a trap/return);
//  - trap entry, mret, dret and debug entry/exit state updates;
//  - WARL legality of every stored CSR/SCR (pc alignment, privilege fields,
//    dcsr fixed fields, mcountinhibit, cpuctrl, MSHWM/MSHWMB alignment, and
//    the tag/perm/otype rules of legalize_scr for MTCC/MEPCC/DEPCC and PCC);
//  - each architectural register changes only through its legal writers,
//    and an illegal CSR/SCR access has no effect;
//  - mcycle/minstret counting and mcountinhibit.
// Bound into cs_registers as u_fcov_sva_csr (kudu_fcov_bind.sv).
// ============================================================================
module kudu_sva_csr
  import super_pkg::*;
  import csr_pkg::*;
  import cheri_pkg::*;
  import kudu_cfg_pkg::*;
#(
  parameter bit          CHERIoTEn      = 1'b1,
  parameter kudu_cfg_t   CFG            = KuduCfg1,
  parameter bit          DbgTriggerEn   = 1'b1,
  parameter int unsigned BrkptNum       = 2
) (
  input logic                clk_i,
  input logic                rst_ni,
  input logic                cheri_pmode,

  // --- trap control (issuer) -------------------------------------------------
  input logic                csr_save_cause_i,
  input exc_info_t           csr_exc_info_i,
  input logic                csr_restore_mret_i,
  input logic                csr_restore_dret_i,
  input logic                csr_mtvec_init_i,
  input logic                ex1_cjalr_set_mie_i,
  input logic                ex1_cjalr_clr_mie_i,

  // --- debug -------------------------------------------------------------------
  input logic                debug_mode_i,
  input logic                debug_csr_save_i,
  input dbg_cause_e          debug_cause_i,

  // --- CSR access (LSU) ------------------------------------------------------
  input logic                csr_access_i,
  input logic                csr_cheri_i,
  input csr_num_e            csr_addr_i,
  input csr_op_e             csr_op_i,
  input logic                csr_op_en_i,
  input logic                illegal_csr_insn_o,
  input logic [31:0]         csr_wdata32,
  input logic                csr_lsu_wr_req_i,
  input logic                mshwm_en,
  input logic                mshwmb_en,
  input logic                debug_mode_entering_i,

  // --- interrupts --------------------------------------------------------------
  input irqs_t               irqs_o,

  // --- architectural state ---------------------------------------------------
  input priv_lvl_e           priv_lvl_q,
  input logic                mstatus_mie,
  input logic                mstatus_mpie,
  input priv_lvl_e           mstatus_mpp,
  input logic                mstatus_mprv,
  input logic                mstatus_tw,
  input irqs_t               mie_q,
  input logic [31:0]         mscratch_q,
  input logic [5:0]          mcause_q,
  input logic [31:0]         mtval_q,
  input logic [RegW-1:0]     mepc_q,
  input logic [RegW-1:0]     mtvec_q,
  input logic [RegW-1:0]     depc_q,
  input logic [RegW-1:0]     dscratch0_q,
  input logic [RegW-1:0]     dscratch1_q,
  input logic [RegW-1:0]     mtdc_q,
  input logic [RegW-1:0]     mscratchc_q,
  input logic [31:0]         dcsr_bits,
  input logic [3:0]          dcsr_xdebugver,
  input dbg_cause_e          dcsr_cause,
  input priv_lvl_e           dcsr_prv,
  input logic [18:0]         dcsr_fixed,
  input logic [31:0]         mshwm_q,
  input logic [31:0]         mshwmb_q,
  input logic [31:0]         mcountinhibit,
  input cpu_ctrl_t           cpuctrl_q,
  input pcc_cap_t            ex1_pcc_cap_q,
  input pcc_cap_t            ir_pcc_cap_q,

  // --- counters ------------------------------------------------------------------
  input logic [63:0]         mcycle,
  input logic [63:0]         minstret_raw,
  input logic [31:0]         mhpmcounter_we,
  input logic [31:0]         mhpmcounterh_we,
  input logic                instr_ret_i,

  // --- debug triggers --------------------------------------------------------
  input logic [BrkptNum-1:0] tmatch_control_o,
  input logic [31:0]         tmatch_value_o [0:BrkptNum-1]
);

`ifndef KUDU_FCOV_OFF

  // --------------------------------------------------------------------------
  // Helper decode (all combinational on the ports)
  // --------------------------------------------------------------------------
  // Trap kinds (cs_registers.sv:763-787).
  wire m_trap    = csr_save_cause_i && !debug_csr_save_i && !debug_mode_i;
  wire dbg_entry = csr_save_cause_i && debug_csr_save_i;
  wire dm_exc    = csr_save_cause_i && debug_mode_i && !debug_csr_save_i;
  wire trap_ctrl = csr_save_cause_i || csr_restore_mret_i || csr_restore_dret_i;
  wire cjalr_mie = ex1_cjalr_set_mie_i || ex1_cjalr_clr_mie_i;

  // A CSR (Zicsr) access that the block accepted as a legal write, and a legal
  // CHERI SCR write (CSpecialRW with rs1 != c0).
  wire csr_wr_legal = csr_op_en_i && !csr_cheri_i && !illegal_csr_insn_o &&
                      (csr_op_i inside {CSR_OP_WRITE, CSR_OP_SET, CSR_OP_CLEAR});
  wire scr_wr_legal = cheri_pmode && csr_op_en_i && csr_cheri_i && !illegal_csr_insn_o &&
                      (csr_op_i == CSR_OP_WRITE);

  function automatic bit csr_is(csr_num_e a, csr_num_e b);
    return 12'(a) == 12'(b);
  endfunction
  function automatic bit scr_is(csr_num_e a, logic [4:0] s);
    return 12'(a) == {7'h0, s};
  endfunction

  wire wr_mepc   = (csr_wr_legal && csr_is(csr_addr_i, CSR_MEPC)) ||
                   (scr_wr_legal && scr_is(csr_addr_i, CHERI_SCR_MEPCC));
  wire wr_mtvec  = (csr_wr_legal && csr_is(csr_addr_i, CSR_MTVEC)) ||
                   (scr_wr_legal && scr_is(csr_addr_i, CHERI_SCR_MTCC));
  wire wr_dpc    = debug_mode_i &&
                   ((csr_wr_legal && csr_is(csr_addr_i, CSR_DPC)) ||
                    (scr_wr_legal && scr_is(csr_addr_i, CHERI_SCR_DEPCC)));
  wire wr_dcsr   = debug_mode_i && csr_wr_legal && csr_is(csr_addr_i, CSR_DCSR);
  wire wr_mcause = csr_wr_legal && csr_is(csr_addr_i, CSR_MCAUSE);
  wire wr_mtval  = csr_wr_legal && csr_is(csr_addr_i, CSR_MTVAL);
  wire wr_mshwm  = cheri_pmode && csr_wr_legal && csr_is(csr_addr_i, CSR_MSHWM);
  wire wr_tdata  = debug_mode_i && csr_wr_legal &&
                   (csr_is(csr_addr_i, CSR_TDATA1) || csr_is(csr_addr_i, CSR_TDATA2));
  wire wr_scr_other = scr_wr_legal &&
                      (scr_is(csr_addr_i, CHERI_SCR_MTDC) || scr_is(csr_addr_i, CHERI_SCR_MSCRATCHC) ||
                       (debug_mode_i && (scr_is(csr_addr_i, CHERI_SCR_DSCRATCHC0) ||
                                         scr_is(csr_addr_i, CHERI_SCR_DSCRATCHC1))));
  wire wr_dscratch_csr = debug_mode_i && csr_wr_legal &&
                         (csr_is(csr_addr_i, CSR_DSCRATCH0) || csr_is(csr_addr_i, CSR_DSCRATCH1));

  // mcause values the core may raise (csr_pkg.sv:197-215, issuer.sv:1003-1012):
  // exceptions 0-8, 11, 28; interrupts 3, 7, 11 and fast 16-30.
  function automatic bit mcause_legal(logic [5:0] c);
    if (c[5]) return (c[4:0] inside {5'd3, 5'd7, 5'd11, [5'd16:5'd30]});
    else      return (c[4:0] inside {[5'd0:5'd8], 5'd11, 5'd28});
  endfunction

  // The mie/mip bit that an interrupt mcause code refers to.
  function automatic bit irq_of_cause(irqs_t q, logic [4:0] code);
    if (code == 5'd3)                        return q.irq_software;
    else if (code == 5'd7)                   return q.irq_timer;
    else if (code == 5'd11)                  return q.irq_external;
    else if (code >= 5'd16 && code <= 5'd30) return q.irq_fast[code[3:0]];  // code - 16
    else                                     return 1'b0;
  endfunction

  // All stored state that an illegal CSR access must leave alone.
  wire [31:0] trig_ctrl_vec = 32'(tmatch_control_o);
  logic [32*BrkptNum-1:0] trig_val_vec;
  always_comb begin
    for (int unsigned i = 0; i < BrkptNum; i++) trig_val_vec[32*i +: 32] = tmatch_value_o[i];
  end

  // ==========================================================================
  // A. Trap-control interface
  // ==========================================================================
  // cs_registers.sv:761 unique case (1'b1): trap entry, mret and dret are
  // mutually exclusive requests from the issuer.
  AssertTrapCtrlOneHot0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    $onehot0({csr_save_cause_i, csr_restore_mret_i, csr_restore_dret_i}))
    else $error("SVA_CSR: more than one of save_cause/mret/dret");

  // cs_registers.sv:309,844: illegal_csr_insn_o is qualified by csr_access_i,
  // so a write strobe without csr_access_i would bypass the legality check.
  AssertOpEnImpliesAccess: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_op_en_i |-> csr_access_i)
    else $error("SVA_CSR: csr_op_en_i without csr_access_i");

  // cs_registers.sv:768-772,1744-1749: dpc is written on debug_csr_save_i alone
  // but dcsr only together with csr_save_cause_i; debug entry must also not
  // happen in debug mode (ebreak in D-mode must not update dpc/dcsr).
  AssertDbgSaveIsEntry: assert property (@(posedge clk_i) disable iff (!rst_ni)
    debug_csr_save_i |-> csr_save_cause_i && !debug_mode_i)
    else $error("SVA_CSR: debug_csr_save without save_cause or inside debug mode");

  // cs_registers.sv:789-790: dret restores priv from dcsr.prv; it is only
  // legal in debug mode (debug spec 4.8).
  AssertDretOnlyInDebug: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_dret_i |-> debug_mode_i)
    else $error("SVA_CSR: dret outside debug mode");

  // cs_registers.sv:761 vs 1671/1741: the trap path wins over a CSR write for
  // mstatus/mcause but loses for mepc/dpc, so a CSR/SCR write retiring in the
  // same cycle as a trap/return would leave an inconsistent state.
  AssertNoCsrWriteAtTrapCtrl: assert property (@(posedge clk_i) disable iff (!rst_ni)
    trap_ctrl |-> !(csr_wr_legal || scr_wr_legal))
    else $error("SVA_CSR: CSR/SCR write in the cycle of a trap/mret/dret");

  // cs_registers.sv:875-879: a cjalr sentry mie set/clear overrides the
  // mstatus.mie value of a concurrent trap entry or mret.
  AssertNoCjalrMieAtTrapCtrl: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cjalr_mie |-> !(csr_save_cause_i || csr_restore_mret_i))
    else $error("SVA_CSR: cjalr mie update in the cycle of a trap/mret");

  // ==========================================================================
  // B. Trap entry / return / debug entry
  // ==========================================================================
  // cs_registers.sv:763-787,875-879: M-mode trap entry: priv <- M, mie <- 0,
  // mpp <- previous priv, mpie <- previous mie (or the in-flight cjalr's mie
  // for LSU faults in CHERIoT mode).
  AssertMTrapEntryStatus: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |=> (priv_lvl_q == PRIV_LVL_M) && !mstatus_mie &&
               (mstatus_mpp == $past(priv_lvl_q)) &&
               (mstatus_mpie == $past((cheri_pmode && csr_exc_info_i.has_pcc) ?
                                      csr_exc_info_i.mie : mstatus_mie)))
    else $error("SVA_CSR: wrong mstatus/priv after trap entry");

  // cs_registers.sv:774-787,1670-1680: trap entry records mcause, mtval and
  // the faulting pc in mepc (address part), whatever else happens that cycle.
  AssertMTrapEntryCauseEpc: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |=> (mcause_q == $past(csr_exc_info_i.mcause)) &&
               (mtval_q == $past(csr_exc_info_i.mtval)) &&
               (mepc_q[31:0] == $past(csr_exc_info_i.pc[31:0])))
    else $error("SVA_CSR: wrong mcause/mtval/mepc after trap entry");

  // csr_pkg.sv:197-215, issuer.sv:960-1030: every trap cause is one the core
  // defines (mcause is WLRL; hardware must only write legal values).
  AssertTrapCauseLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    m_trap |-> mcause_legal(csr_exc_info_i.mcause))
    else $error("SVA_CSR: trap with undefined mcause 0x%02x", csr_exc_info_i.mcause);

`ifdef KUDU_FORMAL_RTL
  // Temporarily formal-only: simulation exercises waived IRQ withdrawal.
  // Privileged spec 3.1.6.1/3.1.9: an interrupt is taken only if it is pending
  // and enabled in mie, and M-mode interrupts are globally enabled (mstatus.mie
  // or a lower privilege) (cs_registers.sv:856, issuer.sv:1003-1015).
  AssertIrqTrapEnabled: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (m_trap && csr_exc_info_i.mcause[5]) |->
      irq_of_cause(irqs_o, csr_exc_info_i.mcause[4:0]) &&
      (mstatus_mie || (priv_lvl_q == PRIV_LVL_U)))
    else $error("SVA_CSR: interrupt %0d taken while not pending/enabled",
                csr_exc_info_i.mcause[4:0]);
`endif

`ifndef DII_SIM
  // DII forces MPP to M for Sail's machine-only configuration.
  // cs_registers.sv:793-808: mret: priv <- mpp, mie <- mpie, mpie <- 1,
  // mpp <- U (least privilege), mprv cleared when returning below M.
  AssertMretRestore: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_mret_i |=> (priv_lvl_q == $past(mstatus_mpp)) &&
                           (mstatus_mie == $past(mstatus_mpie)) && mstatus_mpie &&
                           (mstatus_mpp == PRIV_LVL_U) &&
                           (($past(mstatus_mpp) != PRIV_LVL_M) -> !mstatus_mprv))
    else $error("SVA_CSR: wrong mstatus/priv after mret");
`endif

  // cs_registers.sv:789-790: dret returns to the privilege saved in dcsr.prv.
  AssertDretPriv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_restore_dret_i |=> (priv_lvl_q == $past(dcsr_prv)))
    else $error("SVA_CSR: priv after dret differs from dcsr.prv");

  // cs_registers.sv:441-452: privilege changes only through trap entry, mret
  // or dret (no CSR write can change the current privilege).
  AssertPrivChangeOnlyByTrapCtrl: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !trap_ctrl |=> $stable(priv_lvl_q))
    else $error("SVA_CSR: privilege changed without trap/mret/dret");

`ifdef KUDU_FORMAL_RTL
  // Temporarily formal-only: simulation exercises waived debug withdrawal.
  // issuer.sv:963-976: a debug entry has a defined cause (debug spec 4.9.1).
  AssertDbgEntryCause: assert property (@(posedge clk_i) disable iff (!rst_ni)
    dbg_entry |-> (debug_cause_i inside {DBG_CAUSE_EBREAK, DBG_CAUSE_TRIGGER,
                                         DBG_CAUSE_HALTREQ, DBG_CAUSE_STEP}))
    else $error("SVA_CSR: debug entry with cause %0d", debug_cause_i);
`endif

  // cs_registers.sv:768-772,1744-1749: debug entry saves cause, prv and the pc
  // in dcsr/dpc, switches to M, and leaves mstatus/mcause/mtval/mepc alone.
  AssertDbgEntryUpdate: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (dbg_entry && !cjalr_mie) |=>
      (priv_lvl_q == PRIV_LVL_M) &&
      (dcsr_cause == $past(debug_cause_i)) && (dcsr_prv == $past(priv_lvl_q)) &&
      (depc_q[31:0] == $past(csr_exc_info_i.pc[31:0])) &&
      $stable({mstatus_mie, mstatus_mpie, mstatus_mpp, mstatus_mprv, mstatus_tw}) &&
      $stable(mcause_q) && $stable(mtval_q) && $stable(mepc_q))
    else $error("SVA_CSR: wrong state update on debug entry");

  // cs_registers.sv:765-776: "exceptions [in debug mode] do not update any
  // registers ... cause, epc, tval, dpc and mstatus" (debug spec 4.1). mcause/
  // mepc are covered by AssertNoMTrapCsrWriteInDebug.
  AssertDmExcNoUpdate: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (dm_exc && !cjalr_mie) |=>
      $stable({mstatus_mie, mstatus_mpie, mstatus_mpp, mstatus_mprv, mstatus_tw}) &&
      $stable(mtval_q) && $stable(depc_q) && $stable(dcsr_bits))
    else $error("SVA_CSR: exception in debug mode updated mstatus/mtval/dpc/dcsr");

  // ==========================================================================
  // C. WARL legality of the stored state (both pmodes)
  // ==========================================================================
  // cs_registers.sv:1073 (legalize_scr), 1672-1679: mepc/MEPCC is 2-byte
  // aligned (C extension), whatever the writer (CSR, SCR, trap).
  AssertMepcAlign: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !mepc_q[0])
    else $error("SVA_CSR: odd mepc 0x%08x (KUDU-075)", mepc_q[31:0]);

  // cs_registers.sv:1652,1660-1661,1741-1749: dpc/DEPCC is 2-byte aligned.
  AssertDepcAlign: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !depc_q[0])
    else $error("SVA_CSR: odd dpc 0x%08x (KUDU-077)", depc_q[31:0]);

  // cs_registers.sv:1706,1709-1717, cheri_pkg.sv:1073: mtvec/MTCC is in direct
  // mode and 4-byte aligned (vectored mode not implemented).
  AssertMtvecAlign: assert property (@(posedge clk_i) disable iff (!rst_ni)
    mtvec_q[1:0] == 2'b00)
    else $error("SVA_CSR: mtvec low bits 0x%0x", mtvec_q[1:0]);

  // cs_registers.sv:766,790,798: only M and U are implemented.
  AssertPrivLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    priv_lvl_q inside {PRIV_LVL_M, PRIV_LVL_U})
    else $error("SVA_CSR: illegal privilege %0d", priv_lvl_q);

  // cs_registers.sv:673-676,783,808: mstatus.mpp is WARL {M, U}.
  AssertMppLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    mstatus_mpp inside {PRIV_LVL_M, PRIV_LVL_U})
    else $error("SVA_CSR: illegal mstatus.mpp %0d", mstatus_mpp);

  // cs_registers.sv:695-697,771: dcsr.prv is WARL {M, U}.
  AssertDcsrPrvLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    dcsr_prv inside {PRIV_LVL_M, PRIV_LVL_U})
    else $error("SVA_CSR: illegal dcsr.prv %0d", dcsr_prv);

  // cs_registers.sv:691-715,772: dcsr.xdebugver = 4, the zero/unsupported
  // fields (stepie, nmip, mprven, stopcount, stoptime) stay 0, and cause is a
  // defined value.
  AssertDcsrFixedFields: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (dcsr_xdebugver == XDEBUGVER_STD) && (dcsr_fixed == '0) && (dcsr_cause inside {DBG_CAUSE_NONE, DBG_CAUSE_EBREAK, DBG_CAUSE_TRIGGER,
                                    DBG_CAUSE_HALTREQ, DBG_CAUSE_STEP}))
    else $error("SVA_CSR: dcsr fixed fields corrupted 0x%08x", dcsr_bits);

  // cs_registers.sv:1233-1234: mcountinhibit bit 1 (time) is hardwired to 0.
  AssertMcountinhibitBit1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !mcountinhibit[1])
    else $error("SVA_CSR: mcountinhibit[1] set");

  // cs_registers.sv:1574-1579: cpuctrl features that the configuration does not
  // implement read as 0 (WARL).
  AssertCpuctrlLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (!cpuctrl_q.dcache_en || CFG.DCacheEn) && (!cpuctrl_q.alt_en || CFG.AltEnable) &&
    (!cpuctrl_q.ra_pdt_en || CFG.PredictRA))
    else $error("SVA_CSR: cpuctrl enables an unimplemented feature");

  // cs_registers.sv:983,1009: MSHWM/MSHWMB are 16-byte aligned.
  AssertMshwmAlign: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (mshwm_q[3:0] == 4'h0) && (mshwmb_q[3:0] == 4'h0))
    else $error("SVA_CSR: unaligned MSHWM 0x%08x / MSHWMB 0x%08x", mshwm_q, mshwmb_q);

  // kudu_top.sv:656: debug_mode_entering_i is tied off (cp_entering.hit).
  AssertDbgEnteringTiedOff: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !debug_mode_entering_i)
    else $error("SVA_CSR: debug_mode_entering_i asserted");

  // load_store_unit.sv:542,686-687: an MSHWM/MSHWMB CSR write and an LSU store
  // MSHWM update never share a cycle (cp_mshwm_wr_to_store.same_cycle).
  AssertNoMshwmCsrWrWithLsuWr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_lsu_wr_req_i && cheri_pmode) |-> !(mshwm_en || mshwmb_en))
    else $error("SVA_CSR: MSHWM CSR write in the cycle of an LSU MSHWM update");

  // cs_registers.sv:512-522: in CHERI mode dpc/dscratch0/1 are illegal CSRs,
  // so no legal debug-mode CSR write reaches them (x_dbg_csr_pmode.pmode).
  AssertNoDbgCsrWrInPmode: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_wr_legal && debug_mode_i && cheri_pmode) |->
      !(csr_is(csr_addr_i, CSR_DPC) || csr_is(csr_addr_i, CSR_DSCRATCH0) ||
        csr_is(csr_addr_i, CSR_DSCRATCH1)))
    else $error("SVA_CSR: legal CSR write to dpc/dscratch in CHERI mode (0x%03x)", csr_addr_i);

  // cs_registers.sv:981-986: the store-driven MSHWM update only lowers MSHWM,
  // and never below MSHWMB (CHERIoT spec, stack high-water mark).
  AssertMshwmHwLowers: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !wr_mshwm |=> $stable(mshwm_q) ||
                  ((mshwm_q[31:4] < $past(mshwm_q[31:4])) &&
                   (mshwm_q[31:4] >= $past(mshwmb_q[31:4]))))
    else $error("SVA_CSR: MSHWM hardware update out of [MSHWMB, MSHWM)");

  // cs_registers.sv:981-986 (KUDU-016): a csrw mshwm must take effect; a
  // store-driven update in the same cycle would silently drop it.
  AssertMshwmCsrWriteWins: assert property (@(posedge clk_i) disable iff (!rst_ni)
    wr_mshwm |=> (mshwm_q[31:4] == $past(csr_wdata32[31:4])))
    else $error("SVA_CSR: csrw mshwm lost to a concurrent store update");

  // ==========================================================================
  // D. Registers change only through their legal writers
  // ==========================================================================
  // cs_registers.sv:1670-1683: mepc/MEPCC: M-mode trap entry or a legal write.
  AssertMepcWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(m_trap || wr_mepc) |=> $stable(mepc_q))
    else $error("SVA_CSR: mepc changed without trap or legal write");

  // cs_registers.sv:1740-1753: dpc/DEPCC: debug entry or a write in debug mode.
  AssertDpcWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(dbg_entry || wr_dpc) |=> $stable(depc_q))
    else $error("SVA_CSR: dpc changed without debug entry or debug-mode write");

  // cs_registers.sv:1708-1720: mtvec/MTCC: boot init or a legal write.
  AssertMtvecWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(csr_mtvec_init_i || wr_mtvec) |=> $stable(mtvec_q))
    else $error("SVA_CSR: mtvec changed without init or legal write");

  // cs_registers.sv:690-716,768-773: dcsr: debug entry or a debug-mode write.
  AssertDcsrWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(dbg_entry || wr_dcsr) |=> $stable(dcsr_bits))
    else $error("SVA_CSR: dcsr changed without debug entry or debug-mode write");

  // cs_registers.sv:654-660,774-787: mcause/mtval: trap entry or legal write.
  AssertMcauseMtvalWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(m_trap || wr_mcause || wr_mtval) |=> $stable(mcause_q) && $stable(mtval_q))
    else $error("SVA_CSR: mcause/mtval changed without trap or legal write");

  // cs_registers.sv:1450-1458 (tdata1.dmode = 1): triggers are writable only
  // from debug mode.
  if (DbgTriggerEn) begin : g_trig
    AssertTriggerWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
      !wr_tdata |=> $stable(trig_ctrl_vec) && $stable(trig_val_vec))
      else $error("SVA_CSR: trigger changed outside a debug-mode tdata write");
  end

  // cs_registers.sv:309,644-760,1616-1636,1740-1772,1893-1909: an illegal CSR
  // or SCR access has no architectural side effect (the trap is taken later).
  AssertIllegalCsrNoEffect: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (csr_op_en_i && illegal_csr_insn_o && !trap_ctrl && !csr_mtvec_init_i &&
     !cjalr_mie && !csr_lsu_wr_req_i) |=>
      $stable({mstatus_mie, mstatus_mpie, mstatus_mpp, mstatus_mprv, mstatus_tw}) &&
      $stable(priv_lvl_q) && $stable(mie_q) && $stable(mscratch_q) &&
      $stable(mcause_q) && $stable(mtval_q) && $stable(mepc_q) && $stable(mtvec_q) &&
      $stable(depc_q) && $stable(dscratch0_q) && $stable(dscratch1_q) &&
      $stable(dcsr_bits) && $stable(mtdc_q) && $stable(mscratchc_q) &&
      $stable(mshwm_q) && $stable(mshwmb_q) && $stable(mcountinhibit) &&
      $stable(cpuctrl_q) && $stable(trig_ctrl_vec) && $stable(trig_val_vec))
    else $error("SVA_CSR: illegal CSR access 0x%03x changed state", csr_addr_i);

  // cs_registers.sv:1756-1773,1893-1909: MTDC/MSCRATCHC/DSCRATCH* change only
  // by their SCR (or, for dscratch, debug-mode CSR) write.
  AssertScratchWriters: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(wr_scr_other || wr_dscratch_csr) |=>
      $stable(mtdc_q) && $stable(mscratchc_q) && $stable(dscratch0_q) && $stable(dscratch1_q))
    else $error("SVA_CSR: scratch/MTDC changed without its write");

  // ==========================================================================
  // E. Counters
  // ==========================================================================
`ifdef KUDU_FORMAL_RTL
  // Temporarily formal-only while simulation counter failures are investigated.
`ifndef DII_SIM
  // cs_registers.sv:1253,1321-1333, ibex_counter.sv: mcycle counts every cycle
  // unless inhibited, and holds when inhibited (no CSR write).
  AssertMcycleCount: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(mhpmcounter_we[0] || mhpmcounterh_we[0]) |=>
      (mcycle == $past(mcycle) + 64'(!$past(mcountinhibit[0]))))
    else $error("SVA_CSR: mcycle did not count correctly");
`endif
`endif

  // cs_registers.sv:1255,1337-1349: minstret counts retired instructions
  // unless inhibited (no CSR write).
  AssertMinstretCount: assert property (@(posedge clk_i) disable iff (!rst_ni)
    !(mhpmcounter_we[2] || mhpmcounterh_we[2]) |=>
      (minstret_raw == $past(minstret_raw) + 64'($past(instr_ret_i && !mcountinhibit[2]))))
    else $error("SVA_CSR: minstret did not count correctly");

  // ==========================================================================
  // F. CHERIoT capability legality (CHERIoTEn builds)
  // ==========================================================================
  if (CHERIoTEn) begin : g_cheri
    reg_cap_t mtcc_cap, mepcc_cap, depcc_cap;
    logic [PERMS_W-1:0] mtcc_perms, mepcc_perms, depcc_perms;

    assign mtcc_cap    = reg_cap_t'(mtvec_q);
    assign mepcc_cap   = reg_cap_t'(mepc_q);
    assign depcc_cap   = reg_cap_t'(depc_q);
    assign mtcc_perms  = expand_perms(mtcc_cap.cperms);
    assign mepcc_perms = expand_perms(mepcc_cap.cperms);
    assign depcc_perms = expand_perms(depcc_cap.cperms);

    // cheri_pkg.sv:1068-1082 (legalize_scr), cs_registers.sv:1660-1662,1709:
    // a tagged MTCC is executable and unsealed.
    AssertMtccTagLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
      mtcc_cap.valid |-> mtcc_perms[PERM_EX] && (mtcc_cap.otype == OTYPE_UNSEALED))
      else $error("SVA_CSR: tagged MTCC not executable/unsealed");

    // cheri_pkg.sv:1078, cs_registers.sv:1670-1680: a tagged MEPCC is
    // executable and unsealed (SCR write legalized; trap saves PCC).
    AssertMepccTagLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
      mepcc_cap.valid |-> mepcc_perms[PERM_EX] && (mepcc_cap.otype == OTYPE_UNSEALED))
      else $error("SVA_CSR: tagged MEPCC not executable/unsealed");

    // cheri_pkg.sv:1078, cs_registers.sv:1740-1753: same for DEPCC.
    AssertDepccTagLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
      depcc_cap.valid |-> depcc_perms[PERM_EX] && (depcc_cap.otype == OTYPE_UNSEALED))
      else $error("SVA_CSR: tagged DEPCC not executable/unsealed");

    // cs_registers.sv:1846-1890: PCC (both copies) carries expanded perms that
    // match its compressed cperms.
    AssertPccPermsConsistent: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (ex1_pcc_cap_q.perms == expand_perms(ex1_pcc_cap_q.cperms)) &&
      (ir_pcc_cap_q.perms == expand_perms(ir_pcc_cap_q.cperms)))
      else $error("SVA_CSR: PCC perms inconsistent with cperms");

    // cs_registers.sv:1872-1874, branch_unit.sv:99-128,171, mult_pipeline.sv:247:
    // outside debug mode a tagged PCC is executable and unsealed (cjalr target
    // checks; MTCC/MEPCC legalized). In debug mode the cjalr checks are off by
    // design and dret reloads PCC from DEPCC.
    AssertPccTagLegal: assert property (@(posedge clk_i) disable iff (!rst_ni)
      (!debug_mode_i && ex1_pcc_cap_q.valid) |->
        ex1_pcc_cap_q.perms[PERM_EX] && (ex1_pcc_cap_q.otype == OTYPE_UNSEALED))
      else $error("SVA_CSR: tagged PCC not executable/unsealed outside debug mode");
  end

`endif  // KUDU_FCOV_OFF

endmodule

// ============================================================================
// FV helper lemmas: formal only, compiled only with +define+KUDU_FV_HELPERS.
//
// Auxiliary invariants that JasperGold proves and then assumes (run_fcov_clean
// in fv/fv_kudu_fcov.tcl) so that the harder assertions above become
// inductive. No covergroups; simulation never defines KUDU_FV_HELPERS. They
// are bound only in the KUDU_FV_HELPERS block at the end of kudu_fcov_bind.sv,
// which sits inside its KUDU_FCOV_OFF and CHERIoT guards. They read the fcov
// instances bound there and were proven only with CHERIoTEn=1, so the
// definitions carry the same guards: an unbound copy would become an extra
// top-level module with unresolvable kudu_top.* references.
// ============================================================================
`ifdef KUDU_FV_HELPERS
`ifdef CHERIoT
`ifndef KUDU_FCOV_OFF

// kudu_fvh_csr (was fv/fv_help_csr.sv plus the Tcl asserts of fv/h_final.tcl,
// bound into kudu_top as u_fvh_csr). Supports the csr-area kudu_sva_csr
// targets: AssertDbgEntryUpdate, AssertDmExcNoUpdate, AssertIrqTrapEnabled,
// AssertMTrapEntryCauseEpc, AssertNoCsrWriteAtTrapCtrl and the g_cheri
// capability-legality asserts.
//
// FV helper lemmas for the CHERIoT capability-legality targets of kudu_sva_csr
// (AssertMepccTagLegal / AssertDepccTagLegal / AssertPccTagLegal).
module kudu_fvh_csr
  import super_pkg::*;
  import cheri_pkg::*;
(
  input logic clk_i,
  input logic rst_ni
);
  function automatic bit rcap_ok(logic [RegW-1:0] x);
    reg_cap_t c;
    logic [PERMS_W-1:0] p;
    c = reg_cap_t'(x);
    p = expand_perms(c.cperms);
    return !c.valid || (p[PERM_EX] && (c.otype == OTYPE_UNSEALED));
  endfunction
  function automatic bit pcap_ok(pcc_cap_t c);
    return !c.valid || (c.perms[PERM_EX] && (c.otype == OTYPE_UNSEALED));
  endfunction

  wire       dbg      = kudu_top.issuer_i.debug_mode_q;
  pcc_cap_t  pcc;
  assign pcc = kudu_top.cs_registers_i.ex1_pcc_cap_q;
  wire [RegW-1:0] mepc = kudu_top.cs_registers_i.mepc_q;
  wire [RegW-1:0] depc = kudu_top.cs_registers_i.depc_q;

  // committer error record
  wire            cmt_err  = kudu_top.committer_i.cmt_err_q;
  exc_info_t      cmt_info;
  assign cmt_info = kudu_top.committer_i.cmt_err_info_q;

  // LSU stages
  wire            out_q    = kudu_top.ls_pipeline_i.load_store_unit_i.outstanding_resp_q;
  lsu_req_info_t  lsu_q, dly_q, hold_q, dec;
  assign lsu_q  = kudu_top.ls_pipeline_i.load_store_unit_i.lsu_req_info_q;
  assign dly_q  = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_q;
  assign hold_q = kudu_top.ls_pipeline_i.lsu_if_i.req_hold_q;
  assign dec    = kudu_top.ls_pipeline_i.lsu_req_dec;
  wire            dly_v    = kudu_top.ls_pipeline_i.lsu_if_i.req_dly_valid;
  wire [2:0]      lsif_st  = kudu_top.ls_pipeline_i.lsu_if_i.lsif_fsm_q;
  wire            us_v     = kudu_top.ls_pipeline_i.lsu_if_req_valid;
  // wb fifo (wt_fifo Depth 4)
  wire [2:0]      wb_wr    = kudu_top.ls_pipeline_i.wb_fifo_i.wr_ptr_q;
  wire [2:0]      wb_rd    = kudu_top.ls_pipeline_i.wb_fifo_i.rd_ptr_q;
  wire [2:0]      wb_cnt   = wb_wr - wb_rd;
  pl_out_t        wbm [4];
  for (genvar k = 0; k < 4; k++) begin : g_wbm
    assign wbm[k] = pl_out_t'(kudu_top.ls_pipeline_i.wb_fifo_i.fifo_mem[k]);
  end
  // cmplx unit
  wire [1:0]      cx_st    = kudu_top.comlx_unit_i.cmplx_fsm_cs;
  wire [RegW-1:0] cx_pcc   = kudu_top.comlx_unit_i.pcc_rcap_q;

  wire spec  = kudu_top.issuer_i.ctrl_fsm_cs[8];

  // the LS pipeline, committer error record and cmplx unit are empty in ISSUE_SPECIAL
  AssertHelpSpecDrained: assert property (@(posedge clk_i) disable iff (!rst_ni)
    spec |-> !dly_v && (lsif_st == 3'h0) && !out_q && (wb_cnt == 3'h0) && !cmt_err && (cx_st == 2'h0));
  // ===========================================================================
  // LS-pipeline occupancy vs scoreboard (for the trap/CSR-write targets)
  // ===========================================================================
  wire [3:0] sbd_wp = kudu_top.sbd_fifo_i.wr_ptr_q;
  wire [3:0] sbd_rp = kudu_top.sbd_fifo_i.rd_ptr_q;
  wire [3:0] sbd_n  = sbd_wp - sbd_rp;
  logic [3:0] sbd_ls_n;
  always_comb begin
    sbd_fifo_t e;
    logic [2:0] idx;
    sbd_ls_n = '0;
    for (int unsigned k = 0; k < 8; k++) begin
      idx = sbd_rp[2:0] + k[2:0];
      e   = sbd_fifo_t'(kudu_top.sbd_fifo_i.fifo_mem[idx]);
      if ((k < 32'(sbd_n)) && e.pl[3]) sbd_ls_n = sbd_ls_n + 4'h1;
    end
  end
  wire [2:0] ls_fsm  = kudu_top.ls_pipeline_i.load_store_unit_i.ls_fsm_cs;
  // LS instructions held in lsu_if (DLY1: dly reg; DLY0_WGNT: hold; DLY1_WGNT: hold + dly)
  wire [3:0] lsif_n  = (lsif_st == 3'h2) ? {3'h0, dly_v} :
                       (lsif_st == 3'h1) ? 4'h1 :
                       (lsif_st == 3'h3) ? (4'h1 + {3'h0, dly_v}) : 4'h0;
  // accepted by the LSU and no longer held by lsu_if
  wire [3:0] lsu_n   = {3'h0, out_q && (ls_fsm == 3'h0)};
  wire       lsu_req = kudu_top.ls_pipeline_i.lsu_req;
  wire       csr_go_q = kudu_top.ls_pipeline_i.load_store_unit_i.csr_go_q;
  wire       cjalr_mie = kudu_top.cs_registers_i.ex1_cjalr_set_mie_i | kudu_top.cs_registers_i.ex1_cjalr_clr_mie_i;
  wire [15:0] fsm = kudu_top.issuer_i.ctrl_fsm_cs;

  // every LS instruction in flight (lsu_if, LSU, wb fifo) has its own LS scoreboard entry
  AssertHelpLsCount: assert property (@(posedge clk_i) disable iff (!rst_ni)
    sbd_ls_n >= lsif_n + lsu_n + {1'b0, wb_cnt});
  // no new LS-pipeline request while the issuer waits for the scoreboard to drain
  AssertHelpLsReqNotWait: assert property (@(posedge clk_i) disable iff (!rst_ni)
    us_v |-> !fsm[6]);
  // the LS pipeline is idle when WAIT_CMT0 sees an empty scoreboard
  AssertHelpWaitLsIdle: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (fsm[6] && !kudu_top.sbd_fifo_i.rd_valid_o[0]) |-> !lsu_req && !out_q && (wb_cnt == 3'h0));
  // a CSR access is outstanding in the cycle after csr_go
  AssertHelpCsrGoQOut: assert property (@(posedge clk_i) disable iff (!rst_ni)
    csr_go_q |-> out_q);
  // cjalr mie updates only happen at issue (DECODE, or ISSUE_SPECIAL for a single step)
  AssertHelpCjalrMieState: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cjalr_mie |-> fsm[2] || fsm[8]);
  // ===========================================================================
  // Combined capability-legality invariant (inductive as one conjunction)
  // ===========================================================================
  pcc_cap_t cj_pcap;
  assign cj_pcap = kudu_top.ex1_cjalr_pcap;
  wire      cj_set  = kudu_top.ex1_cjalr_pcc_set;
  // a cjalr that updates PCC outside debug mode installs an executable PCC
  AssertHelpCjalrEx: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (cj_set && !dbg && cj_pcap.valid) |-> cj_pcap.perms[PERM_EX]);

  logic wb_ok;
  always_comb begin
    wb_ok = 1'b1;
    for (int k = 0; k < 4; k++)
      if (3'(2'(k) - wb_rd[1:0]) < wb_cnt) wb_ok &= rcap_ok(wbm[k].pc);
  end
  AssertHelpCapBig: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (dbg || pcap_ok(pcc)) && rcap_ok(mepc) && rcap_ok(depc) &&
    (dbg || ((!cmt_err || rcap_ok(cmt_info.pc)) &&
             (!out_q || rcap_ok(lsu_q.pc)) &&
             (!dly_v || rcap_ok(dly_q.pc)) &&
             (!(lsif_st inside {3'h1, 3'h3}) || rcap_ok(hold_q.pc)) &&
             wb_ok &&
             ((cx_st == 2'h0) || rcap_ok(cx_pcc)))));
  // the cjalr executed by the mult pipeline is the one the branch unit found error-free
  AssertHelpCjalrNoErr: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (cj_set && !dbg) |->
      ((kudu_top.multpl_sel_ira ? kudu_top.branch_unit_i.cjalr_err_a :
                                  kudu_top.branch_unit_i.cjalr_err_b) == 3'h0));
  // --- decomposition of AssertHelpCjalrNoErr
  // WAIT_CMT0 -> ISSUE_SPECIAL transition condition
  wire cmt0_exit = fsm[6] && !kudu_top.issuer_i.sbdfifo_rd_valid_i[0] &&
                   !kudu_top.issuer_i.trvk_outstanding_i && !kudu_top.issuer_i.cmt_err_i;
  // a valid IR slot that decodes as jalr is routed as PL_JALR
  AssertHelpCjDec0: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.issuer_i.ir_valid_i[0] && kudu_top.issuer_i.ir0_dec.is_jalr) |->
      (kudu_top.issuer_i.ir0_dec.pl_type == PL_JALR));
  AssertHelpCjDec1: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.issuer_i.ir_valid_i[1] && kudu_top.issuer_i.ir1_dec.is_jalr) |->
      (kudu_top.issuer_i.ir1_dec.pl_type == PL_JALR));
  // no ir0 hazard once WAIT_CMT0 can exit, nor in ISSUE_SPECIAL
  AssertHelpCmt0NoHz: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt0_exit |-> !kudu_top.issuer_i.ir_hazard[0]);
  AssertHelpSpecNoHz: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fsm[8] |-> !kudu_top.issuer_i.ir_hazard[0]);
  // a single-stepped ir0 (ISSUE_SPECIAL/STEP) has no cjalr error
  AssertHelpCjStep: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (fsm[8] && (kudu_top.issuer_i.special_case_q == STEP) && !dbg) |->
      (kudu_top.issuer_i.ir0_cjalr_err_i == 3'h0));
  AssertHelpCmt0Wrsv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt0_exit |-> (kudu_top.issuer_i.reg_wrsv_q == '0));
  AssertHelpCmt0Trsv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt0_exit |-> (kudu_top.issuer_i.reg_cheri_trsv_q == '0));
  AssertHelpCmt0Raw: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt0_exit |-> !kudu_top.issuer_i.ir_raw_hazard[0]);
  AssertHelpCmt0Waw: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt0_exit |-> !kudu_top.issuer_i.ir_waw_hazard[0]);
  AssertHelpCmt0Chz: assert property (@(posedge clk_i) disable iff (!rst_ni)
    cmt0_exit |-> !kudu_top.issuer_i.ir_cheri_hazard[0]);
  AssertHelpSpecWrsv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fsm[8] |-> (kudu_top.issuer_i.reg_wrsv_q == '0));
  AssertHelpSpecTrsv: assert property (@(posedge clk_i) disable iff (!rst_ni)
    fsm[8] |-> (kudu_top.issuer_i.reg_cheri_trsv_q == '0));
  // for a single step, the ir0 cjalr check result does not change between the WAIT_CMT0 exit and ISSUE_SPECIAL
  AssertHelpSpecErrStable: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (fsm[8] && (kudu_top.issuer_i.special_case_q == STEP)) |-> $stable(kudu_top.issuer_i.ir0_cjalr_err_i));

  // ===========================================================================
  // Former Tcl asserts (fv/h_final.tcl, then named relative to kudu_top).
  // ctrl_fsm_cs is one-hot, bit index = ctrl_fsm_e: 2 DECODE, 3 CMT_FLUSH,
  // 6 WAIT_CMT0, 8 ISSUE_SPECIAL.
  // ===========================================================================
  // trap/mret/dret are only signalled in CMT_FLUSH or ISSUE_SPECIAL
  AssertHelpTrapState: assert property (@(posedge clk_i) disable iff (!rst_ni)
    (kudu_top.cs_registers_i.csr_save_cause_i | kudu_top.cs_registers_i.csr_restore_mret_i |
     kudu_top.cs_registers_i.csr_restore_dret_i) |->
      (kudu_top.issuer_i.ctrl_fsm_cs[3] | kudu_top.issuer_i.ctrl_fsm_cs[8]));
  // no CSR operation retires in CMT_FLUSH (an LS error blocks later csr_go until the flush)
  AssertHelpFlushNoOp: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[3] |-> !kudu_top.cs_registers_i.csr_op_en_i);
  // cs_registers sees the issuer's debug_mode_q
  AssertHelpDbgModeEq: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.cs_registers_i.debug_mode_i == kudu_top.issuer_i.debug_mode_q);
  // no CSR operation (csr_go_q) in ISSUE_SPECIAL (the LS pipeline was idle when WAIT_CMT0 exited)
  AssertHelpSpecNoGoQ: assert property (@(posedge clk_i) disable iff (!rst_ni)
    kudu_top.issuer_i.ctrl_fsm_cs[8] |-> !kudu_top.ls_pipeline_i.load_store_unit_i.csr_go_q);
endmodule

`endif  // KUDU_FCOV_OFF
`endif  // CHERIoT
`endif  // KUDU_FV_HELPERS
