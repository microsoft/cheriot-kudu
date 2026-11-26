# Kudu end-to-end formal verification (fv2)

Goal: prove that kudu_top (KuduCfg1, CHERIoTEn=1, cheri_pmode_i=1) is
observationally (trace) equivalent to the serial machine defined by
cheriot-sail. The method follows CHERIoT-Ibex (Ploix, Armstrong, Melham et al.,
arXiv 2502.04738; flow in cheriot-ibex/dv/formal), adapted to Kudu's dual-issue,
scoreboarded pipeline.

Status: stage 1 (bounded) complete 2026-11-18, see CEX_TRIAGE.md §1.6; stage 2 (induction) complete 2026-11-24 (§5.1); review 1 (fv_review_1.md) harness fixes 2026-11-25, consolidated rerun showed 8 step failures (fix pending); A and B brought into scope 2026-11-26, stages 1 and 2 being re-closed; stage 3 (liveness) not started. Nothing here is part of the regression
or of fv/ (the per-module and fcov FV flows, see fv/README.md).

## 1. Toolchain

Built outside the repo under /home/scratch/fortress/kunyanliu/e2e_tools
($T). Source $T/env.sh first.

| Tool | Version | Use |
|---|---|---|
| lowRISC Sail fork (lowrisc branch, 3f317060, plus a local -sv_unroll_loops option) | 0.17.1, OCaml 4.14.2, $T/opam | Sail -> combinational SV (-sv-fun2wires etc.) |
| cheriot-sail (kudu-fv branch, see below) | $T/upstream_spec/cheriot-sail | the spec |
| psgen (2d0c1e06) | $T/bin/psgen | proof-script -> SVA/Tcl generator |
| z3 | 4.13.0 | Sail constant folding |
| JasperGold | jasper_2024.03, via submit -i -q interactive (§8) | proofs |

Loop unrolling (found 2026-11-26, when B came into scope): the SV backend
unrolls every Sail loop a fixed number of times (sail_plugin_sv.ml,
unroll_loops = Some 4, i.e. 5 iterations) and ends the unrolled copy in a
match failure, so a loop that runs longer sets sail_reached_unreachable.
Spec_NoIntErr catches this (it failed on CLMUL and CLZ, whose loops run 32
times), so no earlier result is affected: every earlier in-scope loop ran
at most 5 times. Fix: a local -sv_unroll_loops <n> option in the Sail fork
(default 4, uncommitted diff in $T/src/sail, rebuilt with $T/step_sail.sh),
and the spec build passes -sv-unroll-loops 32 (upstream_spec/build/Makefile);
the longest in-scope loop runs 32 times. Spec_NoIntErr stays the guard.

Rotates (found 2026-11-26, Cmt_Wr / Reg_Cont cex on ROR x5, x15, x13 with
x13 = 16): prelude.sail rotate_bits_right/left compute the complementary
amount as to_bits(length(n), length(v)) - n, which the SV backend emits as an
unmasked 128-bit subtraction on the dynamic sail_bits struct (0 - 16 wraps
to 2^128 - 16). The native stubs sail_shift_bits_left/right (spec/stub.sv,
copied from cheriot-ibex) shifted by the raw 128-bit y.bits, so the second
half of the rotate was 0 and ROR/RORI/ROL returned v >> n (v << n). Fix in
stub.sv: mask the shift amount to y.size and the result to x.size, matching
Sail's shift by uint(y) on size(x) bits. This is a translation fix, not a
deviation. The rotates are the only unmasked sail_bits arithmetic in
ibexspec.sv and both feed these stubs; the earlier callers (SLL/SRL/SRA,
Zba, Zbs) pass canonical operands, so no earlier result is affected.

The golden model is CHERIoT-Platform cheriot-sail (dii-read-from-file branch)
with lowRISC's FV-enabling changes ported onto it: branch kudu-fv in
$T/upstream_spec/cheriot-sail, sail-riscv submodule branch kudu-fv. Rebuild
with $T/upstream_spec/build_spec.sh (§8.1); the outputs go to $T/upstream_spec/out
(ibexspec.sv, module sail_ibexspec, about 3.8 MB), and verify.tcl reads them
from there unless $E2E_SPEC_BLD is set. $T/upstream_spec/REPORT.md
documents the port in full. The model has RV32 + C + M + A (LR.W/SC.W/AMO*.W,
added 2026-11-26) + B (Zba/Zbb/Zbc/Zbs) + Zicsr + CHERIoT.

### 1.1 Deliberate deviations from upstream cheriot-sail

Changes where the spec is made to follow Kudu rather than upstream. Each
one is a decision about the reference behaviour, not a harness workaround.

| Item | Upstream | Spec used here | Reason | Where |
|---|---|---|---|---|
| sfence.vma (0x12000073 with any rs1/rs2) | retires as a NOP in M-mode, illegal in U-mode | not decoded, so it is an illegal-instruction trap in every mode | Kudu's ir_decoder.sv traps it (only ecall/ebreak/mret/dret/wfi are legal SYSTEM funct3=0 encodings); CHERIoT has no S-mode or address translation. lowRISC 2e3ab10 removed it for Ibex too. Found as the Special_TrapExec CEX. | sail-riscv 4520628, cheriot-sail 84ab893 |
| mcause CSR write (0x342) | stores all 32 bits | keeps the Interrupt bit (31) and Cause[4:0]; bits 30:5 read as 0 | mcause is WLRL in the privileged spec. Kudu (cs_registers.sv mcause_q[5:0]) and cheriot-ibex legalize writes this way, so this is spec-compliant, not a Kudu bug. Found as the CSR_Post_Mcause and Special_State_Mcause CEXs. | sail-riscv 740ba28, cheriot-sail d7f76c4 |
| mie CSR write (0x304) | writes MEIE/MTIE/MSIE and SEIE/STIE/SSIE; bits 30:16 read as 0 | writes MEIE/MTIE/MSIE and the fast-interrupt enables 30:16; SEIE/STIE/SSIE read as 0 | CHERIoT has no S-mode, so the privileged spec makes the S bits read-only zero (an upstream Sail bug). Kudu (irqs_t mie_q) and cheriot-ibex implement the fast-interrupt enables at 30:16. Sail stored them but did not dispatch fast interrupts (now dispatched: see the fast-interrupt row). Found as the CSR_Post_Mie CEX. | sail-riscv 9d7bd77, cheriot-sail e6554e3 |
| mstatus.MPP write with an unsupported value (0b01, 0b10) | lowest supported privilege, U | Machine (0b11) | MPP is WARL, so both are legal. Kudu (cs_registers.sv) and cheriot-ibex map it to M. Found as the CSR_Post_Mstatus CEX. | sail-riscv 9d7bd77, cheriot-sail e6554e3 |
| Store MSHWM update | ext_check_phys_mem_write lowers MSHWM on stores to [MSHWMB, MSHWM) | same (restored) | Not a deviation: the FV port b0589c3 rewrote checked_mem_write and dropped the hook call, so the spec lost the store update. Kudu was correct. Found as the CSR_Post_Mshwm CEX. | sail-riscv 9d7bd77, cheriot-sail e6554e3 |
| RV32E register check (x16-x31) | Error_not_rv32e_register when rX/wX/rC/wC touch the register, at execute, after earlier side effects or faults | checked at decode: an instruction with a register field (as used by Kudu's ir_decoder.sv rf_ren_a/rf_ren_b/rf_we) naming x16-x31 decodes as ILLEGAL (C_ILLEGAL for RVC) | A Sail bug fix: the RV32E check must take priority (Kudu, cheriot-ibex and lowRISC's encdec_r all trap at decode). CSR immediates, the CSpecialRW SCR field and the reserved FENCE fields are not register uses. Compressed hints are not register uses either: Kudu zeroes their register fields (c.mv/c.add with rd=x0, c.addi/c.slli with immediate 0). Found as cause A (Special_Post_Mcause and 13 other CEXs). | cheriot-sail dd34eaa, 3e3a02c (src/cheri_decode_ext.sail rv32e_illegal) |
| M-level interrupt in U-mode with mstatus.MIE=0 | dispatchInterrupt uses its M-only path for any system without S and N: assert(priv == Machine), then no interrupt unless mstatus.MIE=1 | taken whenever it is enabled in mie and pending in mip, if priv != Machine or mstatus.MIE=1 | A Sail bug fix: the privileged spec (§3.1.6.1) always enables interrupts for a higher privilege level; Kudu and cheriot-ibex take them. Upstream would fail the assert in any U-mode step (it is a no-op in the SV build). Found as cause H (Special_TrapIrq, Spec_NoIntErr0, Exc_HandlerPC). | sail-riscv 67633f5, cheriot-sail 1663dfc (model/riscv_sys_control.sail dispatchInterrupt) |
| wfi in U-mode | illegal-instruction trap unconditionally (execute WFI, riscv_insts_base.sail:570) | illegal only when mstatus.TW=1; otherwise executes (waits) | A Sail bug fix: the privileged spec requires a U-mode WFI to trap regardless of TW only when S-mode is implemented, and CHERIoT has none. Kudu (issuer.sv ir0_mode_err: wfi & TW & priv != M) and Ibex behave this way. Found as cause F (Special_TrapSysctl, Special_Post_Priv, Special_Post_Mstatus, Special_Post_Mcause). | sail-riscv 74efd9f, cheriot-sail ba93b28 (model/riscv_insts_base.sail execute WFI) |
| Interrupt taken with PC outside PCC's representable range | handle_trap_extension: MEPCC = setCapAddr(PCC, pc) and assert(representable or untagged); reachable, since jump/branch targets are only bounds-checked at fetch and interrupts are dispatched before fetch | MEPCC = clearTagIf(setCapAddr(PCC, pc), not(representable)) | A Sail bug fix: the assert only holds after a fetch bounds fault (which clears the PCC tag first); the SV build drops asserts, so the spec kept a tagged malformed MEPCC. Kudu (cheri_pkg.sv pcc2fullcap, set_address) clears the tag. Found as the B_CsrWF and Special_Post_Mepc CEXes (round 4). | cheriot-sail 5ca398e (src/cheri_sys_exceptions.sail) |
| Platform fast interrupts (mip/mie 30:16) | not dispatched: findPendingInterrupt considers only MEI/MSI/MTI (and S/U bits), so a pending enabled fast interrupt is ignored and a lower standard one is taken | dispatched first, lowest index highest, mcause 0x10 + index (I_Fast) | Kudu (irq_fast_i, cs_registers irqs) and cheriot-ibex take them with this priority; cheriot-ibex's own sail-riscv fork has the same findPendingInterrupt. Found as the Inv_E_Cur_mcause CEX (fast 27 and MEI both pending). | sail-riscv fba1588, cheriot-sail 5adb53a |
| Zbkb/Zbkx (pack, packh, brev8, zip, unzip, xperm4, xperm8) | legal (haveZbkb/haveZbkx = true) | illegal (both false); rev8 and the rotates, shared with Zbb, stay legal | Kudu implements Zba/Zbb/Zbc/Zbs only (ir_decoder.sv). Not a bug in either: Zbk* is an optional extension Kudu does not claim. | sail-riscv 9b8c527 (model/riscv_sys_regs.sail) |
| A extension (LR.W, SC.W, AMO*.W) | absent (CHERIoT's sail-riscv has no A) | ported from sail-riscv riscv_insts_aext.sail onto the FV memory interface. The address is cs1's address, checked by ext_data_get_addr (tag, seal, permissions Load for LR, Store for SC, Load+Store for AMOs, bounds); misaligned is E_Load_Addr_Align for LR and E_SAMO_Addr_Align otherwise. The SC outcome is the match_reservation port (fun2wires), driven by the harness from Kudu's data_sc_fail_i; a failing SC writes rd = 1 and no memory; an AMO is a read plus a write in one step | Kudu implements A for integer words (cmplx_unit for AMOs, the LS pipeline for LR/SC, the reservation held by the memory). The cs1 checks follow cheri_pkg.sv check_ls_err and the CHERIoT load/store rules. | sail-riscv 9b8c527, cheriot-sail b14d7ea (RV32E decode check for LR/SC/AMO) |
| Untagged PCC/MEPCC with E > 24 (raw bounds fields) | keeps raw B/T/E of any untagged cap in PCC | unchanged; the harness relaxes the comparison | Kudu's PCC (pcc_cap_t) holds decoded base32/top33 only, so an untagged cap with E>24 (CSetHigh can build one; it reaches PCC via a trap to MTCC) loses its raw B/T. Accepted as a Kudu divergence: Special_State/Post_Pcc compare only the tag of an untagged PCC (the address is checked as the PC), and the Mepc checks compare only the address of an untagged MEPCC with E>24, since a trap builds MEPCC from the same PCC. Found as the Special_State_Pcc CEX (cause G). | fv2/spec/cheri.sv pcc_eq_noaddr, xepc_eq |

Upstream behaviour that Kudu does not match, which is still kept in the spec
and therefore excluded from scope in check/top.sv (insn_in_scope):
mtvec/mepc CSR accesses (upstream raises internal_error on a write with ASR).

### 1.2 Known Sail model issues (fix pending)

CEXs where Kudu is correct and the Sail model is wrong. The model is to be
fixed but has not been changed yet, so these properties are expected to keep
failing until it is. The per-CEX status of every run is tracked in
CEX_TRIAGE.md.

None at present. The U-mode WFI trap that was listed here is fixed (§1.1, sail-riscv 74efd9f).

### 1.3 Spec change log

Every change made to the reference relative to upstream CHERIoT-Platform
cheriot-sail (dii-read-from-file, base 1765879) and its sail-riscv submodule
(base 122bcb8). The Sail repos are the kudu-fv branches in
$T/upstream_spec/cheriot-sail (top) and its sail-riscv submodule; the build
directory $T/upstream_spec/build is not under git. $T/upstream_spec/REPORT.md
has the per-step detail of the FV port. §1.1 and §1.2 are the
behaviour-level views of the same changes.

**a. FV port (makes the model provable; intended to keep upstream behaviour)**

| Commit | Change |
|---|---|
| cheriot-sail 2e72030 | Port of lowRISC 4ee9a6c "Prepare for FV": removes the effective-address/VM paths and the revocation memory model (mem_read_cap_revoked becomes a port), turns the CHERI compressed instructions into decompress clauses, StoreCapImm uses the lowRISC version, and drops the DII-only rvfi_read65/rvfi_write65. x16-x31 stay; rC and wC_bits keep upstream's RV32E check (Error_not_rv32e_register), hoisted out of wC because wC becomes SV wires. |
| cheriot-sail ca0079c | Port of lowRISC cd5f3d3 "Never throw an exception": check_mtcc_for_fetch_exception no longer calls not_implemented when MTCC itself fails the fetch checks; it sets spec_mtcc_unrecoverable and takes the CHERI fetch exception. The harness does not count the flag as a spec error (int_err_o): a tagged, executable MTCC with an out-of-bounds address is reachable by software. |
| cheriot-sail 87ba739 | Points the sail-riscv submodule at the local kudu-fv branch. |
| sail-riscv b0589c3 | Squash of kudu-fv-steps: lowRISC sail-riscv 5fca3f9 (all FV-enabling changes: aligned-word memory with byte enables, split-access mtval, decompress+execute, C_ILLEGAL to ILLEGAL, CSR rs1 read only on write, no strings/VEXT/MMIO, PMP unreachable) with the 15 Ibex-behaviour commits reverted, and the CHERIoT semantics re-applied: MIE-gated dispatchInterrupt, MPP and mtvec reset values, RV32E check in rX/wX_bits, read_mcycle_value, misa, no mconfigptr, no A extension. Also restores Zba/Zbb/Zbc/Zbs/Zbkb/Zbkx, FENCE_TSO and SRET (illegal); keeps the __ReadRAM_Meta/__WriteRAM_Meta calls (FV tag ports); removes RV64-only compressed instructions and satp; adds register spec_trap (set by trap_handler). |

**b. Behaviour changes to the Sail source (see §1.1)**

| Commit | Change | Kind |
|---|---|---|
| sail-riscv 4520628, cheriot-sail 84ab893 | SFENCE_VMA removed: decodes as ILLEGAL in every mode | deviation (Kudu-aligned) |
| sail-riscv 740ba28, cheriot-sail d7f76c4 | mcause write keeps bit 31 and bits 4:0 (WLRL) | deviation (Kudu-aligned) |
| sail-riscv 9d7bd77, cheriot-sail e6554e3 | legalize_mie: SEIE/STIE/SSIE read 0, fast-interrupt enables 30:16 kept | Sail bug fix (no S-mode) |
| sail-riscv 9d7bd77, cheriot-sail e6554e3 | legalize_mstatus: an unsupported MPP (0b01, 0b10) becomes Machine | deviation (Kudu-aligned, WARL) |
| sail-riscv 9d7bd77, cheriot-sail e6554e3 | checked_mem_write calls ext_check_phys_mem_write again (CHERIoT MSHWM store update) | port bug fix (b0589c3 had dropped the call) |
| cheriot-sail dd34eaa | ext_decode/ext_decode_compressed: rv32e_illegal(ast) turns any instruction using x16-x31 into ILLEGAL/C_ILLEGAL at decode; the execute-time Error_not_rv32e_register path stays but is no longer reached | Sail bug fix (RV32E priority) |
| cheriot-sail 3e3a02c | rv32e_illegal: dropped the C_ADDI_HINT, C_MV_HINT, C_ADD_HINT and C_SLLI_HINT cases; Kudu zeroes their register fields, so they never trap (dd34eaa wrongly made c.mv x0,x17 illegal: g_cmt[0].Cmt_Trap) | fix of dd34eaa |
| sail-riscv 67633f5, cheriot-sail 1663dfc | dispatchInterrupt: M interrupts are enabled when priv != Machine or mstatus.MIE=1; the assert(priv == Machine) is dropped | Sail bug fix (U-mode interrupt enable) |
| sail-riscv 74efd9f, cheriot-sail ba93b28 | execute WFI: in User mode, illegal only when mstatus.TW=1 | Sail bug fix (no S-mode) |
| cheriot-sail 5ca398e | handle_trap_extension: MEPCC tag cleared when setCapAddr(PCC, pc) is not representable (interrupt at an out-of-range PC), replacing the assert | Sail bug fix (interrupt before fetch check) |
| sail-riscv 9b8c527, cheriot-sail b14d7ea | A extension (riscv_insts_aext.sail, CHERIoT cs1 checks, match_reservation as an input port); haveZbkb/haveZbkx false; RV32E decode check for LR/SC/AMO | scope extension; deviation (Kudu-aligned, Zbk*) |
| sail-riscv fba1588, cheriot-sail 5adb53a | Minterrupts.fastI (30:16), InterruptType I_Fast with FastInterruptId; findPendingInterrupt takes the lowest pending fast interrupt first; dispatchInterrupt/handle_interrupt carry the id (spec/main.sail and riscv_step.sail updated) | deviation (Kudu/cheriot-ibex-aligned platform interrupts) |

Not yet changed in the Sail source (§1.2): none.

**c. Spec build directory ($T/upstream_spec/build)**

A copy of cheriot-ibex dv/formal's Makefile, Sources.mk and spec/*.py.

- Makefile/Sources.mk: CHERI = ../../src (relative to the model directory);
  the hints and Zb* instruction files are added; riscv_insts_aext.sail stays
  out; SAIL_EXTRACTED adds the <_u operator (needed by
  encCapabilityToCapability since upstream 087d07f).
- spec/main.sail: dispatchInterrupt/handle_interrupt in the (intr, priv) form
  (no fast IRQs); try_execute maps Error_not_rv32e_register to
  handle_illegal(), as upstream riscv_step; main wraps main_inner in try/catch
  and reports Error_internal_error / Error_not_implemented on the
  spec_internal_error / spec_not_implemented outputs; main clears the four
  spec_* flags (including spec_trap and spec_mtcc_unrecoverable) at the start
  of each step.
- The post-processing scripts (fix_pmp_bug.py, unreachable_loc_info.py,
  extract_funcs.py, cull_funcs.py) are unchanged from cheriot-ibex.

**d. Harness-side spec interface fixes (fv2/spec, fv2/check)**

These change how Kudu state is mapped onto, or compared with, the spec;
they do not change the Sail model.

| File | Change | Found by |
|---|---|---|
| fv2/spec/cheri.sv regcap2sail | Overrides T with Kudu's top9 (as well as E). With cE=0 the Sail decoder derived T[8] as a denormal, so the root PCC/MTCC decoded with the wrong top. | Spec_NoIntErr0/1 |
| fv2/spec/spec_api.sv mem_read_cap_o | A capability load requires a width-8 __ReadRAM_Meta call; upstream checked_mem_read calls it on every load, so c.lwsp was flagged as a cap load. | Mem_IsCap |
| fv2/spec/cheri.sv pcc2sail | Uses pcc2fullcap_lite: pcc2fullcap's set_address clears the tag when the PC is outside the representable range, but Sail's PCC keeps its tag (the fetch fault is reported separately). | Special_State_Pcc |
| fv2/spec/cheri.sv cap_well_formed, fv2/check/checks.sv Mem_RdataCapWF | Environment assumption: tagged caps returned by memory are well formed (E <= 24, 0 <= base <= top <= 2^32); see §4.4. | CSR_Post_Mscratchc, CSR_Post_Mtdc, Special_State_Pcc |
| fv2/spec/cheri.sv pcc_eq_noaddr, xepc_eq | Untagged PCC compared on tag only; untagged MEPCC with E > 24 compared on address only (Kudu divergence G, §1.1). | Special_State_Pcc |

## 2. Spec interface (sail_ibexspec)

- One combinational step per call: inputs are the pre-state
  (x1..x31 as t_Capability, PCC, nextPC, CSRs), insn_bits and mode
  (IDEX, IFERR, IRQ); outputs are the post-state and main_result.
- Side effects are exposed as fun2wires ports: wX/wC (register write),
  read_ram/write_ram (2 granules each, addr/data/be), __ReadRAM_Meta /
  __WriteRAM_Meta (tag), mem_read_cap_revoked (revocation bit lookup).
- misa.E selects RV32E at run time. Kudu reports E=1 when cheri_pmode=1
  (cs_registers.sv:132-146), matching the Ibex harness.
- Ibex-only state (nmi, nmi_mode, mstack*) is tied off: Kudu has no NMI.

## 3. Kudu micro-architecture facts the harness relies on

All paths relative to kudu_top.

| Topic | Fact | Source |
|---|---|---|
| Program order | ir0 = ira_is0 ? ira : irb; ir1 the other | issuer.sv:285 |
| Issue | ir0_normal_issued / ir1_issued, only in CSM_DECODE | issuer.sv:305-342, 749 |
| Slot-1 restrictions | never sysctl, cmplx (AMO), error, brkpt, or after a CJALR (pmode) | issuer.sv:753-758 |
| Same-pair RAW | allowed; slot 1 gets slot 0's result by forwarding | issuer.sv:410-417 |
| Same-pair WAW | serialised (wr_req_conflict) | issuer.sv:422 |
| Serialised ops | sysctl (wfi/ecall/ebreak/mret/dret/fence.i, CSR writes to mstatus/mie), AMO, IRQ, debug, issue-time errors wait in CSM_WAIT_CMT0 until the scoreboard is empty | issuer.sv:505-540, 760-775 |
| Other CSR ops | executed in order inside ls_pipeline (csr_* ports), with loads/stores | kudu_top.sv:508-525 |
| Commit | sbd_fifo (8 entries, 2 wide) in order; committer dequeues via sbdfifo_rd_rdy | committer.sv:89-114 |
| GPR writes | 3 ports; rf_we2 = LSU (early/late load); priority 2 > 1 > 0 | committer.sv:113-179 |
| Exceptions | committer cmt_err -> issuer CSM_CMT_FLUSH -> cmt_flush to all pipes, pc_set to handler | issuer.sv:494-505 |
| Memory | data_req_o is driven by the LSU state machine, before commit; misaligned non-cap accesses split | load_store_unit.sv:344-441 |
| dcache | loads to cacheable addresses can hit without a bus access; enabled by cpuctrl.dcache_en (reset = CFG.DCacheEn) | dcache.sv, cs_registers.sv:1560 |
| Revocation | load filter (trvk) clears tags of loaded caps late; CLC destinations reserved until trvk | issuer.sv:450-490, ls_pipeline.sv |

## 4. Proof architecture

### 4.1 Where the spec is evaluated

At issue (CSM_DECODE, ir0/ir1 issued), or at CSM_ISSUE_SPECIAL for
serialised instructions/IRQs. At that point the instruction bits, PC and the
operand values actually used (forwarded) are known, which is the Ibex "ID/EX"
point.

Two chained spec instances, spec0 and spec1:
- spec0 pre-state = architectural state after every older instruction;
- spec1 pre-state = spec0 post-state (same pair).
A single issued instruction uses spec0 only.

### 4.2 Architectural pre-state (abstraction function)

Kudu's register file and CSRs lag behind issue (older instructions may be
in flight). The pre-state is therefore not read from the RF/CSRs directly.
Instead it is built as:

- GPRs: the operands Kudu itself supplies (ira/irb_full_data2_fwd), for the
  registers the instruction reads. Unread registers are left free (Ibex
  "reg_driven" trick).
- Continuity: a shadow architectural state (spec_past_*) is updated from each
  spec step's post-state. Properties then require each later pre-state to
  equal spec_past_*. This chains the instruction stream and catches wrong
  forwarding, a wrong RF write or a lost CSR update.
- CSRs: serialised instructions see committed CSR state (cs_registers_i.*_q).
  Ordinary instructions do not read or write CSRs other than through
  ls_pipeline, whose in-order execution makes cs_registers state correct
  when the CSR op executes. The spec step for a CSR op therefore takes its
  CSR inputs from spec_past_*, and the check compares the CSR effect when
  ls_pipeline performs it.
- PCC: ex1_pcc_cap / ir_pcc_cap plus the instruction PC from ir*_dec.pc.

### 4.3 Follower and checks

Each issued instruction gets a follower entry, keyed by its scoreboard slot,
holding the spec outputs (wX/wC, next PC/PCC, memory ops, CSR post-state,
main_result/exception). The entry advances with Kudu's own sbd_fifo
pointers and is cleared by cmt_flush, so it needs no separate pipeline
model.

Checks, one psgen/SVA group per instruction class:

| Check | When | Compared |
|---|---|---|
| Next PC | next issued instruction (or pc_set target) | spec nextPC / nextPCC |
| GPR write | committer rf_we* for this entry | wX/wC (address, data, capability) |
| Memory | LSU data_req_o for this entry (alt-LSU lemma) | read_ram/write_ram/meta: addr, be, wdata, is_cap |
| Load data | committer write of a load | spec result given the bus rdata |
| Exceptions | cmt_err / CSM_CMT_FLUSH and handler entry | main_result, mcause, mtval, mepc(c), handler PC |
| CSR | cs_registers write enables | spec CSR post-state |
| IRQ | CSM_ISSUE_SPECIAL with IRQ | mode=IRQ step |

### 4.4 Environment assumptions (stage 1)

Decision (2026-11-18): these restrictions — debug off, dcache off, no
mtvec/mepc CSR accesses — are kept for the rest of the e2e proof (stages 2
and 3 as well), not only for stage 1. The A and B extensions were brought
into scope on 2026-11-26; stages 1 and 2 are being re-closed with them.

- cheri_pmode_i = 1, constant boot_addr_i and hart_id_i, debug_req_i = 0,
  no breakpoint triggers.
- Instruction scope. Since review 1 (2026-11-25, fv_review_1.md gap 3) the
  scope is decided on the raw bits Sail decodes, not on Kudu's decode:
  Env_InsnScope (check/top.sv, insn_in_scope) restricts only 32-bit
  instructions, whose bits are the memory word (Fetch_Iss*); every 16-bit
  parcel is in scope, so a mis-expansion reaches the spec. Since 2026-11-26
  the only exclusions are SYSTEM CSR accesses outside the whitelist and to
  mtvec/mepc; OP, OP-IMM (all of B, including illegal encodings) and the AMO
  opcode 0x2f (LR/SC/AMO, including illegal ones) are fully in scope. The
  former Env_NoBrkpt assume is an assert (Scope_NoBrkpt: triggers cannot be
  armed), and Scope_IsComp checks Kudu's length decode against the raw low
  bits.
- Atomics. An AMO is one spec step (st_special, special case CMPLX, harness
  signal s0_cmplx) but two cmplx_unit scoreboard entries and two bus
  requests (amo_flag 0100 read, 1000 write); the follower records both
  (amo_rec_*, amo_wr_ent_q) so the usual Cmt_* and Mem_* checks apply to
  each, and Mem_AmoFlag checks data_amo_flag_o for every request (LR 0001,
  SC 0010). The SC outcome is free but tied: the spec's match_reservation
  input (spec*_sc_ok_i) must equal !data_sc_fail_i on the SC response
  (Mem_ScFail), i.e. the reservation lives in the memory, as in Kudu. A
  failing SC still issues a write request; its data and byte enables are
  unchecked, since the memory drops it.
- No revocation (Env_NoRevoke). Hence tag comparisons are exact (review 1
  gap 4): alas/alas_noaddr in spec/cheri.sv let Kudu clear a tag the spec
  keeps only when E2E_REVOKE is defined; otherwise a spurious tag clear
  fails the GPR, operand and invariant checks.
- dcache off: the harness builds kudu_top with a local copy of KuduCfg1
  with DCacheEn = 0 (cpuctrl.dcache_en then reads 0). This is a harness
  config, not an RTL change. It stays off for the whole e2e proof.
- Memory responses: bounded grant/response latency, as in fv/fv_fcov_env
  (reuse those bounds); a symbolic memory model per address for
  load data and tag.
- Instruction fetch (gap found and fixed 2026-11-25, check/fetch.sv).
  Until then this section said fetch data was "free, compared against the
  spec insn_bits at issue". It was not: Sail decodes insn_bits_of(ir_dec)
  (abs.sv), i.e. the bits Kudu itself issues, and nothing tied those bits
  to the memory at the PC. A front-end bug that issued the wrong bits for a
  PC (wrong lane or word in fetch_fifo64, a misaddressed request, stale ALT
  data, a reordered s0 FIFO entry) passed every check, because Sail and
  Kudu then agreed on the same wrong instruction. The data side never had
  this gap (Mem_Rdata* tie load data to Sail's reads only after the request
  address/size checks). Fix: a frozen symbolic halfword address fch_a and
  value fch_h (free, never change; the divider-proof trick). Env_FetchMem
  assumes that every fetch response whose granted 8-byte word covers fch_a
  returns fch_h in that lane; all other fetch data stays free. Fetch_Iss0
  and Fetch_Iss1 assert, at every issue that Sail decodes (s0 in IDEX mode,
  s1), that the issued parcel at fch_a equals fch_h: the compressed parcel
  or low half when pc == fch_a, the high half of a 32-bit instruction when
  pc + 2 == fch_a. As fch_a/fch_h are arbitrary, this proves that every
  issued instruction is the memory content at its PC. Assumption: memory
  is constant while it is fetched; self-modifying code (stores to code,
  FENCE.I) and external writes to code are out of scope. Covers
  C_FetchIss* (compressed, 32-bit, high half, word-straddling, slot 1)
  show the check fires. Helper invariants Inv_G_F* are in §5.1.
- Tagged capabilities loaded from memory are well formed (Mem_RdataCapWF in
  check/checks.sv, cap_well_formed in spec/cheri.sv): E <= 24 and decoded
  bounds 0 <= base <= top <= 2^32, using Sail getCapBoundsBits arithmetic.
  Software cannot derive other encodings from the root capabilities, and
  Kudu and Sail handle them differently (Kudu's SCR write clears the tag of a
  cap whose base wraps; the PCC keeps only decoded bounds). Stage 2 should
  justify this with a memory invariant (every tagged cap in memory was stored
  from a register). Mem_SpecRdCapWF0/1 assume the same for the spec's load
  data at issue, and Mem_RdataCapWFAny for every tagged bus response
  (including loads in a trap shadow, whose data still enter the LS
  write-back FIFO).
- No PC wrap (Env_NoPcWrap in check/top.sv, added in stage 2): no issued
  instruction ends at 2^32. Sail's CJAL/CJALR assert that the link cap at
  nextPC is representable, and that fails when nextPC wraps to 0; sail_assert
  is a no-op in the SV build, so the spec writes a malformed cap (found by
  B_RegWF in s2ind40).
- No CSpecialRW read of a lossy MEPCC (Env_NoDivGRd0/1 in
  check/spec_instance.sv, added in stage 2 / s2ind67): no non-trapping
  CSpecialRW with rd != 0 and SCR MEPCC while the spec MEPCC is untagged with
  E > 24. Under Kudu divergence G (§1.1) that MEPCC came from a lossy PCC,
  and the read would expose Kudu's decoded bounds in rd (found as the
  LsWbData cex in s2ind67; user decision 2026-11-21). Extended in s2ind73
  (f_mepc_lossy) to an E = 24 MEPCC whose T[8] is not canonical for its B[8]:
  the spec's main_inner hack (cheriot-ibex issue #11) clears PCC.B[8] at
  E = 24, a trap copies that PCC into MEPCC, and wC's encode/decode then
  recomputes T[8] from the cleared B[8], changing the top bound. Kudu returns
  the raw T, whose bounds match unmodified Sail (s2tmo1 Cmt_Wr cex).
- Divide lemma (Env_DivLemma in check/spec_instance.sv, added in stage 2 /
  s2ind74): when multdiv32 reaches MD_FINISH with the operands, operator and
  signed mode latched from a recorded non-trapping DIV/DIVU/REM/REMU issue,
  imd_val_q[0] equals the recorded Sail wX result. It composes two lemmas
  justified outside the e2e harness: (K) multdiv32 at MD_FINISH computes the
  RISC-V M result of its latched inputs; (S) Sail execute_DIV/REM computes
  the same function. K: div/tb_divk.sv (Verilator, no licence) checks every
  MD_FINISH against a reference under random flushes, idle gaps, input
  changes while busy and data_ind_timing; 16 seeds x 1M divides passed
  (2026-11-23), and two RTL mutants are caught. K is also proven formally
  (2026-11-25) in two parts. (K1) div/divfv.sv + div/divfv.tcl (Jasper,
  every multdiv32 input free): at MD_FINISH, imd_val_q[0] equals f_rdiv of
  the latched operands, operator and mode, where f_rdiv is the RISC-V
  special cases around f_udiv, a restoring divider loop (Div_Result, under
  Env_DivLemma's DIV/REM, mode 00/11 premise). It is a joint 2-induction
  over per-state and per-counter helpers, with a from-reset base case and no
  counterexample. All 84 assertions are proven or step-pass in about 40 s.
  The reference is the loop unrolled into a wire chain (Ref_Chain proves it
  equal to the loop). The chain is fed from frozen symbolic operands
  fa/fb/fsm, and each property is guarded by "the latched operands are
  fa/fb/fsm". That is equivalent, by instantiating fa := op_a_q etc., but
  both induction time frames then share one reference circuit; without it
  the step times out. Covers reach MD_FINISH, including a second divide in
  one trace. Mutants d1 (zero-divisor sign fix-up removed) and d2
  (quotient bit shifted by div_counter_d) give from-reset counterexamples.
  (K2) div/udiv_z3.py (z3) proves f_udiv equals unsigned / and % for all
  32-bit inputs (loop invariant per step plus uniqueness of div/mod), and
  f_rdiv equals the RISC-V M DIV/DIVU/REM/REMU semantics, including a zero
  divisor and INT_MIN / -1. Runs: /home/scratch/fortress/kunyanliu/divpf
  (jg5_*, mut/). S: by inspection of the generated spec: operands are
  sign/zero-extended to 128 bits; DIV gives -1 on a zero divisor, else the
  truncating quotient, clamped to xlen_min_signed when signed and above
  xlen_max_signed; REM gives the dividend on a zero divisor, else the
  truncating remainder (stub.sv: SV signed / and %, which truncate toward
  zero); wX takes the low 32 bits. The iterative divider is otherwise intractable inside the
  induction. Inv_H_DivFol/Busy/Wait/Done in check/inv.sv tie the divider
  state to the record; Cmt_DivData reports the divide write data, so
  Cmt_Wr stays assumption-free.
- Multiply lemma (Env_MulLemma in check/spec_instance.sv, added in stage 2,
  2026-11-24): same scheme as the divide lemma. When multdiv32's
  mult_en_i is high, the harness records the issuing step's Sail operands
  (X(rs1), X(rs2)), instruction and wX result, and mirrors the multiplier's
  op_a/op_b/operator/signed_mode. Until the next enable, mult_result_o equals
  the recorded wX when the mirrored inputs, operator and signed mode match
  the recorded ones. It composes (K) and (S), both proven formally:
  K: Conformal LEC proves the signed_mult_33x33_wallace tree equal to a*b
  for all inputs (kudu_e2e/mullec2_*, 66/66 Equivalent in each of four
  variants: b[32] = 0 and b[32] = 1 cover all inputs; a mutated compressor
  gives 64/66 Non-equivalent). Jasper proves the plStageNum = 5 pipeline gives
  product == $past(a*b) after an enable and holds it otherwise
  (kudu_e2e/mulpipe_*: P_Pipe, P_MulProd, P_Hold). mult_result_o selects
  [31:0] or [63:32] by the mult_op latched on enable.
  S: Jasper proves the 256-bit product in the generated execute_MUL equals
  the 66-bit signed product of the 33-bit sign/zero-extended operands
  (kudu_e2e/mulnarrow_*, P_eq). By inspection, execute_MUL extends each
  operand by signed_rs1/rs2 and takes bits [31:0] or [63:32] for wX.
  Without the lemma, MulIss_C[1-4] timed out (40 min) even with K assumed
  (Ext_K_MulProd/Hold in check/inv.sv, now opt-in with E2E_MULPROD), with
  the multiplier output cut, or with a narrowed spec. The solver had to
  equate two different multipliers whose operands are equal only through
  the spec's register-file mux. With the lemma, MulIss_C[1-4] step-pass in
  about 70 s each (s2mull_20261124_200527, product cut by stopat).

## 5. Stages

| Stage | Scope | Exit criterion |
|---|---|---|
| 0 | toolchain, spec generation, design (this doc) | done when the spec elaborates with kudu_top in JG |
| 1 | bounded per-instruction checks for ALU, branch, jump, CJALR, load/store, CSR, mult/div, single- and dual-issue | (a) every Cov_* cover covered (non-vacuity); (b) no CEX within the exhaustive bound reached by the bounded engines (B/B4/K, default and E2E_ZERO_WAIT environments), with the bound per property recorded; (c) no CEX from a depth-40 bug hunt (engines L/Ht); every CEX explained, real bugs reported. Exhaustive BMC to depth 20-30 is not feasible: the cost grows about 3.5x per cycle (depth 12 in 200 s, 13 in 970 s); deeper guarantees come from stage 2. **Done 2026-11-18** (CEX_TRIAGE.md §1.6): all Cov_* covered; 0 CEX in jobs 047761391/047761525/047761539/047761523; cex-free bound min 8 / median 12 (default env), min 7 / median 11 (zero-wait); 2 harness properties proven unbounded; the L hunt stalled at bound 9. |
| 2 | unbounded: invariants (follower/scoreboard consistency, DTI on RF/CSR caps, memory alt-LSU lemmas), continuity across both slots | all stage-1 properties proven unbounded. **Done 2026-11-24** (§5.1): step-ordered 3-induction plus from-reset base case, under the §4.4 assumptions (incl. Env_DivLemma, Env_MulLemma) |
| 3 | liveness of spec_en (no deadlock), top-level observational-correctness theorem | proven, documented in fv/README.md |

### 5.1 Stage 2 method (done 2026-11-24)

Invariants live in check/inv.sv (included by check/top.sv, followed only by
check/fetch.sv, which holds the fetch-data part of group G), grouped:

- A: local RTL state (priv/mpp legal, debug off, LSU/lsu_if FSM, LSU
  error/CSR flags, CSR scope of the LSU request).
- B: harness past_* state legal (past priv/mpp in {M, U}).
- C: follower/scoreboard consistency, and shadow ordering: a trapping or
  shadow sbd entry implies shadow_q, every younger entry is shadow, shadow_q
  comes from cmt_err_q or a non-shadow trapping entry, and ISSUE_SPECIAL
  never coincides with shadow_q.
- D: counts (sbd depth vs lsu_if/lsq; LS entries in the sbd == waw_fifo
  count == LSQ + outstanding response + wb_fifo; wb_fifo room and waw depth
  bounds).
- E: applied-CSR ghost e_cur_*: the spec CSR state Kudu has applied so far,
  updated in program order when Kudu applies a step (CSR instruction at
  csr_chk1_q from its LSQ entry's post-state; serialised non-LS step or trap
  at ISSUE_SPECIAL from s0_post; shadow trap at CMT_FLUSH from the frozen
  past_*). Inv_E_Cur_*: Kudu CSR == e_cur; Inv_E_Eq_*: e_cur == past_* when
  nothing is pending (no shadow, LSQ empty, no CSR op in flight). mshwm
  excluded. (A first single-snapshot "lag" version failed BMC: CSR
  instructions issue from DECODE in either slot, not only at ISSUE_SPECIAL.)
  A sentry CJALR sets/clears mstatus.mie at issue (EX1 is the issue cycle),
  so e_cur follows it immediately and a later non-mstatus CSR apply keeps
  it. Linking invariants: each LSQ entry also records the spec pre-state;
  outside the shadow the entries chain e_cur -> pre(head), post(k-1) =
  pre(k), post(youngest) = past_*, non-CSR entries leave the CSRs
  unchanged. mstatus.mie is left out of the chain except for mstatus/mie
  writes (sysctl.csrw), which are serialised and so the only entry pending.
  Not a bug: an LS trap takes MPIE/MEPCC from the error info captured at
  issue (has_pcc), so a CJALR in its shadow does not corrupt them.
- F (todo): GPR refinement map (regfile + in-flight sbd writers vs
  past_regs); then mshwm, PCC and PC/fetch state.
- Capability well-formedness (WF): inv_cap_ok (tagged caps survive the
  memory encode/decode round trip and are cap_well_formed) on the spec side
  (Inv_B_RegWF/PccWF/CsrWF) and on Kudu storage (Inv_A_RfWF/FwdWF/CsrWF, the
  ALU/mult write-back results and every LS write-back FIFO slot). The spec
  reads its operands from Kudu, so WF must hold on both. Write-back WF
  (AluWbWF0/1, MulWbWF, MulEx2WF) only covers rd != 0: the register file
  has no x0 flops, so a JAL/AUIPCC/CJALR result aimed at x0 is discarded and
  may be malformed. Inv_A_MulEx2WF covers the mult EX2 result (CJALR link or
  CSetBounds), Inv_A_LsuCs1WF the cs1 capability of an LSU CSR request (the
  SCR write data), and f_kreq_we_ok requires it for CSR LSQ entries.
  Inv_A_KPccWF (inv_kpcc_ok) covers Kudu's ex1_pcc_cap_q: E <= 24, perms ==
  expand_perms(cperms), base/top aligned to 2^E, base <= top <= 2^32,
  length <= 2^(E+9), and pcc2sail of it passes inv_cap_ok. ir_pcc_cap_q is
  excluded: it is only a fetch-check prediction and may be stale.
- PCC: the Sail PCC address is not the PC (CJALR keeps cs1's address, a trap
  installs MTCC, MRET MEPCC), so Inv_F_PccBnd decodes bounds at
  past_pcc.address, and Inv_F_ShPcc ties past_pcc to mtvec, address
  included, inside a trap shadow.
- G, fetch data (check/fetch.sv, for Fetch_Iss0/1): ghost fch_rsp_addr /
  fch_in_addr hold the granted address of the response on the bus and in
  the prefetch input register. fetch_fifo64 entry i holds word
  instr_addr_q[31:3] + i; the input register, the due response and the held
  or next request (stored_addr_q / fetch_addr_q) are the following words
  unless discarded by a branch (Inv_G_FInA/FBusA/FHeld/FNext), and the fifo
  has room for all of them (Inv_G_FRoom). Data invariants then carry
  "lane at fch_a == fch_h" through the input register, the fifo entries
  (Inv_G_FQD), the ALT table (a live entry holds the words just below
  nxt_addr, Inv_G_FAltD), the s0 FIFO (raw parcels, Inv_G_FS0D) and
  IR0/IR1 (Inv_G_FIr0D/FIr1D). An IR entry that owns an ALT entry falls
  through to its first word (Inv_G_FS0Alt/FIr0Alt/FIr1Alt), and each ALT
  id has at most one in-flight owner (Inv_G_FAltU), so a restored ALT
  entry lines up with the corrected PC.

Each invariant is first BMC-checked from reset (s2invbmc runs), then
2-induction-checked by a diagnostic sweep: free initial state
(-init_state empty, assume no reset, assume past_valid), every other
property assumed on all cycles, the target assumed only on the first 2
cycles (assume -from_assert p -bound 2) and proven at trace length 3.
"cex 3" means a genuine step failure relative to the others; "undetermined
4" means the step holds. The first sweep (pass 1) did not assume the target
on earlier cycles and so was not induction; its results are void.
Mutual same-cycle assumption is circular, so the sweep is diagnostic only;
the final proof is a monolithic/step-ordered prove with all invariants as
asserts.

Stage-2 status (2026-11-24): the induction step and base case hold for all
825 properties.
- Step-ordered (levelled) proof, round 7 (kudu_e2e/s2fin7[0-3]_20261124_054458,
  s2r7l1, s2r7l2), sound by induction on (time, level):
  - L0: 814 properties, each proven with every property assumed on the first
    2 cycles.
  - L1: AluData0/1 and MulEx2Data, with the issue-time splits AluIss_C/X and
    MulIss_C assumed on all cycles.
  - L2: Cmt_Wr[0/1] and Reg_Cont*, with the L0 helpers, L1, MulData and
    LsWbData assumed on all cycles.
  - Results: 0 cex. L0 properties that timed out at 15 min were rerun at
    40 min (retries A-D) and pass.
  - MulIss_C[1-4] pass only with Env_MulLemma (§4.4). Every other property
    was proven without that assumption, so its result also holds with it.
- Base case: from-reset BMC (s2bmc31/32/33).
  - Every helper lemma and issue split is cex-free to depth 7-16, above the
    induction depth of 3.
  - s2bmc33 adds covers for Env_MulLemma firing and for MULHSU/MULHU
    retiring, all reached at depth 7.
- Special_Post/State_Mshwm step-pass (group M), so the earlier mshwm
  deviation note is closed (CEX_TRIAGE §4.12).
- Mutation testing done (§5.2). Open: stage 3.
- Fetch consistency (2026-11-25, §4.4): Fetch_Iss0/1 and the 38 group-G
  fetch invariants (incl. helpers Inv_G_FRoom, Inv_G_FAltU) step-pass in
  the same L0 form (runs fchstp1-3); from-reset BMC finds no cex to depth
  10-11 (fchbmc1/2); all C_FetchIss* covers hit at depth 5-6. Env_FetchMem
  only constrains instruction-fetch data, so earlier results stand.

### 5.2 Mutation testing (2026-11-25)

Eight one-line RTL mutants (full rtl copies in
$T/kudu_e2e/mut_20261124_221849/m*/, each with a mut.diff) were run through
the harness unchanged. A mutant counts as caught when any property the
stage-2 proof relies on gets a counterexample.

- Pass 1, mutrun.tcl: from-reset BMC of the 95 non-Inv asserts, trace length
  12, 20 min per mutant. In that time the BMC reaches only depth 8-9 (the
  first retirement needs depth 6-7), so it sees one or two instructions.
- Pass 2, steprun*.tcl: the stage-2 induction step (§5.1, L0 form: free
  state, every property assumed for 2 cycles, checked at length 3) on the
  properties relevant to each BMC escapee. Every property that fails there
  step-passes on the real RTL in round 7, so the failure is due to the
  mutant.

| Mutant | Bug | Caught by |
|---|---|---|
| m1_blt | BLT compares unsigned | BMC: PC_Cont0/1 (depth 6-7) |
| m2_sra | SRA shifts logically | BMC: Reg_Cont0/1_Rs1/Rs2, Cmt_Wr |
| m3_mulhsu | MULHSU decoded signed x signed | Step: MulIss_C[3], MulEx2Data |
| m4_lbext | LB zero-extends | BMC: Cmt_Wr[0] (depth 7) |
| m5_ldperm | load-permission fault removed (pmode RV32 loads) | Step: Cmt_Trap[0/1], Mem_GoTrap, Inv_F_LsqTrap/Cause, Inv_F_CurTrap/Cause, Inv_F_RespTrap |
| m6_mret | MRET sets mie = 1 instead of mpie | Step: Special_Post_Mstatus |
| m7_fwd | forwarding match for operand 1 forced off | BMC: Reg_Cont0/1_Rs1/Rs2 (depth 6) |
| m8_candperm | CAndPerm keeps cs1 perms | BMC: Reg_Cont0/1_Rs1/Rs2 (depth 7) |

- m3 is caught both with the real multiplier and with the s2mull recipe
  (stopat on the product, Env_MulLemma). MUL, MULH and MULHU still
  step-pass. Env_MulLemma does not mask the mutant: its RTL half constrains
  the result by the latched signed mode, and the mutated mode no longer
  matches the instruction.
- Env_MulLemma/Env_DivLemma would mask a bug inside the multiplier or
  divider datapath itself. Those blocks are covered by the block-level
  LEC/Jasper proof (multiplier) and the divfv Jasper + z3 proof (divider)
  instead (§4.4).
- CSR_Post_* do not see m6: they check CSR instructions only. MRET's mstatus
  update is checked at the serialised point (Special_Post_*).

Batch 2 (CHERI checks, decoder, LSU byte enables, interrupts), same method;
8 of 8 caught. Every step counterexample is on a property that step-passes on
the unmutated RTL (round 7).

| Mutant | Bug | Caught by |
|---|---|---|
| n1_basebound | cheri_pkg base violation uses <= instead of < | Step: Cmt_Trap[0/1], Inv_F_LsqTrap[0], Inv_F_CurTrap, Inv_F_RespTrap |
| n2_csealse | CSeal ignores cs2's SE permission | Step: AluIss_X[4] (CSeal), both pipes |
| n3_cunsealgl | CUnseal GL taken from cs1 only | BMC: Reg_Cont0/1_Rs1/Rs2, Cmt_Wr (depth 7) |
| n4_jalsentry | JAL link sentry IE/ID seal types swapped | BMC: Reg_Cont0/1_Rs1/Rs2, Cmt_Wr (depth 6-7) |
| n5_csrai | C.SRAI decoded as C.SRLI | BMC: Reg_Cont0/1_Rs1/Rs2, Cmt_Wr (depth 7) |
| n6_shbe | SH at offset 2 uses byte enables 0011 | Step: Mem_StoreBe, Mem_StoreData |
| n7_irqmie | interrupts taken regardless of mstatus.MIE | Step: Special_TrapIrq, Exc_HandlerPC |
| n8_irqprio | external interrupt loses priority to software | Step: Special_Post_Mcause |

Fetch mutant (2026-11-25, after the §4.4 fetch fix;
$T/kudu_e2e/fchmut1_20261125_190513). Before the fix this mutant could not
have been caught: Sail decoded whatever bits Kudu issued.

| Mutant | Bug | Caught by |
|---|---|---|
| f1_lane | fetch_fifo64 slot 1, pc[2:1] == 1, 32-bit insn takes rdata128[95:64] instead of [79:48] | BMC: Fetch_Iss1 (depth 7), Fetch_Iss0 (8), Inv_G_FS0D[0] (7) |

## 6. Soundness checklist

- Every env assumption above is listed with its justification; vacuity
  checked with covers for every check (each instruction class retires).
- Free (undriven) spec inputs are only for registers the instruction does
  not read.
- Exclusions (debug, dcache, mtvec/mepc CSR accesses) are explicit assumes, not
  silent cut points.
- Spec strengthening (Kudu clearing more tags than Sail, e.g. load filter)
  is documented per case; with revocation off the tag comparison is exact
  (review 1 gap 4).
- Bus outputs (review 1 gap 7, check/checks.sv): untagged capability stores
  write the spec's 64 bits (Mem_CapStoreBits), capability stores enable all
  bytes (Mem_CapStoreBe), data_amo_flag_o matches the access kind
  (Mem_AmoFlag; was Out_NoAmoFlag before A was in scope), and an
  ungranted request is held unchanged (Bus_InstrReqHold, Bus_DataReqHold).
  cheri_fatal_err_o is checked against the spec's mtcc_unrecoverable
  (Out_FatalErr0/1, Cov_FatalErr): when the spec takes a fetch exception
  with an unusable MTCC, Kudu enters the trap and raises the flag. Kudu also
  flags other traps with a bad MTCC (it is informational), and the
  addr <= top < addr + 2 corner is waived (Kudu checks addr <= top only).
  Not checked: the revocation-map (tsmap) port, which needs a revocation
  model.
- Instruction bits: Sail decodes Kudu's issued bits, so they must be tied
  to memory separately. Fetch_Iss0/1 (check/fetch.sv) prove that they are
  the bus data at the PC, assuming memory is constant while it is fetched
  (§4.4). Before 2026-11-25 this link was missing.
- Arithmetic lemmas (Env_DivLemma, Env_MulLemma) assume only identities
  proven outside the harness (§4.4). The RTL halves of both are proven
  formally; Sail's divide half is by inspection. Their base case is
  BMC-checked from reset with the real RTL (no cut points), with covers
  showing that each lemma fires.

## 7. Layout

| Path | Contents |
|---|---|
| fv2/README.md | this document |
| fv2/CEX_TRIAGE.md | every counterexample found and how it was resolved |
| fv2/fv_review_*.md | external reviews of the proof and their action items |
| fv2/check/ | harness: top wrapper, abstraction, follower, checks; inv.sv holds the stage-2 invariants; fetch.sv is the instruction-fetch consistency check (§4.4) |
| fv2/spec/ | spec_api wrapper adapted from Ibex, native-function stubs, CHERI helpers |
| fv2/div/ | block-level divider proof (divfv.sv/.tcl, udiv_z3.py) |
| fv2/verify.tcl | interactive JasperGold set-up (analyze + elaborate only) |
| fv2/flow/ | batch run templates and scripts for stages 1 and 2 (§8) |
| fv2/spec_build/ | everything needed to regenerate the spec: build script, Makefile, post-processing scripts, main.sail, the fork diffs and the toolchain scripts (§8.1) |
| $T/kudu_e2e/ | JG run directories (scratch), STATE.md run log |
| $T/upstream_spec/ | Sail fork working copies and the generated spec (out/) |

## 8. Running the flow

All commands run from a login shell on the LSF cluster. Jasper licences are
scarce: run at most 2 Jasper jobs at a time. Each job needs about 64-80 GB.

### 8.1 Toolchain and spec (only when the spec or Sail changes)

The tools live in $T = /home/scratch/fortress/kunyanliu/e2e_tools. To
recreate them elsewhere, set T and use the scripts in spec_build/toolchain/:

1. Clone lowRISC sail (https://github.com/lowrisc/sail.git) at the commit
   in spec_build/patches/BASE.txt into $T/src/sail and apply
   patches/sail/sail_plugin_sv_unroll.diff.
2. step_opam.sh: opam root, the sail switch (OCaml 4.14.2) and sail's
   dependencies.
3. step_sail.sh: make sail + make install (a release build; a dune dev
   build makes the SV plugin fail to load with an interface mismatch).
4. env.sh (toolchain) sets PATH, OPAM* and SAIL_DIR; source it before any
   step below. step_sv.sh is the original cheriot-ibex spec build
   ($T/ibex_formal), kept for reference only.

The spec sources are two forks, kept as squashed diffs against the bases
recorded in spec_build/patches/BASE.txt (which also lists the fork commits):

```
F=$T/upstream_spec
git clone https://github.com/lowrisc/cheriot-sail.git $F/cheriot-sail
cd $F/cheriot-sail && git checkout <cheriot-sail base> && git submodule update --init sail-riscv
git apply --binary fv2/spec_build/patches/cheriot-sail.diff
git -C sail-riscv apply --binary fv2/spec_build/patches/sail-riscv.diff
```

Then copy spec_build/{Makefile,Sources.mk,spec/} to $F/build/ and
spec_build/{build_spec.sh,env.sh} to $F/, and build the spec on the farm
(a few minutes; the post-processing peaks at several GB):

```
submit -i -m 24 $F/build_spec.sh
```

The outputs (ibexspec.sv, sail_genlib_ibexspec.sv, extracted.sv, VERSION)
go to $F/out/, where verify.tcl and the run templates read them.
flow/check_pyslang.py is a licence-free parse/elaboration check of the whole
harness and spec (pyslang; submit it with -m 16).

### 8.2 Run directories

flow/mkrun.sh instantiates a template into a fresh run directory and
writes its go.sh (submit -i -q interactive):

```
fv2/flow/mkrun.sh <template.tcl> <rundir> [mem_GB=64] [timeout_min=1200]
<rundir>/go.sh          # blocks until the job ends; run it in the background
```

Each run writes <rundir>/jg.out, res.txt (one line per property: status,
bound, name; written after the prove finishes) and a VCD per cex or cover.
While a job runs, the IPF055 lines of jg.out name each cex as it is found.
flow/vcdq.py <vcd> '<regex>' prints the value changes of matching signals.

### 8.3 Stage 1 (bounded, from reset)

| Template | Content | Typical job |
|---|---|---|
| flow/stage1_bmc_cover.tcl | all Cov_* covers (non-vacuity, §5 criterion a) | -m 80 -t 110 |
| flow/stage1_bmc_assert.tcl | every non-Inv assert, BMC to depth 16 under an 80 min limit (criterion b) | -m 80 -t 110 |

Edit set_max_trace_length, set_prove_time_limit and the engine list in the
generated run.tcl for deeper runs. In res.txt, "undetermined N" means no cex
to depth N; record the bounds in the §5 table. Stage 1 is closed when every
cover is covered and no assert has a cex.

### 8.4 Stage 2 (induction, §5.1)

flow/stage2_step.tcl is the step-mode base (free initial state, rst_ni high,
trace length 3); flow/mkfinal8.py rewrites it for one level of the
step-ordered induction, and flow/stage2_fetch_base.tcl is the from-reset base
case of the fetch checks. A full run is 5 jobs:

```
R=$T/kudu_e2e/r9_$(date +%Y%m%d_%H%M%S); FL=fv2/flow
for j in l0s0 l0s1 l1 l2; do $FL/mkrun.sh $FL/stage2_step.tcl ${R}$j; done
python3 $FL/mkfinal8.py ${R}l0s0 ${R}l0s0 0 0 2
python3 $FL/mkfinal8.py ${R}l0s1 ${R}l0s1 0 1 2
python3 $FL/mkfinal8.py ${R}l1 ${R}l1 1
python3 $FL/mkfinal8.py ${R}l2 ${R}l2 2
$FL/mkrun.sh $FL/stage2_fetch_base.tcl ${R}base 80 240
nohup bash $FL/queue8.sh ${R}{l0s0,l0s1,l1,l2,base}/go.sh > ${R}_queue.log 2>&1 &
```

queue8.sh runs the jobs in order, at most 2 at a time (about 12-16 h in
total). In res.txt (trace length 3), "undetermined 4" is a passing step,
"cex 3" a step failure (a VCD is saved) and "undetermined 3" a time-out;
"proven" is an unbounded proof. Stage 2 is closed when every L0/L1/L2
property passes its step and the base job (and the stage-1 assert BMC as the
base case of the other properties) shows no cex. Record each failure and its
fix in CEX_TRIAGE.md.

### 8.5 Keeping fv2/ in step

The run templates in flow/ are copies of the run.tcl of the latest
stage-1/stage-2 runs with the run directory and fv2 path replaced by
@RUNDIR@ and @FV2@, and spec_build/ mirrors $T/upstream_spec. Update them
whenever a run script, the spec build or a fork changes (regenerate
patches/*.diff and BASE.txt with git diff --binary <base> HEAD).
