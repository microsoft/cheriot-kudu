# Counterexample triage tracker

Status of every counterexample (CEX) from the e2e (fv2) and clean fcov (fv)
formal runs. Update this file as each CEX is triaged.

Status values:

- **divergence**: a real Kudu/Sail difference, accepted by decision; the harness relaxes the comparison (README §1.1).
- **spec bug, fix pending**: Kudu is correct and the Sail model is wrong; the model is not yet fixed (README §1.2).
- **fixed (spec deviation)**: Kudu's behaviour is correct, and the spec was changed to match it (README §1.1).
- **fixed**: a harness or spec bug, already fixed.
- **fixed, unverified**: fixed, but not yet re-run.
- **waived**: accepted, with a reference.
- **needs decision**: root cause known; the user must choose how to handle it.
- **untriaged**: not analysed yet.

Paths: E2E = /home/scratch/fortress/kunyanliu/e2e_tools/kudu_e2e,
CLEAN = /home/scratch/fortress/kunyanliu/fvclean_repo_20261116_123102.

## 1. e2e run 047757291 (E2E/jg_20261117_010914, depth 20, 2026-11-17)

Result: 24 CEX, 0 proven, 68 undetermined (E2E/jg_20261117_010914/res.txt).
Waveforms, where they exist, are in E2E/dbg_csr_20261117_022534
(kudu_e2e_top.\<property\>.vcd, debug job 047757441).

### 1.1 Triaged

Second debug pass (2026-11-17 15:54, current harness including the mcause and PCC
fixes): jobs 047759108 (b), 047759109 (c), 047759116 (fixchk), 047759112 (a, still
running). VCDs are in E2E/dbg_{a,b,c,fixchk}_20261117_155449. Per-CEX summaries
(spec instruction stream plus a signal table) are in E2E/cexsum_20261117/\<property\>.txt,
generated with E2E/tools/cexsum.py. Every CEX was re-found with a new trace, so the
cycle counts below are from the second pass.

The CEXs fall into seven root causes, A to G.

**A. Sail checks RV32E too late (Sail bug, fixed in cheriot-sail dd34eaa + 3e3a02c, unverified).** Kudu traps an instruction
that names x16-x31 as illegal at decode (mcause 2, mtval 0, no side effects).
Sail decodes and executes it, and only raises Error_not_rv32e_register when it
touches the register. By then a CSR write has already happened, or a CHERI or
alignment fault has been raised first. The mismatch is caught at the trap
(Special_Post_*), or later at the next special or CSR instruction
(Special_State_*, CSR_Post_*). This is the same bug as Special_Post_Mcause.

| Property | Cycles | Status | Trapping instruction and mismatch |
|---|---|---|---|
| Special_Post_Mcause | 8 | fixed (verified 047760210) | clc x31,-1(x15) (0xfff7bf83). Kudu mcause 2; Sail 0x1c (CHERI fault first). README §1.2. |
| Special_Post_Mie | 8 | fixed (verified 047760210) | csrrs x16,mie,sp (0x30412873). Sail writes mie=0x20, Kudu leaves 0. |
| Special_Post_Mscratch | 8 | fixed (verified 047760210) | csrrs x16,mscratch,sp (0x34012873). Sail mscratch=0x2, Kudu 0. |
| Special_Post_Mshwm | 8 | fixed (verified 047760210) | csrrsi x16,mshwm,0x10 (0xbc186873). Sail mshwm=0x10, Kudu 0. |
| Special_Post_Mshwmb | 8 | fixed (verified 047760210) | csrrs x16,mshwmb,s0 (0xbc242873). Sail mshwmb=0x4000000, Kudu 0. |
| Special_Post_Mstatus | 8 | fixed (verified 047760210) | csrrsi x16,mstatus,0x1e (0x300f6873). Sail sets MIE, then the trap copies it to MPIE=1. Kudu MPIE=0. |
| Special_Post_Mtval | 8 | fixed (verified 047760210) | c.clcsp x31 (0x6ffe). Sail raises a CHERI tag fault on csp first (mtval 0x42 = csp, tag violation). Kudu: illegal, mtval 0. |
| Special_State_Mcause | 12 | fixed (verified 047760210) | lw x24 (0xeef5ac03). Sail mcause 0x1c, Kudu 2. Caught at the next trap. The mcause legalisation fix did not clear this property; this new trace is cause A. |
| Special_State_Mie | 12 | fixed (verified 047760210) | csrrwi x20,mie,0x12 (0x30495a73). Sail mie=0x2 (SSIE, see also B), Kudu 0. |
| Special_State_Mstatus | 12 | fixed (verified 047760210) | csrrw x17,mstatus,s0 (0x300418f3). Sail MPIE=1, Kudu 0. |
| CSR_Post_Mscratch | 12 | fixed (verified 047760210) | csrrw x24,mscratch,gp (0x34019c73). Sail mscratch=0x100, Kudu 0. Caught at a later csrrs of mscratch. |
| CSR_Post_Mshwmb | 12 | fixed (verified 047760210) | csrrs x25,mshwmb,s1 (0xbc24acf3). Sail mshwmb=0x50, Kudu 0. |
| CSR_Post_Mcause | 12 | fixed (verified 047760210) | c.clcsp x16 (0x6802). Sail mcause 4 (misaligned first), Kudu 2. The mcause legalisation fix removed the first trace (csrrw of 0x80); this new trace is cause A. |

**B. Sail mie keeps the S-mode bits (Sail bug, now a spec deviation).**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| CSR_Post_Mie | 9 | fixed (spec deviation) | csrwi mie,2 sets SSIE. Sail legalize_mie (riscv_sys_regs.sail:381) writes SEIE/STIE/SSIE even though CHERIoT has no S-mode. The privileged spec makes them read-only 0 in that case. Kudu implements only MSIE/MTIE/MEIE and the fast-interrupt bits 16-30 (rtl/cs_registers.sv:346-351), so it reads 0. Related latent difference: Sail drops bits 16-30, which Kudu keeps (platform-defined bits; allowed). Fixed in the spec: mie keeps MEIE/MTIE/MSIE and bits 30:16; the S bits read 0 (sail-riscv 9d7bd77, README §1.1). Recheck 047759218: this trace is gone; the property now fails at 12 cycles via cause A (csrrs x20,mie,sp, 0x30412a73). |

**C. mstatus.MPP WARL legalisation differs (both legal; now a spec deviation).**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| CSR_Post_Mstatus | 10 | fixed (spec deviation) | csrrc ra,misa,tp, then csrrw ra,mstatus,ra. misa[12:11] = 0b10 (M set, L clear), so MPP is written with the reserved value 2. Kudu maps an illegal MPP to M (rtl/cs_registers.sv:674), as cheriot-ibex does. Sail maps it to the lowest supported mode, U (riscv_sys_regs.sail:277). MPP is WARL, so both are legal. Fixed in the spec: an unsupported MPP maps to M (sail-riscv 9d7bd77, README §1.1). Recheck 047759218: this trace is gone; now fails at 12 cycles via cause A (csrrsi x16,mstatus,8, 0x30046873). |

**D. The spec port drops the MSHWM update on stores (harness/spec-port bug).**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| CSR_Post_Mshwm | 11 | fixed | csrrs a2,mshwm,sp sets mshwm=0x8000. Then csw ra,1028(cra) stores to 0x404, inside [mshwmb=0, mshwm). Kudu lowers mshwm to 0x400 (rtl/cs_registers.sv:983-986), which is correct. The spec keeps 0x8000. Upstream cheriot-sail does this update in ext_check_phys_mem_write (src/cheri_addr_checks.sail:237). Our FV port commit (sail-riscv b0589c3) rewrote checked_mem_write and dropped that call, so the generated spec only writes MSHWM from CSR instructions. Kudu is correct. Fixed: checked_mem_write calls ext_check_phys_mem_write again (sail-riscv 9d7bd77). Recheck 047759218: this trace is gone; now fails at 12 cycles via cause A (csrrw x16,mshwm,s1, 0xbc149873). |

**E. Unconstrained memory supplies malformed tagged capabilities.** The formal
memory can return any 65-bit value with the tag set. That includes encodings
software can never create: a decoded base that wraps below 0, or E > 24.
Kudu and Sail treat these differently. Note that the PCC CEX "fixed" earlier
(pcc2fullcap_lite) was also a cap with a wrapping base.

| Property | Cycles | Status | Finding |
|---|---|---|---|
| CSR_Post_Mscratchc | 12 | fixed | clc ca4 loads a tagged cap: addr 0x5f800, E=11, B=0x1bf, T=0x11c, so the decoded base is 0xfffdf800 (> top 0x8e000). cspecialw mscratchc,ca4: Kudu legalize_scr (rtl/cheri_pkg.sv:1068) calls set_address on every SCR write, and set_address clears the tag because addr < base32 (borrow in tmp33). The input tag was 1 (scr_wfcap1.valid=1, scr_wfcap2.valid=0). Sail writes MScratchC unchanged (cheri_insts.sail:411), with the tag kept. Recheck 047759222: no CEX up to 12 cycles (bound 13, 15 min). |
| CSR_Post_Mtdc | 12 | fixed | Same mechanism. cspecialrw cra,mtdc,ca5 with ca5 from clc: addr 0x1880, E=5, B=0x1c4, so base32=0xfffff880. Kudu clears the tag; Sail keeps it (cheri_insts.sail:410). Recheck 047759222: no CEX up to 12 cycles (bound 13). |
| Special_State_Pcc | 14 | fixed | clc cra loads a cap with cE=5, i.e. E=26 (> cap_max_E 24). cjalr cra installs it as PCC. Decoded bounds are identical in both models (top truncates to 0), and both take IFERR at 0x80000046. Only the raw field differs: Kudu's PCC stores top33/base32, so pcc2sail rebuilds T=0, while Sail keeps T=0x100. Harness comparison artefact; if the PCC is later saved to MEPCC and stored, the memory bits would differ too. The earlier pcc2fullcap_lite fix stays valid; this is a new trace. Recheck 047759222: this E=26 trace is gone, but a new 15-cycle CEX is cause G below. |

Resolution for E: the harness now assumes that loaded tagged capabilities
are well formed (Mem_RdataCapWF, cap_well_formed: E <= 24 and
0 <= base <= top <= 2^32; README §4.4).

Fix checks: jobs 047759218 (E2E/dbg_fx1_20261117_163217: Mie, Mstatus, Mshwm)
and 047759222 (E2E/dbg_fx2_20261117_163217: Mscratchc, Mtdc, Pcc).

**F. Sail traps wfi in U-mode unconditionally (Sail bug, fixed in sail-riscv 74efd9f / cheriot-sail ba93b28).**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| Special_TrapSysctl | 12 | fixed (verified 047761391) | mret drops to U-mode with mstatus.TW=0, then wfi at pc 0. Kudu executes wfi, as Ibex does. Sail (riscv_insts_base.sail:570) traps wfi in U-mode unconditionally, but the privileged spec only requires that when S-mode is implemented. README §1.2. |
| Special_Post_Priv | 13 | fixed (verified 047761391) | Same as Special_TrapSysctl: mret to U-mode, then wfi at pc 0. Sail traps (priv U->M); Kudu executes wfi and sleeps in U. E2E/cexsum_20261117/kudu_e2e_top.Special_Post_Priv_v2.txt. |

**G. Kudu's PCC holds decoded bounds only; loses raw B/T when E > 24 (divergence, accepted).**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| Special_State_Pcc | 15 | divergence | auipcc ca4, then csethigh ca5,ca4,a4 (0x2ce707db) builds an untagged cap with E=25, B=0x80, T=0x40, otype 4, addr 0x5f0c8080. Software can reach this: CSetHigh writes any metadata bits into an untagged cap. cspecialw mtcc,ca5, then sb x24,1(a0) (0x018500a3) traps illegal (RV32E) to MTCC, so the untagged cap becomes PCC and the next fetch takes IFERR. Kudu keeps PCC as base32/top33 (pcc_cap_t): B<<25 overflows, so base32=0 and rebuilding gives B=0, while Sail keeps raw B=0x80. The same pcc2fullcap path makes MEPCC on this trap, so cspecialr mepcc would show different raw bits (untagged only). E2E/cexsum_20261117/kudu_e2e_top.Special_State_Pcc_v2.txt. Decision: accepted as a Kudu divergence. The Pcc checks now compare only the tag of an untagged PCC (pcc_eq_noaddr), and the Mepc checks compare only the address of an untagged MEPCC with E>24 (xepc_eq); see README §1.1. Recheck 047759432 (900 s per property): no CEX; bounds reached Special_State_Pcc 15, Special_Post_Pcc 13, CSR_Post_Mepc 12, Special_State_Mepc 13. |

Options for G: (1) accept it as a documented Kudu divergence limited to untagged caps with E > 24, and compare only the tag and address of an untagged PCC (it always faults on the next fetch); (2) report it as a Kudu RTL issue (pcc_cap_t cannot represent an untagged E > 24 cap); (3) constrain it in the harness (assume CSetHigh never produces E > 24).

**Consequences of A and D**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| g_cmt[0].Cmt_Wr | 10 | fixed (verified 047760210) | The main run found it only as incidental traces of CSR_Post_Mshwm (10 cycles, cause D) and CSR_Post_Mshwmb (11 cycles, cause A): a later csrrs reads the diverged CSR, so the GPR write differs as well. The debug rerun (B+Ht, 40 min) found no CEX up to 7 cycles. The 10-cycle trace is fixed by D; the 11-cycle trace remains until A is fixed in Sail. |
| Reg_Cont0_Rs1 | 12 | fixed (verified 047760210) | The main run found it only as an incidental trace of CSR_Post_Mscratch (cause A): Sail's csrrw x24,mscratch writes mscratch, a later csrrs reads it into a GPR, and the next instruction's forwarded rs1 differs. The debug rerun (40 min) found no CEX up to 7 cycles. Clears when A is fixed. |

**C (cont.)**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| Special_State_Priv | 18 | fixed (spec deviation) | csrrw s0,mstatus,a0 writes 0x34000800, so MPP=0b01 (S, unsupported). Kudu legalises it to M; the old spec used U. The following mret therefore leaves Kudu in M and Sail in U, caught at the next special instruction. Fixed by the MPP deviation (sail-riscv 9d7bd77). The debug job ran on the old spec. E2E/cexsum_20261117/kudu_e2e_top.Special_State_Priv_v2.txt. Recheck 047759282 (new spec): no CEX up to depth 20. |

### 1.2 Untriaged

None. All 24 CEXs of run 047757291 have a root cause.

### 1.3 Rerun 047759965 with the cause A fix (E2E/jg_20261118_002629, cheriot-sail dd34eaa)

Result: 21 CEX, 71 undetermined. Gone: all CSR_Post_*, Special_State_{Mcause,Mie,Mstatus,Pcc,Priv},
Cmt_Wr, Reg_Cont0_Rs1. Still failing: Special_Post_{Mcause,Mie,Mscratch,Mshwm,Mshwmb,Mtval,Mstatus},
Special_Post_Priv and Special_TrapSysctl (cause F). New, short CEXs: g_cmt[0/1].Cmt_Trap (6),
Mem_NoShadowReq (6), Special_Post_Mepc (7), and Exc_FlushPC, Exc_HandlerPC, Special_Post_{Mscratchc,Mtdc,Mtvec,Pcc},
Spec_NoIntErr0 (9), Special_TrapIrq (16).

| Property | Cycles | Status | Finding |
|---|---|---|---|
| g_cmt[0].Cmt_Trap | 6 | fixed (verified 047760210) | Regression from dd34eaa. Instruction 0x8046 = c.mv x0,x17 (C_MV_HINT). Sail's rv32e_illegal flagged it illegal, but Kudu's compressed_decoder.sv zeroes rs2 of c.mv/c.add when rd=x0, and rd of c.addi/c.slli when the immediate is 0, so these hints never use x16-x31 and never trap. Fix: removed the C_ADDI/C_MV/C_ADD/C_SLLI_HINT cases (cheriot-sail 3e3a02c). Debug: E2E/dbg_a1_20261118_033011. The other new short CEXs are presumed to have the same cause (debug jobs stopped before they finished); recheck run E2E/jg_20261118_033518. |

### 1.4 Rerun 047760210 with the hint fix (E2E/jg_20261118_033518, cheriot-sail 3e3a02c)

Result: 4 CEX, 88 undetermined (3 h). Special_TrapIrq, Spec_NoIntErr0 and Exc_HandlerPC share one
16-cycle trace (cause H below); Special_TrapSysctl (12) is cause F (U-mode wfi, README §1.2).
Every other CEX of 047757291 and 047759965 is gone, which verifies causes A-E and the hint fix
(rows marked "verified 047760210"). Special_Post_Priv (cause F) was not found within 3 h. The
res.txt length column is JG's min_length (proven CEX-free bound), not the trace length.
Next: rerun 047760531 (E2E/jg_20261118_045115) with the cause H fix.

**H. Sail ignores M-level interrupts in U-mode when mstatus.MIE = 0 (Sail bug, fixed in sail-riscv 67633f5 / cheriot-sail 1663dfc).**

| Property | Cycles | Status | Finding |
|---|---|---|---|
| Special_TrapIrq | 16 | fixed (verified 047760531) | csrrsi t1,mie,8 (mie.MSIE=1), then mret to U-mode with MPIE=0, so mstatus.MIE=0 in U. irq_software_i rises (mip.MSIP=1) and Kudu takes the interrupt in U-mode (special_case IRQ, csr_save_cause). That is correct: the privileged spec (§3.1.6.1) says interrupts for a higher privilege level are always globally enabled regardless of its xIE bit, and Ibex behaves the same. Sail's dispatchInterrupt (sail-riscv model/riscv_sys_control.sail:267) uses the M-only branch for any system without S and N, so for CHERIoT (U=1, S=0, N=0) it returns no interrupt whenever mstatus.MIE=0, even in U. Upstream also runs assert(priv == Machine) there, so upstream Sail would abort on any U-mode step; in the SV build sail_assert is a no-op. Our port b0589c3 only dropped the unreachable getPendingSet branch; behaviour is the same as upstream. Debug: E2E/dbg_irq_20261118_043213 (job 047760283). Fix (user-approved): enable M interrupts when priv != Machine or mstatus.MIE=1, and drop the assert (sail-riscv 67633f5, cheriot-sail 1663dfc; README §1.1). To be verified by the next e2e rerun. |
| Spec_NoIntErr0 | 16 | fixed (verified 047760531) | Same trace. In MAIN_IRQ mode Sail's dispatchInterrupt returns None, so main returns MAINRES_NOIRQ, which spec_api.sv counts as int_err. |
| Exc_HandlerPC | 16 | fixed (verified 047760531) | Same trace. Sail does not trap, so its post-PC is the interrupted PC, while Kudu's special_pc_q is the mtvec handler. |

### 1.5 Rerun 047760531 with the cause H fix (E2E/jg_20261118_045115, sail-riscv 67633f5, cheriot-sail 1663dfc)

Result: 4 CEX, 88 undetermined (3 h). Cause H is gone (Special_TrapIrq, Spec_NoIntErr0,
Exc_HandlerPC). All four remaining CEXs are cause F (U-mode wfi, README §1.2), which is
documented but not fixed in Sail:

| Property | Cycles | Status | Finding |
|---|---|---|---|
| Special_TrapSysctl | 12 | fixed (verified 047761391) | Cause F, as in 047757291. Found at 22 s. |
| Special_Post_Priv | 13 | fixed (verified 047761391) | Cause F, as in 047757291. Found at 46 s. |
| Special_Post_Mstatus | 13 | fixed (verified 047761391) | Incidental trace of Special_Post_Priv: Sail's spurious wfi trap also updates mstatus (MPP/MPIE). |
| Special_Post_Mcause | 13 | fixed (verified 047761391) | Incidental trace of Special_Post_Priv: Sail's spurious wfi trap writes mcause 2. |

No real Kudu divergence remains at this depth; the remaining CEXs clear when cause F is fixed in Sail.

Cause F fixed afterwards (user-approved): a U-mode WFI traps only when mstatus.TW=1, matching Kudu
issuer.sv ir0_mode_err (sail-riscv 74efd9f, cheriot-sail ba93b28). Recheck: rerun 047761391
(E2E/jg_20261118_133340).

### 1.6 Stage 1 closure runs (sail-riscv 74efd9f, cheriot-sail ba93b28, 2026-11-18)

All five jobs use the same spec build and the permanent restrictions of README §4.4. E2E is
$T/kudu_e2e.

| Job | Directory | Engines, depth, time | Result |
|---|---|---|---|
| 047761513 | E2E/s1cov_20261118_135458 | covers only | all 30 Cov_* covered in about 1 min (Cov_Store/Cov_StoreCap at 8, Cov_Irq at 16, slot-1 commits for every class) |
| 047761391 | E2E/jg_20261118_133340 | B Ht, 20, 3 h | 0 CEX, 92 undetermined. Cause F verified gone (it used to fire at 22 s / 46 s). |
| 047761525 | E2E/s1bnd_20261118_135458 | B4 K, 20, 3 h | 0 CEX; Harness_LsqOnePush and Harness_SbdWrStep1 proven (unbounded); 90 undetermined |
| 047761539 | E2E/s1zw_20261118_135933 | B Ht, 20, 3 h, +define+E2E_ZERO_WAIT | 0 CEX, 92 undetermined |
| 047761523 | E2E/s1hunt_20261118_135458 | L Ht, 40, 6 h | 0 CEX; engine L restarted once and stalled after trace step 7 (bounds 8-9 only) |

Cex-free bound per property (max over the B/Ht, B4/K and L/Ht runs in the default
environment; 999 = proven). Full table: E2E/stage1_bounds.txt (one row per property, one column per job).

| Bound | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 20 | 21 | proven |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Default env (properties) | 0 | 7 | 7 | 13 | 18 | 11 | 3 | 7 | 4 | 2 | 1 | 3 | 1 | 13 | 2 |
| Zero-wait env (properties) | 3 | 6 | 11 | 14 | 17 | 7 | 4 | 7 | 1 | 3 | 2 | 3 | 0 | 14 | 0 |

Minimum 8 (default) and 7 (zero-wait); median 12 and 11. The shallowest properties are the
operand/continuity and commit checks: Reg_Cont{0,1}_Rs{1,2}, g_cmt[*].Cmt_Wr and Mem_Addr (8);
PC_Cont0, g_cmt[*].Cmt_Trap, Cmt_NoWr and Mem_NoShadowReq (9). B4/K gave the deeper bound on 24
properties and B/Ht on 37.

Stage 1 verdict (README §5): (a) met; (b) met, with no CEX at the bounds above; (c) met in the sense
that no CEX was found, but the L hunt did not get past bound 9, so it adds nothing beyond (b).
No Kudu RTL bug was found in stage 1. Every CEX was a Sail or harness issue (causes A-H) and is
fixed or documented. Deeper guarantees are left to the stage 2 induction.

## 2. Resolved in earlier e2e runs

| Property | Run | Status | Finding / fix |
|---|---|---|---|
| Spec_NoIntErr0/1 (MAINRES_IFERR_1, spec_mtcc_unrecoverable) | 047755997 | fixed | regcap2sail passed cE=0, so Sail decoded the root PCC/MTCC with T[8]=0. Fix: set s.T = c.top9 in fv2/spec/cheri.sv. Debug: E2E/dbg_ierr_20261116_183702. Confirmed gone in 047756793. |
| Mem_IsCap (and the Mem_* family) | 047756793 | fixed | c.lwsp was flagged as a capability load because upstream checked_mem_read calls __ReadRAM_Meta on every load. Fix: mem_read_cap_o requires width 8 (fv2/spec/spec_api.sv). Debug: E2E/dbg_cex_20261116_224543. Confirmed gone in 047757291. |
| Special_TrapExec | 047756793 | fixed (spec deviation) | sfence.vma: Kudu traps it as illegal, upstream Sail treats it as a NOP in M-mode. Removed from the spec (sail-riscv 4520628, cheriot-sail 84ab893); README §1.1. Confirmed gone in 047757291. |

## 3. Clean fcov runs (CLEAN/p0, CLEAN/p1; jobs 047755452 / 047755456)

Both stopped at the 15 h job limit (2026-11-17 03:31) before finishing:

- p0: 739 proven, 282 undetermined, 4 CEX; stopped in pass 6.
- p1: 742 proven, 237 undetermined, 4 CEX; stopped in pass 8.

Results are in CLEAN/p0/res.txt and CLEAN/p1/res.txt. The CEXs are the same in both modes.

| Property | Cycles | Status | Note |
|---|---|---|---|
| ls_pipeline_i.u_fcov_sva_lsu.AssertEarlyLoadSplitInRegion | 7 | waived | INT-3, sim/testplan/integration_issues.md; waiver in fv/fv_kudu_fcov.tcl:22. Defined at sim/fcov/kudu_fcov_lsu.sv:1485. |
| u_fvh_front_pc.AssertHelpFpcRdStable | 16 | untriaged | FV helper (sim/fcov/kudu_fcov_if.sv:1638). A false helper must not be used as a lemma. |
| u_fvh_issue_fwd.HlpJWl4 | 8 | untriaged | FV helper (sim/fcov/kudu_fcov_issue.sv:2319). |
| u_fvh_issue_fwd.HlpWrsvConv | 8 | untriaged | FV helper (sim/fcov/kudu_fcov_issue.sv:2317). |

## 4. Stage 2 induction step counterexamples (well-formedness round, 2026-11-21)

Runs are under /home/scratch/fortress/kunyanliu/e2e_tools/kudu_e2e. No RTL bug was found in this
round: every counterexample was a missing invariant, an over-strict invariant or a missing
environment assumption.

| Property | Run | Cause | Fix |
|---|---|---|---|
| B_RegWF, A_RfWF (all indices) | s2ind40 | Spec: jal/jalr at PC 0xfffffffe writes a malformed link cap (Sail's representability assert is a no-op in the SV build). | Assumption Env_NoPcWrap (top.sv). |
| B_RegWF, A_RfWF | s2ind40 | Kudu: a WB result reaches the RF after a WAW cancel cleared its forward-valid. | Inv_A_AluWbWF0/1, Inv_A_MulWbWF, Inv_A_LsFifoWF. |
| A_LsFifoWF | s2bmc26 | A faulting (err) entry holds raw bus data; the committer blocks its write. | Antecedent ent.we && !ent.err. |
| A_LsFifoWF | s2ind45 | f_req_eq ignored rf_we/rd (store with rf_we); shadow load had unconstrained tagged data. | f_req_eq compares rf_we/rd; f_kreq_we_ok; assumption Mem_RdataCapWFAny (checks.sv). |
| A_AluWbWF0/1, A_MulWbWF | s2ind49, s2ind50 | JAL/AUIPCC in the trap shadow used Kudu's unconstrained PCC; the bad values went to x0, which the RF discards. | Antecedent waddr != 0; Inv_A_KPccWF. |
| A_MulWbWF | s2ind49 | CJALR result in mult EX2 unconstrained. | Inv_A_MulEx2WF (rd != 0). |
| A_CsrWF | s2ind49 | SCR write from a malformed cs1_fcap in the LSU request. | Inv_A_LsuCs1WF; f_kreq_we_ok requires inv_cap_ok of a CSR request's cs1_fcap. |
| A_KPccWF | s2ind50, s2ind53, s2ind56 | Over-strict or wrong invariant: covered the IR-stage predicted PCC; required E in {0..14, 24} (spec allows E <= 24); 5-bit exp + 9 wrapped at E = 23. | EX1 PCC only; E <= 24, perms == expand_perms(cperms), inv_cap_ok(pcc2sail), 6-bit length bound. |
| A_MulEx2WF | s2ind53 | CJALR link inherited a shadow PCC with non-canonical cperms. | Covered by the stronger Inv_A_KPccWF. |
| B_CsrWF, Special_Post_Mepc, CSR_Post_Mepc, E_Cur_mepc | s2fin1/s2fin2 round 4 (20261121_040039) | Spec hole, reachable: an interrupt taken while PC is outside the PCC's representable range (a JAL/branch target is not bounds-checked; only fetch is, and Sail dispatches interrupts before fetch). handle_trap_extension does MEPCC = setCapAddr(PCC, pc) and only asserts representable or untagged, which holds after a fetch bounds fault (PCC tag cleared) but not for an interrupt. The SV spec ignores the assert and keeps the tag; Kudu's pcc2regcap uses set_address and clears it. | Spec fix cheriot-sail 5ca398e: clearTagIf(not(representable)) in handle_trap_extension (matches Kudu and the assert's intent). s2ind60: B_CsrWF, Special_Post_Mepc, CSR_Post_Mepc and E_Cur_mepc all pass the step. |
| E_Cur_mstatus | s2fin0 round 4 (20261121_040039) | Unreachable start state: committer cmt_err_q = 1 with cmt_err_info_q.has_pcc = 0 (only reset leaves has_pcc = 0; every load sets has_pcc = 1, clrtag = 0). With has_pcc = 0 the CSRs take mpie from mstatus.mie instead of the mie captured at issue. | New Inv_E_CmtErrPcc (cmt_err_q -> has_pcc && !clrtag). s2ind61: passes step (with Inv_G_IrFErr, Inv_G_IrPccQ, Inv_E_CmtErrPcc, all of which pass step too). |
| E_Cur_mtval | s2fin0 round 4 | Unreachable start state: ir0's latched fetch checks (bound_vio, cause 1) came from a stale tagged, sealed ir_pcc_cap_q, while the EX1 PCC and the spec PCC are untagged (spec reports tag violation, cause 2). Nothing linked the IR-stage PCC (PredictRA) or ir0/ir1 errs to the architectural PCC. | New Inv_G_IrFErr (ir0/ir1 perm/bound/asr_vio re-decoded against the PCC each issues under: EX1 PCC, or for ir1 behind a predicted CJALR its unsealed ptarget) and Inv_G_IrPccQ (ir_pcc_cap_q is the PCC the next decoded instruction issues under). s2ind61: passes step (with Inv_G_IrFErr, Inv_G_IrPccQ, Inv_E_CmtErrPcc, all of which pass step too). |
| E_Cur_mcause | s2fin1 round 4 | Spec hole, reachable: fast interrupt 27 and MEI both pending and enabled. Kudu (as cheriot-ibex) takes the lowest fast interrupt first; upstream Sail never dispatches fast interrupts, so it took MEI. With only fast interrupts pending the spec takes none. | Spec fix sail-riscv fba1588 / cheriot-sail 5adb53a: fast-interrupt dispatch ported from cheriot-ibex's sail-riscv fork. s2ind61: passes step (with Inv_G_IrFErr, Inv_G_IrPccQ, Inv_E_CmtErrPcc, all of which pass step too). |
| Spec_NoIntErr0 | s2fin1 round 4 | Unreachable start state: MTCC (mtvec) address 0x113ffb2 has bits [1:0] = 2. A C.CSCSP through a sealed sp traps, and the spec's prepare_trap_vector calls internal_error on any non-direct tvec mode (sail_reached_unreachable). Kudu's legalize_scr (cheri_pkg.sv:1073), boot init and the spec's CSpecialRW all clear bits [1:0], and both reset values are aligned. | Added Inv_B_MtvecAlign (past_mtvec) and Inv_A_MtvecAlign (dut_mtvec). s2ind61: Spec_NoIntErr0/1 still cex (MtvecAlign was not yet in that run's list); rechecked in s2ind62. |
| A_KPccWF | s2bmc29 (BMC from reset, depth 1) | Stale inv.sv with the 5-bit wrap: the reset PCC (E = 24, top 2^32) failed the length bound. | Same 6-bit fix; s2bmc30 with the final inv.sv has no cex to depth 12. |

Step-check status after the fixes: all of the above pass (undetermined at length 4);
F_LsqReq[3] and five A_FwdWF slots are proven outright. B_RegWF[1] and A_RfWF[1] pass with a
60-minute limit (s2ind48). All other indices pass too: A_RfWF[2-16] (s2ind58) and
A_RfWF/B_RegWF[17-31] (s2ind55) take about 75 s each; B_RegWF[2-10] (s2ind54) and
B_RegWF[11-16] (s2ind59) take 1-17 minutes each.

### 4.1 Round 5 status (s2ind61, s2ind62)

s2ind61 (20261121_170737) ran with submit -t 900 (seconds), which killed shards 0 and 3 before
they finished, so Mem_CsrGo and a few other Mem_* checks returned no result.

- Pass step: Inv_G_IrFErr[0,1], Inv_G_IrPccQ, Inv_E_CmtErrPcc, E_Cur_mcause/mtval/mstatus,
  Special_Post_Mtval/Mstatus/Mcause, Special_TrapSysctl/TrapExec/TrapIrq, Exc_HandlerPC.
- Step cex: Spec_NoIntErr0/1, Reg_Cont0/1_Rs1/Rs2, Special_State_Mshwm, Special_Post_Mshwm,
  Exc_FlushPC, Cmt_Wr/Cmt_Trap/Cmt_NoWr (both slots), Mem_GoTrap, Mem_Kind, Mem_TrapRead,
  Mem_IsCap, Mem_GoSplit.

Reg_Cont0_Rs1 cex: past_regs[3] matched neither a pending writer nor the register file. Nothing
linked the spec's register file to Kudu's RF, scoreboard and pipeline results. New group H
invariants in check/inv.sv:

- Inv_H_RegPend / Inv_H_RegRf: past_regs[i] equals the youngest pending writer's spec result,
  or, with no pending writer, Kudu's rf_reg[i].
- Inv_H_Wrsv: a pending writer of x_i implies reg_wrsv_q[i] (outside special-issue FSM states).
- Inv_H_IssueRd0/1: Kudu's rf_we/rd at a normal issue matches the spec's destination.
- Inv_H_AluCnt/Ent/Data/Fwd (per ALU), Inv_H_MulCnt/Ent/Data/Fwd: pipeline stages match their
  scoreboard entries (rd, we, data, forward-valid only for the youngest writer).
- Inv_H_LsWaw / Inv_H_LsWbData: waw_fifo and wb_fifo slots match LS entries by age rank.

s2ind62 (20261121_173315, jobs 047771694/96/700/702, -t 7200) checks group H, MtvecAlign and the
remaining step cex properties.

### 4.2 s2ind62 results and fixes (2026-11-21, s2ind63 launched 18:03)
s2ind62: proven Inv_A/B_MtvecAlign. Step passes (undetermined 4): H AluCnt/AluFwd/AluEnt 0/1, MulCnt, MulFwd,
MulEnt, IssueRd0/1, RegPend, LsWaw, Spec_NoIntErr1, Reg_Cont0/1_Rs1/Rs2. Step cex and cause:
- Inv_H_LsWbData, g_cmt[0].Cmt_NoWr: LSU in-flight rd not linked to spec rd. Added Inv_H_LsCurEnt, Inv_H_LsqEnt
  (LSU current / LSQ entry linked to scoreboard entry by LS rank: pc, wx, rd).
- Inv_H_AluData1: non-canonical cgp (T[8]) kept by AUICGP; covered by inv_cap_canon in RegWF / inv_rcap_ok.
- Inv_H_MulData: EX2 result unlinked. Added Inv_H_MulEx2Data (div excluded).
- Mem_GoTrap: lsu_if DLY1_WGNT presenting req_hold_q with stale lschk_err. Added Inv_F_HoldChk, Inv_F_HoldEarly.
- Special_State/Post_Mshwm: no mshwm invariants. Added group M (Inv_M_*), follower pre_mshwm field.
- Exc_FlushPC: SLEEP with cmt_err_q set and shadow_q (unreachable). Added Inv_C_SpSbdEmpty, Inv_C_SleepEmpty.
- g_cmt[0].Cmt_Trap: spec trap on a mult-pipe entry; Kudu ALU/mult err is tied 0. Added Inv_C_ErrLs.
- Inv_H_Wrsv, Inv_H_RegRf, Spec_NoIntErr0: fixed before s2ind63 (Inv_H_SpNoPw, Inv_C_ErrAllSh, spec_api int_err_o).
Open: Kudu mshwm checks only the first address of a misaligned store; a bus-error store in range may differ.
s2ind63: shards 0-2 re-check the above; shard 3 re-proves WF invariants (RegWF/RfWF sampled at 1 and 17).

### 4.3 s2ind63 results and fixes (2026-11-21, s2ind64 launched 19:12)

Proven: most Inv_M_* (DutAlign, PstAlign, LsqTKeep, LsqShPast, LsqChain, LsqPost), FwdWF. Step passes:
Inv_C_ErrAllSh, Inv_C_ErrLs, Mem_GoTrap, Cmt_NoWr, Inv_A_CsrWF and others. Timeouts at 15m: AluData0/1,
MulEx2Data (re-run at 40m in s2ind643). Counterexamples and fixes:

| Check | Cause | Fix |
|---|---|---|
| Cmt_Trap | LS entries had no trap/shadow link to the follower | inv_lsk_ok checks shadow and trap; new Inv_H_LsWbErr (wb_fifo err == spec trap) |
| Inv_H_MulData | WB held a divide result; the iterative divider has no invariants | Ibex precedent (M-types inconclusive there): div excluded from MulData and Cmt_Wr data; separate Cmt_DivData (expected inconclusive, a documented hole) |
| Inv_A_LsFifoWF, Inv_H_LsWbData | non-canonical untagged MTDC/MScratchC read through the LSU | inv_cap_canon added to B_PccWF, B_CsrWF, A_CsrWF, A_LsuCs1WF |
| Spec_NoIntErr0 | tagged non-executable PCC: Sail fetch check raises internal_error | Inv_B_PccX / Inv_A_PccX: tagged PCC, MTCC, MEPCC are unsealed and executable (Sail SCR writes clear the tag otherwise) |
| Exc_FlushPC | spec PC in the trap shadow not tied to MTCC | Inv_F_ShPc: shadow -> past_pc == past_mtvec.address |
| Cmt_Wr[0], Cmt_Wr[1] | spec runs a load at issue on free read data; nothing tied the stored rd_*_data and Kudu's byte offset to the spec result (int load got byte 1, Kudu byte 3; cap load perms differed) | inv_lsk_ok: spec wX == Kudu formatting of the stored read (inv_lfmt: offset/size/sign from kreq; inv_lcap: mem2regcap with kreq.clrperm); Inv_H_LsuOff (rdata_offset_q), Inv_H_LsuRdq (rdata_q in a split load's second part) |

### 4.4 s2ind64 results and fixes (2026-11-21, s2ind65 launched 19:42)

Step passes: Inv_A_PccX, Inv_B_PccX, Inv_F_ShPc, Inv_A_LsFifoWF (all), Inv_C_ErrLs (all), Inv_C_SpSbdEmpty,
Inv_C_SleepEmpty, Inv_B_CsrWF, Inv_H_MulData, Inv_H_LsCurEnt, Inv_H_LsqEnt, Inv_H_LsuRdq, Inv_H_LsWbErr,
Spec_NoIntErr0/1, Exc_FlushPC, Cmt_Trap, Cmt_NoWr, Inv_F_ShPcc, Inv_F_Pcc, Inv_E_CmtErrInfo.
Cmt_DivData: cex as expected (documented hole). Counterexamples and fixes:

| Check | Cause | Fix |
|---|---|---|
| Inv_B_PccWF | spec harness clears nextPCC.B[8] when E = 24 (cheriot-ibex issue #11), so PCC after a trap to a canonical MTCC is not canonical | canon or E == 24 |
| Inv_A_CsrWF | Kudu MEPCC non-canonical under divergence G (untagged PCC with E > 24 at a trap) | MEPCC canon dropped from A_CsrWF; new Inv_E_MepcCanon (canon, or the divergence G case) |
| Inv_A_LsuCs1WF | CSR request moved from lsu_if req_dly_q (no canon) into the LSU | f_cs1_ok; Inv_F_LsqCs1WF, Inv_F_HoldCs1WF, Inv_F_DlyCs1WF |
| Inv_H_LsuOff, Cmt_Wr[0] | in WAIT_GNT(_MIS) the LSU uses lsu_if's req_hold_q, which differed from lsu_req_info_q | Inv_D_LsuHold: LSU busy -> lsif in DLY0/DLY1_WGNT and req_hold_q == lsu_req_info_q |
| Inv_H_LsWbData | CSR (CSpecialRW MScratchC) result: no link between the spec wX of a CSR entry and its pre-state | f_csr_rd_ok in inv_lsk_ok (old SCR / CSR value from the entry's pre-state, MIE from kreq.mie); Inv_E_Chk1Cur (lsq_cur_q == csr_ent1_q at csr_go_q) |
| Mem_Addr | no link between Kudu's request address and the spec's memory address in LSQ entries | Inv_F_LsqAddr, Inv_F_CurAddr (kreq.addr word == spec first word, second word = next) |
| Cmt_Wr[1] | lsu_req_info_q.clrperm differed from lsq_cur_q.kreq.clrperm (cap load perms) | f_req_eq also compares clrperm and sign_ext |

Risk: a CSpecialRW read of MEPCC under divergence G returns Kudu's decoded bounds (LsWbData/Cmt_Wr may cex).
s2ind65: three shards over the new and changed props (15m each); s2ind643 (40m AluData/MulEx2Data) still running.

### 4.5 s2ind65 results and fixes (s2ind66 launched 20:03)

Step passes: Inv_D_LsuHold, Inv_E_Chk1Cur, Inv_F_LsqCs1WF/HoldCs1WF/DlyCs1WF, Inv_F_LsqAddr, Inv_F_CurAddr,
Inv_F_LsifHd/LsifNx/LsuCur/Chk1Req, Inv_B_PccWF, Inv_A_CsrWF, Inv_A_LsuCs1WF, Inv_H_LsuRdq, Mem_Addr.
s2ind643: Inv_H_AluData0 timed out again at 40m.

| Check | Cause | Fix |
|---|---|---|
| Inv_E_MepcCanon | e_st_eq linked spec states with the relaxed xepc_eq, so a pending CSR entry's MEPCC could be any untagged value with the same address, and applying it moved that value into e_cur | e_st_eq compares MEPCC with cap_eq (both sides are spec states) |
| Inv_H_LsWbData, Inv_H_LsuOff, Cmt_Wr[0/1] | LSQ / LSU requests carrying a nonzero amo_flag (LR/SC/AMO), so the load-data link was skipped or the LSU offset/data path differed | f_kreq_we_ok: amo_flag == 0 (A out of scope, cmplx_unit idle); AMO exemption dropped from inv_lsk_ok |
| Inv_H_LsCurEnt, Inv_H_LsqEnt | CSpecialRW read of MEPCC: the spec's wC result is encodeDecodePermsOf(MEPCC) (otype re-derived from permit_execute) | f_csr_rd_ok compares SCR reads with encodeDecodePermsOf(pre SCR) |

### 4.6 s2ind66 results and fixes (launched s2ind67, 20:35)

| Prop | s2ind66 | Cause | Fix |
|---|---|---|---|
| MepcCanon, LsCurEnt, LsqEnt, LsqReq, CurReq, LsqChain/Id/Post | pass (step) | - | - |
| CurPre, HeadPre, Chk1Pre | cex | Inv_E_Eq_mepc used xepc_eq between two spec states | KE_CHKF Inv_E_Eq_* uses cap_eq; Inv_E_Cur_* keeps EQ |
| LsuOff | cex | request with lschk_err.any_fault takes ls_go without ctrl_update; rdata_offset_q stale (no data returned) | antecedent excludes lschk_err.any_fault |
| LsWbData, Cmt_Wr[0/1] | cex | f_addr_ok compared only [31:2]; induction state had unaligned spec rd_fst_addr and rd_snd disagreeing with Kudu split | f_addr_ok: Sail passes the aligned word to read_ram/write_ram, so fst[1:0]==0, snd == fst+4, and snd == Kudu split_misaligned_access for non-cap |

### 4.7 s2ind67 results and fixes (launched s2ind68, 2026-11-22 17:28)

| Prop | s2ind67 | Cause | Fix |
|---|---|---|---|
| CurPre, HeadPre, Chk1Pre, Eq_mepc, Cur_mepc, MepcCanon, LsqReq/CurReq/LsqAddr/CurAddr, LsCurEnt, LsqEnt, LsuRdq, Mem_Addr | pass (step; LsqAddr[3], LsqReq[3] proven) | - | - |
| LsuOff | cex | non-split request in WAIT_GNT (or WAIT_GNT_MIS) before its grant: rdata_offset_q loads only on the grant | antecedent excludes WAIT_GNT_MIS and WAIT_GNT with !handle_misaligned_q |
| LsWbData, Cmt_Wr[1] | cex | real divergence G: CSpecialRW read of an untagged E>24 MEPCC returns Kudu's decoded bounds (insn 0x03f4035b, 0x03f6045b) | user decision: harness assumption Env_NoDivGRd0/1 (spec_instance.sv); f_csr_rd_ok MEPCC case adds !f_divg(pre.mepc); README §4 |
| Cmt_Wr[0] | cex | unreachable: split word load in WAIT_GNT with handle_misaligned_q = 0 (only first word fetched) | new Inv_H_LsuMis (FSM phase vs handle_misaligned_q and split) |

### 4.8 Round-5 full check (s2fin5*_20261122_175524) triage, fixes for s2ind69
Full check: every property assumed 2 cycles, proven at depth 3 (shallower than s2ind).
- Mem_* (Addr, Kind, GoSplit, TrapRead, CsrGo, IsCap, StoreBe, StoreData, CapStore{Tag,Addr,Cap}):
  LSQ entry request fields and spec rd/wr were not tied to the entry's instruction word (e.g. a
  CSpecialRW 0x03c8005b at the LSQ head with csr = 0, is_load = 1, issued as a byte load). Added
  f_is_csr / f_kreq_dec_ok (ls_pipeline request decode) and f_rw_ok (spec read/write iff non-CSR
  load/store): Inv_F_LsqDec, Inv_F_LsqRw, Inv_F_CurDec, Inv_F_CurRw.
- Inv_A_LsFifoWF[0..3]: CSpecialRW read of a divergence-G MEPCC (spec E = 28, untagged) already at
  csr_chk1_q. Env_NoDivGRd0/1 restrict it at issue only. Added f_nodivg_ok and Inv_F_LsqNoDivG,
  Inv_F_CurNoDivG, Inv_F_Chk1NoDivG.
- Inv_E_MepcCanon, Inv_B_CsrWF, Inv_E_Cur_mepc, Special_Post_Mepc: trap from an untagged PCC with
  E <= 24 whose Kudu bounds differ from the spec's. Inv_F_Pcc compared untagged PCCs on tag only.
  New f_pcc_eq_k: tag-only only for divergence G (untagged, spec E > 24), else cap_eq_noaddr.
- Inv_E_Cur_mstatus, Special_Post_Mstatus: trap-source entry (lsq_cur_q.trap) with post mstatus
  MIE = 1, MPP unchanged; e_app_flush then loads it. Added e_trap_mst (MIE = 0, priv = M,
  MPP = pre priv): Inv_E_LsqTMst, Inv_E_CurTMst.
- Reg_Cont{0,1}_Rs{1,2}: operand forwarded from a divide result in mult WB (wb_reg.flags.is_div).
  Same root as the Cmt_DivData hole (div data not covered by Inv_H_MulData/MulEx2Data). Open.
- Cmt_DivData[0/1]: known hole. Special_Post_Mshwm: known deviation.

### 4.9 s2ind69 triage (2026-11-23), fixes for s2ind70

s2ind69 confirmed the 4.8 fixes (decode, NoDivG, TMst, MEPCC/mstatus, CsrWF). Remaining cex:

- **Inv_F_Pcc**: after a trap flush from an untagged MTCC with E <= 24, the spec PCC was
  unconstrained because Inv_F_ShPcc tied only tag and ASR for any untagged MTCC.
  Fix: Inv_F_ShPcc relaxes only the divergence-G case (untagged, E > 24).
- **Inv_A_LsFifoWF[0..3]**: a CSpecialRW x0 read of a divergence-G MEPCC (0x03f2005b) left an
  ill-formed value in the LS write-back FIFO. The value is discarded; the invariant now
  excludes waddr 0, like the ALU and mult write-back WF invariants.
- **Mem_CsrGo**: a trapping CSR entry carried spec rd = 1; rd/wr are meaningless for a
  trapping entry. The check now excludes trap entries.
- **Mem_TrapRead**: a store entry had kreq.early_load = 1, which lets a trapping store reach the bus.
  ls_pipeline sets early_load on every CSR request and on loads only, so f_kreq_dec_ok now requires that.
  No RTL issue.
- **Mem_StoreData/StoreBe/IsCap/CapStoreAddr/CapStoreTag/CapStoreCap**: f_req_eq omits wdata,
  so the RTL queue's store data was free; nothing tied spec rd_cap/wr_cap, byte enables
  or store data to the Kudu request. New: f_wd_eq (Inv_F_LsifHdWd, LsifNxWd, LsuCurWd;
  tag cleared on SLC where lsu_if clears it) and f_wr_ok (Inv_F_LsqWr per entry and
  Inv_F_CurWr): cap flags, be = size mask << offset, data = wdata rotated by offset,
  cap store address word, tag and decoded capability.
- **Inv_M_Cur** (round 5): in the shadow of a trap that has already responded, m_cur
  was not tied to past_mshwm. New Inv_M_ShPast (mshwm analogue of Inv_E_ShKeep).

### 4.10 s2ind70 triage (2026-11-23), fixes for s2ind71

s2ind70: 40/45 pass the step (LsFifoWF[0..3], LsqWr/CurWr, Wd links, ShPcc, most Mem_*). Remaining cex:

- **Mem_CapStoreAddr/Tag/Cap**: the entry was a capability load. The checks tested wr_cap without wr,
  and wr_cap is meaningless for a load. They now require lsq_req_ent.wr.
- **Mem_TrapRead**: lsu_if's hold register had early_load = 1 for a trapping CSC, while the LSQ copy had 0;
  f_req_eq did not compare early_load. Added.
- **Inv_F_Pcc**: the MTCC was untagged with E = 26 (divergence G), which Inv_F_ShPcc (4.9) left free.
  Sail prepare_trap_vector sets nextPCC = MTCC unchanged; the harness main_inner patch only
  clears B[8] at E = 24. So Inv_F_ShPcc now requires spec PCC == normalised MTCC unconditionally;
  Inv_F_Pcc relaxes Kudu's comparison for untagged E > 24 as before.

### 4.11 Round-6 timeout reruns and the MEPCC T[8] cex (2026-11-23)

Timeout reruns at 40 min per property, engines Hp/N/AM:
- s2tmo1 (9 props): step-pass for Mem_GoReq, Mem_GoTrap, regwf[1], LsqTrap[0], LsqCause[0],
  CurCause; AluData0 and MulEx2Data still time out; g_cmt[0].Cmt_Wr cex.
- s2tmo2 (18 props, built before the fix below): regwf[2..7] step-pass; g_cmt[1].Cmt_Wr cex (same
  cause); the rest pending.

- **Cmt_Wr (s2tmo1 [0], s2tmo2 [1])**: CSpecialR of an untagged MEPCC with E = 24. Kudu returns
  the stored T (e.g. B = 0x1ae, T = 0x09a); Sail's wC encodes and decodes the cap, recomputing
  T[8] = B[8] ^ (T[7:0] < B[7:0]) ^ 1 from a B[8] that the spec's main_inner hack
  (cheriot-ibex issue #11) cleared on the PCC before the trap copied it into MEPCC. Kudu's
  bounds equal those of unmodified Sail, so this is a spec artefact.
  Fix: f_mepc_lossy (spec_instance.sv) extends Env_NoDivGRd0/1 and the inv.sv f_nodivg_ok /
  f_csr_rd_ok MEPCC cases to that E = 24 case (README §4.4).
  s2ind73: the lossy-read invariants (Inv_F_*NoDivG, Inv_H_LsWbData/LsCurEnt/LsqEnt) step-pass;
  g_cmt[0].Cmt_Wr now times out at 40 min instead of failing.
- **Divide lemma** (s2ind74): Env_DivLemma plus Inv_H_DivFol/Busy/Wait/Done; the divide exclusions
  were removed from Inv_H_MulData/MulEx2Data (README §4.4).


### 4.12 Round 7 and the multiply lemma (2026-11-24)

- Round 7 (step-ordered, README §5.1) found 0 cex in 825 properties. L0 properties that timed out
  at 15 min were rerun at 40 min (retries A-D): RegWF[2..15], Mem_GoReq/GoTrap, LsqTrap/LsqCause,
  CurTrap and MulIss_C[5..6] pass.
- **MulIss_C[1-4]** (MUL/MULH/MULHSU/MULHU) still timed out at 40 min in every variant
  without the lemma:
  - the product lemma assumed (s2mulk1);
  - plus the multiplier product cut (s2mulk2);
  - plus a spec narrowed to a 66-bit multiply (s2mulnar).

  Cause: the RTL multiplies md_op_a/b, while Sail multiplies X(rs1)/X(rs2) read through its
  register-file mux. The solver must equate two different multipliers. Fix: Env_MulLemma
  (README §4.4), whose parts K and S are proven at block level (mullec2, mulpipe, mulnarrow).
  s2mull: all four step-pass in 63-80 s. s2bmc33 (base case, real multiplier): no cex to
  depth 8-11, and the lemma-fire and MULHSU/MULHU retire covers are reached at depth 7.
- Special_Post/State_Mshwm(b) and CSR_Post_Mshwm(b) step-pass in round 7 (group M). The
  "known deviation" in 4.8 and the misaligned-store note in 4.2 do not cause a mismatch under
  the proven properties.
