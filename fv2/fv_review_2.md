# fv2 end-to-end formal flow: gap review 2

Date: 2026-11-26. Follow-up to fv_review_1.md.

Scope:
- the fv2/ harness as changed by the review-1 actions (backup before the
  changes: /home/scratch/fortress/kunyanliu/fv2_bak_review1_20261125_224241);
- RTL commit 4472c7f (regfile x16-x31 without metadata);
- the round-7 and round-8 induction scripts (mkfinal8.py, queue8.sh) and
  run results in /home/scratch/fortress/kunyanliu/e2e_tools/kudu_e2e/.

This was a read-only review; nothing was changed. Job status is as of
2026-11-26 08:45.

## Summary

The review-1 fixes are correct in design. The simulation regression for the
regfile change is clean, and from-reset BMC finds no real bug in the new
checks. However, the round-8 induction step (L0) currently fails for 8
properties. Several of them read the register file, which suggests 4472c7f
broke the induction even though simulation passes. Stage 2 is therefore
**not** closed for the current RTL and harness until these are triaged.

| # | Severity | Gap |
|---|---|---|
| 1 | High | Round-8 L0 step: 8 cex, untriaged |
| 2 | Medium | Reset state never compared with the architecture |
| 3 | Medium | No direct check that trap-shadow entries write nothing |
| 4 | Medium | -bound 2 induction with multi-cycle properties unconfirmed |
| 5 | Medium | Wrong-path out-of-scope instructions still pruned |
| 6 | Low | B extension excluded though the spec already has it |
| 7 | Low | irq inputs to mip wiring unchecked |
| 8 | Low | Lint / cosmetic |

## Status of review-1 gaps

| Review-1 gap | Action taken | Status |
|---|---|---|
| 1 regfile change | committed as 4472c7f; full regression in regfile_regr_20261125_224125 | 317 sims: 310 PASS, 7 XFAIL (KUDU-042, KUDU-019, known), 0 FAIL. **Formal: see gap 1 below** |
| 3 scope via DUT decode | insn_in_scope returns 1 for compressed parcels (check/top.sv:204); Env_NoCmplx/NoBrkpt became asserts Scope_NoCmplx/Scope_NoBrkpt; new Scope_IsComp (top.sv:237-245) | Sound: Sail decodes the raw c_insn, and Fetch_Iss ties both widths to memory. Scope_NoBrkpt fails the L0 step (gap 1). Residual: gap 5 |
| 4 alas() | exact cap_eq unless E2E_REVOKE (spec/cheri.sv:148-161) | BMC clean. inv.sv uses alas at about 1671-1786; Inv_H_RegRf (inv.sv:1674) fails the L0 step (gap 1) |
| 7 outputs | Mem_CapStoreBits/Be, Out_NoAmoFlag, Bus_InstrReqHold/DataReqHold; Out_NoFatalErr hit a legal cex at 9 (Kudu flags any trap with an invalid MTCC) and was replaced by Out_FatalErr0/1 against the spec's mtcc_unrecoverable, with a near-top waiver (checks.sv:258-282) | fixbmc1/fixbmc2: no cex to depth 7-15; Cov_FatalErr hit at 14. Mem_CapStoreBits fails the L0 step (gap 1) |
| 8 no matching proof run | round 8 (r8l0s0, r8l0s1, r8l1, r8l2, r8base) via queue8.sh, max 2 JG | running since 01:02; L0 shards still going |

## High

### 1. Round-8 L0 step: 8 cex, untriaged

From r8l0s0_20261125_232003 and r8l0s1_20261125_232003. These are partial
results; the shards are still running.
- Both shards so far: 59 proven, 8 cex, and 733 undetermined, all at
  length >= 4 (which counts as a pass under the "done" rule).
- Every cex has length 3, so each is an induction-step failure, not a
  trace from reset.

| Property | Likely cause |
|---|---|
| Inv_A_IraRd0/1, Inv_A_IrbRd0/1 (inv.sv:311-314) | Registered read data == rf_reg[raddr]. These held in round 7, before 4472c7f; rf_reg_q[16..31] now stores only wdata[31:0] |
| Inv_H_RegRf (inv.sv:1674) | RF refinement vs past_regs; same suspect, or the stricter alas |
| Mem_CapStoreBits | new check, may need a helper (BMC is clean to depth 7-13) |
| Scope_NoBrkpt[0/1] | new assert (was an assume); needs a helper invariant on the IR / decode path |

The regfile hypothesis is not confirmed. One likely mechanism: in the free
initial state the step allows a read address in x16-x31 together with metadata
that the new flops can no longer hold, and no invariant ties pmode1 reads to
x0-x15. Look at the cex waveforms before strengthening.

Note: PastValidK=16 and the base-case BMC depths (7-16, s2bmc31-33) are
from round 7; round 8 regenerates them as r8base.

## Medium

### 2. Reset state never compared with the architecture

PC_Boot (checks.sv:47) is the only reset check.
- On the first step (!past_valid), the harness copies the pre-state from the
  DUT (check/spec_instance.sv:125-165, check/abs.sv): PCC, MTCC, MTDC,
  MScratchC, mepc, mstatus, priv and mshwm.
- GPRs are unchecked until past_has_reg is set.

As a result, Kudu's reset values for the root capabilities and CSRs are never
compared with Sail's reset state. A wrong reset bound or permission set on a
root capability would go unseen; every later step would be consistent with it.

Fix: add Reset_* asserts on the first step, comparing dut_* with Sail's reset
values: PCC/MTCC/MTDC root caps, mstatus, priv = M, mshwm, and GPRs untagged.

### 3. No direct check that trap-shadow entries write nothing

cmt_chk excludes shadow entries.
- Memory is checked directly (Mem_NoShadowReq), and Inv_C_* (inv.sv:452-495)
  cover shadow ordering.
- No property says that a shadow entry never writes the register file or a
  CSR. A clobber shows up only indirectly: through a later Reg_Cont read, and
  only after past_has_reg.

Fix: add Cmt_ShadowNoWr (no rf we0/1/2 for a shadow sbd entry; no CSR write
from a shadow LSQ entry).

### 4. -bound 2 induction with multi-cycle properties unconfirmed

The L0 step assumes every property with assume -from_assert -bound 2 and proves
at trace length 3. It is not confirmed how Jasper applies the bound to
properties with |=>, $past or $stable:
- Bus_InstrReqHold/DataReqHold (checks.sv:282-283);
- Harness_PastValidSoon;
- several Inv_E_* properties.

If an attempt started at cycle 1 is assumed to cover cycle 2, the target
partly assumes itself. The 16-mutant campaign (§5.2), several of them caught
at L0, gives partial confidence, but no mutant targeted a |=> property.

Fix: plant one mutant that drops instr_req_o before the grant and confirm that
the L0 step for Bus_InstrReqHold reports cex. Alternatively, check the Jasper
documentation for how -bound counts attempts.

### 5. Wrong-path out-of-scope instructions still pruned

Env_InsnScope (top.sv:237) still assumes in-scope bits for every valid IR
entry, including one that will be flushed.
- Traces where an out-of-scope word (AMO, B extension, an excluded CSR)
  reaches IR on a mispredicted path are discarded.
- So wrong-path side effects of those instructions are never explored, for
  example an AMO or CSR access starting a bus request or a CSR read before
  the flush.

Fix: restrict the assume to entries that will commit (non-shadow, on the
correct path), or replace it with an assert that out-of-scope instructions
cause no externally visible effect before retirement.

## Low

### 6. B extension excluded though the spec already has it

The cheriot-sail build (upstream_spec/out/ibexspec.sv) already contains
execute_ZBA_*, ZBB_*, ZBC_*, ZBS_* and ZBKB_*. The exclusion in insn_in_scope
is therefore a harness choice, not a spec limit. Dropping it would put Kudu's
bit-manip unit under the same proofs. Expect a cost in proof time, mostly from
clmul.

### 7. irq inputs to mip wiring unchecked

dut_mip is taken from Kudu's own mip (check/abs.sv:43), so the mapping from
irq_*_i to mip is never compared with the inputs. Mutation n7_irqmie showed
that the enable logic is checked; the input wiring is not. Fix: add an assert
that mip (after its register delay) equals the irq inputs.

### 8. Lint / cosmetic

- rtl/regfile.sv: trvk_clrtag_dec[16..31] is declared (line 43) but not
  driven after 4472c7f (line 53 is generated only for x1-x15). The signal is
  unused, so this is lint only.
- fixbmc1_20261125_224340/run.tcl lines 5 and 67: header comments copied from
  the stage-1 and fetch scripts.

## Not gaps (checked)

- CSR_Post skips mstatus.mie and the PCC (checks.sv:330-331) on purpose: a
  younger CJALR may update them first. They are checked at serialised points
  (Special_*) and through the Inv_E chain.
- A trapping early load may issue a read (Mem_GoTrap, checks.sv:200). This is
  documented at checks.sv:196-197; Mem_TrapRead forbids a write. The read is
  limited to the RAM region by decode_early_load_addr; there is no
  architectural leak.
- Compressed scope change: Fetch_Iss0/1 tie both the 32-bit and the 16-bit
  bits to memory, so passing raw c_insn to Sail is sound.
- Induction levels in mkfinal8.py match round 7. L2 assumes only L0, L1 and
  the L0 data lemmas (MulData, LsWbData).
- Out_NoFatalErr cex (fixbmc1, 9): legitimate Kudu behaviour; the
  replacement Out_FatalErr0/1 is spec-referenced and covered.

## Suggested order

1. Triage the round-8 L0 cex (gap 1) before anything else; the waveforms decide
   whether the regfile change needs a new invariant or a harness fix.
2. Mutant check for -bound 2 with |=> (gap 4); it is cheap and decides whether
   the step method is sound for the new bus checks.
3. Reset_* asserts and Cmt_ShadowNoWr (gaps 2-3), added to the next round.
4. Wrong-path scope (gap 5) and B extension (gap 6), as scope extensions.
