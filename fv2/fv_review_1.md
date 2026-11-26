# fv2 end-to-end formal flow: gap review 1

Date: 2026-11-25. Scope: fv2/ harness (check/, spec/, verify.tcl, README.md),
the stage-2 run scripts in /home/scratch/fortress/kunyanliu/e2e_tools/kudu_e2e/,
and the RTL as of the review date. Read-only review; nothing was changed.

## Summary

The proof method is sound as far as it goes: step-ordered k=2 induction, with
base-case BMC to depth 7-21, and the div/mul lemmas are discharged outside the
harness. The gaps are in **what is assumed** and **what is left unchecked**,
plus one RTL change that no proof or regression has seen yet.

| # | Severity | Gap |
|---|---|---|
| 1 | High | Uncommitted regfile RTL change is newer than all proof and coverage evidence |
| 2 | High | Bus model: fixed 1-cycle response, short grant windows |
| 3 | High | Instruction-scope assumes use the DUT's own decode |
| 4 | High | alas() lets the DUT clear any tag although revocation is off |
| 5 | Medium | Large areas with no formal coverage |
| 6 | Medium | Interrupt assumptions; no liveness |
| 7 | Medium | DUT outputs never compared |
| 8 | Medium | No single proof run matches the current harness and RTL |
| 9 | Low | Kudu/Sail divergences assumed away rather than waived |
| 10 | Low | Values sourced from the DUT side |
| 11 | Low | Formal-only regfile read mux |
| 12 | Low | Flow not reproducible from the repository |

## High

### 1. Uncommitted RTL change is newer than all evidence

- **rtl/regfile.sv** and **rtl/kudu_top.sv** have uncommitted changes, made
  2026-11-25 at 18:23-18:37.
  - NRegs becomes a localparam, and kudu_top no longer passes #(.NRegs(32)).
  - Registers x16-x31 move to a new g_rf_flop_1 loop that keeps only 32-bit
    data: no tag or capability metadata, and no trvk tag clear.
- The change is newer than:
  - the round-7 stage-2 proof (s2fin7*, 11-24 05:47-06:12);
  - the mutation runs (11-25 01:59);
  - the coverage campaign (finished 11-25 15:24).
- x16-x31 are illegal in pmode1 (**rtl/ir_decoder.sv:142**, illegal_reg_cheri).
  The fv2 harness is pmode1-only (Env_Pmode), so it cannot see this change at
  all.
- **Action:** run pmode0 simulation (mini regression + riscv-tests) before
  relying on it, or revert.

### 2. Bus model is too tight

- **check/top.sv:160-174**:
  - Env_InstrRsp / Env_DataRsp force rvalid exactly one cycle after the
    grant.
  - Env_InstrGntWithin allows a grant delay of 0-3 cycles;
    Env_DataGntWithin allows 0-1.
- So variable response latency, a long data-grant stall, and a response that
  arrives while a new request is pending are never explored. Today only the
  simulation memdly runs (+*_GNT_WMAX / +*_RESP_WMAX) cover them.
- **Action:** add an optional variable-latency bus model (response 1..N
  cycles after grant, in order), at least for a BMC run.

### 3. Instruction-scope assumes use the DUT's own decode

- **check/top.sv:232-234**:
  - Env_InsnScope applies insn_in_scope to the instruction **after** Kudu has
    expanded it. insn_in_scope (**top.sv:194**) takes is_comp and c_insn as
    arguments but never uses them.
  - Env_NoCmplx and Env_NoBrkpt assume on Kudu's decoder outputs (is_cmplx,
    is_brkpt).
- Consequences:
  - If Kudu mis-expands a compressed instruction into an out-of-scope
    encoding (for example a B-extension or excluded-CSR form), the trace is
    silently dropped instead of failing.
  - Likewise if Kudu wrongly flags an in-scope instruction as AMO or as a
    breakpoint.
- **Action:** scope on the raw fetched bits instead:
  - every 16-bit encoding is in scope;
  - AMO is raw opcode 0x2f;
  - the breakpoint condition comes from the trigger CSR state, not the
    decoder.

### 4. alas() accepts a cleared tag although revocation is off

- **spec/cheri.sv:144-148**: the comment reads "'At least as strict': the DUT
  may clear a tag the spec would keep."
- alas() is used by:
  - the operand checks (**check/checks.sv:57-66**);
  - the commit checks (**checks.sv:177-179**);
  - several invariants (**check/inv.sv:1671, 1716, 1774, 1786**).
- The relaxation exists for load-time revocation. This harness ties revocation
  off (tsmap_rdata=0, mem_revoke_i=0), so Kudu has no legitimate reason to
  clear a tag. A spurious tag loss (a functional bug: lost capabilities) passes
  every check.
- **Action:** under the current environment, use exact cap_eq, or gate the
  relaxation on a revocation-enabled define.

## Medium

### 5. Large areas with no formal coverage

- **Extensions:**
  - B: Zba, Zbb, Zbc and Zbs are all excluded by insn_in_scope.
  - A: AMO, LR and SC (Env_NoCmplx; not compiled into the Sail spec).
- **CSRs:**
  - Only a 12-CSR whitelist is in scope: 300, 301, 304, 340, 342, 343,
    f11-f14, bc1, bc2.
  - Excluded: mtvec, mepc, mstatush, mip, mcycle/minstret and the other
    counters, mcountinhibit, mhpm*, tselect/tdata, dcsr/dpc, pmp and mseccfg.
  - Also excluded: the illegal-instruction trap for an unimplemented CSR.
  - The spec is fed mcycle=0 and mcounteren=0.
- **Configuration and environment:**
  - Data cache: DCacheEn=0 in the harness, while the shipping Cfg1 enables it.
  - Instruction and data bus errors, SC failure, revocation, debug
    (Env_NoDebugReq), hardware breakpoints.
  - pmode0, Cfg2 and Cfg3, PC wrap, self-modifying code, wfi wake and sleep.
- **Load data / memory:**
  - The Mem_Rdata* assumes (**checks.sv:~263-294**) tie bus read data to the
    spec's free read inputs.
  - There is no memory model, so store-to-load data flow is not checked end to
    end. That is acceptable only while there is no store buffer forwarding and
    no D-cache.
  - Memory capabilities are assumed well-formed (Mem_RdataCapWFAny,
    Mem_SpecRdCapWF).
- Both open bugs fall in excluded areas: **KUDU-019** (minstret) and
  **KUDU-042**.
- **Action:** widen scope incrementally:
  1. counter CSRs and the unknown-CSR trap;
  2. B extension (the Sail model has it);
  3. a simple word memory model for store-to-load;
  4. a DCacheEn=1 build.

### 6. Interrupt assumptions and no liveness

- Env_IrqHeld (**check/top.sv:187**): a pending IRQ line cannot drop until
  csr_save_cause. So a masked pending interrupt that later goes away, or a
  glitching level-sensitive line, is never explored.
- The spec's interrupt decision uses Kudu's own mip (dut_mip in
  **check/abs.sv**). The irq_* inputs → mip wiring and its masking are
  therefore never checked against the spec.
- Nothing proves an interrupt is eventually taken. Cov_Irq only shows the path
  is reachable. Interrupt latency and "never taken" are liveness properties;
  stage 3 has not started.
- **Action:**
  - add a run with the IrqHeld assume removed;
  - compute the spec's mip from the irq_* inputs;
  - add a bounded-latency liveness assert (interrupt pending, enabled and
    unmasked → taken within N instructions).

### 7. DUT outputs never compared

- Capability store, untagged: Mem_CapStoreCap (**checks.sv:252**) is gated on
  wr_tag. For an untagged capability store the upper (metadata) word of
  data_wdata_o is not checked; only Mem_CapStoreAddr (the low word) and the
  tag bit are.
- Capability-store byte enables are not checked; Mem_Addr compares the
  word-aligned address only.
- Never checked at all: data_amo_flag_o, cheri_fatal_err_o and the
  revocation-map (tsmap) address and request.
- No request-stability check: nothing asserts that address, wdata, we and be
  stay stable from req until gnt.
- CSR_Post_Mstatus checks mpie, mpp, mprv and tw. mstatus.mie and the PCC are
  checked only at serialised points (Special_Post).
- **Action:** add the missing output asserts. Each is a one-line property.

### 8. No single proof run matches the current harness and RTL

- These harness files were edited after the round-7 stage-2 proof:
  - **check/inv.sv** (11-24 20:40)
  - **check/spec_instance.sv** (11-24 20:05)
  - **check/top.sv** (11-25 17:39)
  - **check/fetch.sv** (11-25 18:46)
- The fetch-group invariants were proven in separate runs (fchstp1-3,
  fchbmc1-2, 11-25 17:42-19:12).
- No run covers the full 825+ property set on the final harness and current
  RTL together.
- Some L0 properties passed only on 40-minute reruns after timing out at
  15 minutes.
- The README header (**README.md:9**) still says "stage 2 (induction) next".
- **Action:** one consolidated rerun (BMC + step-ordered induction) on the
  current harness and RTL, and record its run directory and results in the
  README.

## Low

### 9. Kudu/Sail divergences assumed away rather than waived

- Env_NoDivGRd0/1 (**check/spec_instance.sv:306-309**) exclude CSpecialRW
  reads of an MEPCC that was written lossily.
- pcc_eq_noaddr and xepc_eq (**spec/cheri.sv**) relax the comparison for
  untagged values (with E>24 for xepc).
- spec_mtcc_unrecoverable is not counted in int_err_o
  (**spec/spec_api.sv:11-16, 419-423**).
- The spec is also aligned to Kudu for sfence and U-mode wfi
  (**README.md §1.1**).
- These are deliberate, but each is a place where a divergence of the same
  shape would be hidden. Record each one as an explicit waiver in the README,
  with the reason and the matching Sail/Kudu behaviour.

### 10. Values sourced from the DUT side

- The spec reads misa from Kudu.
- The vendor, arch and impl ID constants come from the same csr_pkg that Kudu
  uses.
- None of these values is independently checked.

### 11. Formal-only regfile read mux

- With KUDU_FORMAL_RTL defined, **rtl/regfile.sv:96-108** replaces the
  rf_reg[raddr] read with (raddr == 0) ? 0 : rf_reg_q[raddr].
- The change is trivially equivalent, but the proven read path is not the
  synthesised one.
- `ifdef FORMAL blocks also exist in dual_fifo, stage_fifo, wt_fifo and
  waw_tracking_fifo. FORMAL is not defined by verify.tcl.
- **Action:** a quick LEC or Jasper SEC of regfile with and without the
  define.

### 12. Flow not reproducible from the repository

- **verify.tcl** is the stage-1 BMC script only (depth 20, prove -all).
- The step-ordered stage-2 proof lives in ad-hoc tcl under
  e2e_tools/kudu_e2e/ (s2fin7*, s2r7l1/2/3).
- fv2/ is untracked in git, and the README says it is not part of the
  regression.
- **Action:** check in the stage-2 tcl (and the mutation tcl), with a
  one-command wrapper.

## Not gaps (checked)

- Env_FetchMem freezes a single symbolic halfword, which is sound for a
  fetch-data check.
- Fetch_Iss0 checks only s0_mode == MAIN_IDEX. Fetch-error mode is unchecked,
  which is consistent with instruction errors being excluded (gap 5).
- E2E_ZERO_WAIT (**top.sv:175-180**) is an opt-in deep-BMC variant; it is not
  used by default.
- Three fcov helper CEXs (AssertHelpFpcRdStable, HlpJWl4, HlpWrsvConv, see
  CEX_TRIAGE §3) are from the fv/ fcov flow, not fv2.

## Suggested order

1. Regress or revert the regfile change (gap 1).
2. Fix gaps 3, 4 and 7. These are small harness edits.
3. Consolidated rerun on the current harness and RTL; update the README
   (gap 8).
4. Add a variable-latency bus option (gap 2) and a run where IRQ lines can
   drop (gap 6).
5. Widen scope: counter CSRs, then B extension, then a memory model, then
   DCacheEn=1 (gap 5).
6. Check the stage-2 flow into the repository (gap 12).
