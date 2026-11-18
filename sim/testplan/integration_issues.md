# CHERIoT-Kudu integration issues

Core behaviour that the design owner has waived, provided that the SoC
integrator meets a requirement. Each entry gives the requirement, what goes
wrong when it is violated, and where the evidence is. All entries are to be
added to the integration manual.

| ID | Area | Requirement | Source | Waived |
|---|---|---|---|---|
| INT-1 | Interrupts | Interrupt lines stay asserted until acknowledged at their source | KUDU-072 ([bug_logs_3.md](bug_logs_3.md)) | 2026-11-14 |
| INT-2 | Debug | debug_req stays asserted until the hart is halted | KUDU-073 ([bug_logs_3.md](bug_logs_3.md)) | 2026-11-14 |
| INT-3 | Memory map | The first word above the early-load region is side-effect-free to read | FV, `AssertEarlyLoadSplitInRegion` (not numbered) | 2026-11-15 |

## INT-1 and INT-2: interrupt lines and debug_req must not withdraw

- **Interrupts (KUDU-072):** an interrupt line (irq_external, irq_software,
  irq_timer, irq_fast) must stay asserted until software acknowledges it at
  its source. If a line drops without an acknowledgement, the core may still
  take the interrupt it had already decided on. The trap is then reported
  with mcause = machine timer (0x80000007), even when MTIE = 0.
- **Debug requests (KUDU-073):** debug_req must stay asserted until the hart
  is halted (the debug module sees halted / allhalted). If it drops in the
  two cycles after the core decides to halt, the hart still enters debug
  mode. It reports the reserved dcsr.cause = 0, or STEP when dcsr.step = 1.
- mepc, dpc and the resume pc are correct in both cases. Only the reported
  cause is wrong.
- **Root cause:** the issuer latches `special_case_q` at the WAIT_CMT0
  decision, but re-derives the cause from live inputs one cycle later in
  CSM_ISSUE_SPECIAL (`rtl/issuer.sv:835`, `:948-952`, `:968-975`,
  `:1004-1018`).
- **Evidence:** `sim/tests_2/rtl_bug_irq_withdraw` and
  `sim/tests_2/rtl_bug_dbg_req_withdraw` (DEFER, collide testbench); details
  in the KUDU-072 and KUDU-073 sections of [bug_logs_3.md](bug_logs_3.md).
- **Coverage:** `cp_irq_cause_vs_line` bin `withdrawn` records the violating
  case ([fcov_bug_crosscheck.md](fcov_bug_crosscheck.md)).

## INT-3: the word above the early-load region must be side-effect-free

- An early load is sent to the bus before its checks complete; the checks
  are applied on the response. The early-load region is decoded from the
  load's base address only (`rtl/ls_pipeline.sv:93-96,227`; default region
  `0x8000_0000`–`0x80FF_FFFF`, or the `KUDU_CUSTOM_ADDR_DECODE` decode).
- A misaligned load whose base is in the last 3 bytes of the region is
  split. Its second beat goes to the first word above the region
  (`0x8100_0000` by default) and is still issued as an early load.
- **Requirement:** the first word above the early-load region must be
  side-effect-free to read (memory or unmapped, not a device register). A
  custom region decode must meet the same rule at its upper boundary.
- **Evidence:** 7-cycle JasperGold CEX of `AssertEarlyLoadSplitInRegion`
  (`sim/fcov/kudu_fcov_lsu.sv`) at pmode 0 and 1, snapshot
  `/home/scratch/fortress/kunyanliu/fvall_20261115_171802` (`p{0,1}_lsu`).
  The assertion is kept and listed in `fcov_expected_cex`
  (`fv/fv_kudu_fcov.tcl`), so FV reports it as an expected CEX; a simulation
  that reaches this case still reports an assertion failure.
