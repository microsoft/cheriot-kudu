# CSR architectural tests

`isa_test_csr` runs in CHERIoT PMODE=1; `rv32_test_csr` runs in PMODE=0
on either the CHERIoT-capable or plain RV32 elaboration. Both use
`csr_patterns.h` and `csr_patterns.inc` from this directory. The existing
`CSR test passed` / `CSR test failed` UART verdicts remain authoritative;
simulator exit status alone is not a verdict.

Both tests print one completion line for each CSR in the pattern
matrix. Completion lines include cumulative case and failure counts in
decimal without leading zeros, and a four-digit, zero-padded hexadecimal CSR
address (for example, `csr=0x0300 total_cases=132 total_failures=0`).
The final case/failure totals also use decimal. A separate message announces
the start of the precise-trap matrix, followed by the final verdict.
Progress is reported between CSR
groups, never inside a helper's save/restore window.

## Pattern coverage

Each listed CSR gets six seed patterns: zero, all ones, alternating
`aaaaaaaa` / `55555555`, `80000100`, and `80000308`. Seeds replace only
the selected writable bits; all other original bits are preserved.

For every seed:

* CSRRS and CSRRC use the seed, its complement, `0x200`, and **a non-x0
  source register holding zero**, restricted to the selected writable mask.
  Ignored-write CSRs receive the unrestricted operands.
* CSRRSI and CSRRCI use zimm **0, 1, 8, 16, 21, 31**. Unlike a register
  holding zero, zimm=0 suppresses the write.
* CSRRS/CSRRC with encoded rs1=x0 provide two more read-only controls.

Every case checks the independently calculated legalized seed, returned old
value, final readback, and restoration readback. CSRRW seeds/restores each case.
Failures accumulate with CSR address, operation, seed, operand, old/readback,
expected, saved and restored values; subsequent CSRs and the trap matrix still
execute. Operation IDs: 0/1=register SET/CLEAR; 2/3=zimm0; 4/5=zimm1;
6/7=zimm8; 8/9=zimm16; 10/11=zimm21; 12/13=zimm31; 14/15=rs1=x0.

| CSR(s) | Selected writable mask / behavior |
| --- | --- |
| MSTATUS `300` | `00200088`: TW, MPIE, MIE; preserve MPP/MPRV |
| MIE `304` | `7fff0888`: implemented fast, external, timer, software enables |
| MCOUNTINHIBIT `320` | `00000005`: CY/IR; bit1 zero, absent HPM bits stay one |
| MSCRATCH `340`, MTVAL `343` | `ffffffff` |
| MCAUSE `342` | `8000001f`; reserved bits remain zero |
| CPUCTRL `7c0` | `00000010`: constant-fetch only |
| MCYCLE/H `b00/b80`, MINSTRET/H `b02/b82` | `ffffffff`, inhibited during exact comparisons |
| MTVEC `305`, MEPC `341` (PMODE=0 only) | `fffffffc`, `fffffffe`: aligned address WARL |
| MSHWM/MSHWMB `bc1/bc2` (PMODE=1 only) | `fffffff0`: 16-byte alignment |
| CDBG_CTRL `bc4` (PMODE=1 only) | `00000001` |
| MISA `301`, MCOUNTEREN `306`, MIP `344`, SECURESEED `7c1` | Ignored writes / unchanged readback |
| TSELECT/TDATA1/2/3/MCONTEXT/SCONTEXT `7a0/7a1/7a2/7a3/7a8/7aa` | M-mode writes ignored; programming requires debug mode |

CPUCTRL runs zimm=0/16 only: other immediate bits change CFG-dependent cache
and predictor controls, so their legal values are not assumed. MSTATUS's MIE
bit is exercised only while MIE's interrupt-source enables are all zero;
otherwise global interrupts stay disabled. Counters are inhibited before
testing; MCOUNTINHIBIT's own cases may briefly enable counting, but the
inhibit state is restored before the counter data cases. MIP assumes no
injected asynchronous interrupts. Do not run these tests with interrupt/debug
injection or memory-error injection.

There are **3120 pattern cases in PMODE=1**, **2988 in PMODE=0**. No
memory operations or calls occur between saving and restoring each CSR, which
protects the watermark cases from software stores. In PMODE=0 MTVEC is
temporarily replaced only in this straight-line, non-faulting code, with
interrupts disabled; the real vector is restored before any trap checks.
The known raw-mask address-legalization RTL bug must produce failures for
MTVEC/MEPC SET/CLEAR, including non-x0 zero operands and nonzero immediates.
Those failures are not masked or marked as passes.

## Read-only and inaccessible registers

The original precise-PC/cause/privilege trap matrices are retained and
extended: **77 traps for CHERIoT, 66 for RV32**. All four ID registers
`f11..f14` permit the four zero-operand read forms and reject register
SET/CLEAR (including a non-x0 zero source) and nonzero immediate SET/CLEAR.
Unknown CSRs, debug-only `7b0..7b3`, and PMODE=1 numeric MTVEC/MEPC receive
all four illegal RMW checks in addition to the existing read/write checks.
Existing U-mode privilege, ECALL/EBREAK, MRET and CHERIoT SCR tests remain.

DPC/DCSR/DSCRATCH are **not** writable M-mode test targets: they require a
debug-mode harness. CHERIoT MTCC/MEPCC/MSCRATCHC/MTDC are capabilities, not
integer CSR RMW targets; existing SCR save/restore and capability comparisons
are retained. PMP, optional HPM counters/events, unimplemented CSR addresses,
CPUCTRL's other fields and MSTATUS's privilege-changing fields are outside
this safe writable-pattern scope. This is not a claim to test every CSR or
every pipeline configuration.

## Isolated validation

Do not run the normal build scripts in `tests/`: they overwrite `tests/work`
and `run/bin`. Mirror both test directories, `csrc_cheri`, `csrc_rv32`,
linker scripts and build scripts into a fresh `sim/temp/<run>/program` tree,
including empty `program/run/bin`; invoke the copied scripts from its
`tests` directory. Set `TMPDIR` to a directory inside that private tree.

From `sim/run`, `submit -i ./vcscomp -nowave -outdir=<fresh-build>` builds
both simulators. Each simulation needs its own fresh working directory and
`bin` symlink to the private images (non-DII loading ignores `+BINDIR`).
Use `submit -i <build>/simv +TEST=isa_test_csr +PMODE=1` or
`submit -i <build>/simv[32] +TEST=rv32_test_csr +PMODE=0`; repeat with all
four instruction/data grant/response `WMAX` plusargs set to 3.
Allow `+TIMEOUT=5000000` for complete failure diagnostics.
