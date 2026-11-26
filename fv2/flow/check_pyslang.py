#!/usr/bin/env python3
# Parse + elaborate kudu RTL + Sail spec + fv2 harness with pyslang.
import os, sys
sys.path.insert(0, "/home/scratch/fortress/kunyanliu/pylib_pyslang")
import pyslang
from pyslang import driver as sd

SUPER = "/home/kunyanliu/riscdev/super"
T = "/home/scratch/fortress/kunyanliu/e2e_tools"
RTL = SUPER + "/rtl"
FV2 = SUPER + "/fv2"

rtl_files = """cheri_pkg csr_pkg super_pkg kudu_cfg_pkg dual_fifo stage_fifo wt_fifo
waw_tracking_fifo regfile ir_decoder ir_stage issuer fetch_fifo64 prefetch_buffer64
compressed_decoder if_stage alu_decoder rv32_alu cheri_alu alu_pipeline
load_store_unit lsu_if dcache cheri_trvk_stage ls_pipeline multdiv32 mult_pipeline
committer branch_unit branch_predict ibex_counter ibex_csr cs_registers cmplx_unit
kudu_top""".split()

files = [f"{RTL}/{f}.sv" for f in rtl_files] + [
    f"{T}/upstream_spec/out/ibexspec.sv",
    f"{FV2}/spec/stub.sv",
    f"{T}/upstream_spec/out/extracted.sv",
    f"{FV2}/spec/ext_bounds.sv",
    f"{FV2}/spec/cheri.sv",
    f"{FV2}/spec/spec_api.sv",
    f"{FV2}/check/top.sv",
]
incs = [RTL, f"{T}/src/sail/lib/sv", f"{T}/upstream_spec/out", f"{FV2}/spec", f"{FV2}/check"]

args = ["slang", "--single-unit", "-DSYNTHESIS=1", "-DCHERIoT=1", "-DKUDU_FORMAL_RTL=1",
        "--top", "kudu_e2e_top", "--error-limit=1000", "--allow-hierarchical-const", "--allow-genblk-reference",
        "--ignore-unknown-modules"]
args += [f"-I{i}" for i in incs] + files

d = sd.Driver(); d.addStandardArgs(); d.setTerminalColorsEnabled(False)
if not d.parseCommandLine(" ".join(args)):
    sys.exit("bad command line")
if not d.processOptions():
    sys.exit("bad options")
if not d.parseAllSources():
    print("parse failed")
comp = d.createCompilation()
diags = comp.getAllDiagnostics()
eng = pyslang.DiagnosticEngine(comp.sourceManager)
cl = pyslang.TextDiagnosticClient()
eng.addClient(cl)
show_all = "--all" in sys.argv
n_err = n_fv2 = n_fv2_err = 0
for x in diags:
    sev = eng.getSeverity(x.code, x.location)
    is_err = sev in (pyslang.DiagnosticSeverity.Error, pyslang.DiagnosticSeverity.Fatal)
    fn = str(comp.sourceManager.getFileName(x.location))
    mine = "/fv2/" in fn
    n_err += int(is_err)
    n_fv2 += int(mine)
    n_fv2_err += int(mine and is_err)
    if show_all or mine or is_err:
        eng.issue(x)
print(cl.getString(), end="")
print("-" * 70)
print("total diagnostics: %d, errors: %d, fv2 diagnostics: %d (fv2 errors: %d)"
      % (len(diags), n_err, n_fv2, n_fv2_err))
print("PYSLANG_RESULT:", "PASS" if n_err == 0 else "FAIL")
sys.exit(0 if n_err == 0 else 1)
