"""Elaborate the Kudu RTL plus the functional coverage model with pyslang.

    python sim/fcov/check_syntax.py
    python sim/fcov/check_syntax.py --matrix

The default matches the CHERIoT KuduCfg1 testbench build.  --matrix checks
KuduCfg1/1x/2/3 with CHERIoT enabled and disabled (both the macro and parameter).
--fv-helpers also defines KUDU_FV_HELPERS (the formal-only kudu_fvh_* helper
lemmas; they exist only with CHERIoT defined and KUDU_FCOV_OFF undefined).
Top parameter overrides are in memory; no build files or logs are overwritten.
This checks elaboration, not simulator coverage collection or reachability.
"""
import argparse
import glob
import os
import shlex
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RTL = os.path.join(ROOT, "rtl")
FCOV = os.path.dirname(os.path.abspath(__file__))

PKG_ORDER = [
    "kudu_cfg_pkg.sv",
    "cheri_pkg.sv",
    "csr_pkg.sv",
    "super_pkg.sv",
    "tracer_pkg.sv",
]

# Not part of the kudu_top hierarchy and not self-contained (it relies on the
# DPI flow's own compilation unit for MemW / rvfi_t).
SKIP = {"tracer_dpi_wrapper.sv"}

CONFIGS = ("KuduCfg1", "KuduCfg1x", "KuduCfg2", "KuduCfg3")


def coverage_sources():
    """Read source order from the real coverage file list, including new modules."""
    flist = os.path.join(FCOV, "kudu_fcov.f")
    sources = []
    with open(flist, encoding="utf-8") as source:
        for line in source:
            line = line.split("//", 1)[0].strip()
            if not line:
                continue
            line = line.replace("${verifRoot}", os.path.dirname(FCOV))
            line = line.replace("$verifRoot", os.path.dirname(FCOV))
            entries = shlex.split(line)
            for entry in entries:
                if entry.startswith(("+", "-")):
                    raise ValueError("expected a source path in %s, got %s" % (flist, entry))
                path = os.path.normpath(os.path.join(FCOV, entry))
                if not os.path.isfile(path):
                    raise ValueError("coverage source not found: %s" % path)
                if path in sources:
                    raise ValueError("duplicate coverage source: %s" % path)
                sources.append(path)
    if not sources:
        raise ValueError("empty coverage file list: %s" % flist)
    if os.path.basename(sources[-1]) != "kudu_fcov_bind.sv":
        raise ValueError("kudu_fcov_bind.sv must be last in %s" % flist)
    return sources


def rtl_sources():
    pkgs = [os.path.join(RTL, p) for p in PKG_ORDER]
    rest = sorted(
        f for f in glob.glob(os.path.join(RTL, "*.sv"))
        if os.path.basename(f) not in PKG_ORDER
        and os.path.basename(f) not in SKIP
    )
    return pkgs + rest


def elaborate(config, cheriot, sources, *, coverage_off=False, fv_helpers=False,
              all_diagnostics=False):
    import pyslang
    from pyslang import driver as sd

    args = ["slang", "-DRVFI=1", "--error-limit=500", "--top", "kudu_top",
            "-Wno-unused-def", "-GCFG=kudu_cfg_pkg::" + config,
            "-GCHERIoTEn=%d" % cheriot, "-GUseDWMult=0", "-GRvfiDumpEn=1"]
    if cheriot:
        args.append("-DCHERIoT=1")
    if coverage_off:
        args.append("-DKUDU_FCOV_OFF=1")
    if fv_helpers:
        # The helpers name the unnamed DCacheEn block of ls_pipeline (genblk1),
        # which JasperGold accepts.
        args += ["-DKUDU_FV_HELPERS=1", "--allow-genblk-reference"]
    args += sources

    d = sd.Driver()
    d.addStandardArgs()
    d.setTerminalColorsEnabled(False)
    if not d.parseCommandLine(" ".join('"%s"' % a for a in args)):
        print("command line parse failed")
        return 2
    if not d.processOptions():
        return 2
    if not d.parseAllSources():
        return 2

    comp = d.createCompilation()
    diags = comp.getAllDiagnostics()   # forces full elaboration, incl. binds
    eng = pyslang.DiagnosticEngine(comp.sourceManager)
    cl = pyslang.TextDiagnosticClient()
    eng.addClient(cl)
    n_err = 0
    fcov_errors = 0
    fcov_diags = 0
    fcov_hierarchy_warnings = 0
    for x in diags:
        severity = eng.getSeverity(x.code, x.location)
        is_error = severity in (pyslang.DiagnosticSeverity.Error,
                                pyslang.DiagnosticSeverity.Fatal)
        if is_error:
            n_err += 1
        filename = str(comp.sourceManager.getFileName(x.location))
        owned = os.path.abspath(filename).startswith(FCOV + os.sep)
        if owned:
            fcov_diags += 1
            fcov_errors += int(is_error)
            # Direct RTL observations are intentional; unresolved paths still fail.
            fcov_hierarchy_warnings += int(
                not is_error and x.code == pyslang.Diags.UpwardHierarchicalName)
        # Never hide an RTL elaboration error behind a coverage-only filter.
        if all_diagnostics or owned or is_error:
            eng.issue(x)
    print(cl.getString(), end="")
    print("-" * 70)
    print("%s CHERIoT=%d: fcov diagnostics: %d (%d errors, %d permitted hierarchy warnings); "
          "other diagnostics: %d; total errors: %d"
          % (config, cheriot, fcov_diags, fcov_errors, fcov_hierarchy_warnings,
             len(diags) - fcov_diags, n_err))
    return 1 if n_err or fcov_diags != fcov_hierarchy_warnings else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", choices=CONFIGS, default="KuduCfg1")
    parser.add_argument("--cheriot", choices=("on", "off", "both"), default="on")
    parser.add_argument("--matrix", action="store_true",
                        help="check all four named configurations with CHERIoT on/off")
    parser.add_argument("--coverage-off", action="store_true",
                        help="also define KUDU_FCOV_OFF")
    parser.add_argument("--fv-helpers", action="store_true",
                        help="also define KUDU_FV_HELPERS (formal-only helper lemmas)")
    parser.add_argument("--all-diagnostics", action="store_true",
                        help="show RTL warnings as well as all errors and coverage diagnostics")
    options = parser.parse_args()
    try:
        sources = rtl_sources() + coverage_sources()
        configs = CONFIGS if options.matrix else (options.config,)
        modes = (True, False) if options.matrix or options.cheriot == "both" else (
            options.cheriot == "on",)
        result = 0
        for config in configs:
            for cheriot in modes:
                result = max(result, elaborate(
                    config, cheriot, sources, coverage_off=options.coverage_off,
                    fv_helpers=options.fv_helpers, all_diagnostics=options.all_diagnostics))
        return result
    except (OSError, ValueError, ImportError) as error:
        print("ERROR: %s" % error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
