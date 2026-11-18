"""Run the standalone queued timing monitor tests (no covergroup support needed).

Uses Verilator only for the covergroup-free helper. Each invocation preserves
its build and test logs in a fresh sim/temp/flow_bus_timing_runs directory.
"""
import os
from pathlib import Path
import resource
import subprocess
import uuid


def main():
    here = Path(__file__).resolve().parent
    work = here.parent / "temp" / "flow_bus_timing_runs" / uuid.uuid4().hex
    work.mkdir(parents=True)
    # Expected $fatal tests must not leave core dumps behind.
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    env = dict(os.environ, TMPDIR=str(work))
    command = [
        "verilator", "--binary", "--timing", "--top-module", "tb_flow_bus_timing",
        "--Mdir", str(work / "obj"), "-DKUDU_FCOV_BUS_TIMING_ONLY",
        str(here / "kudu_fcov_top.sv"), str(here / "tb_flow_bus_timing.sv"),
    ]
    with (work / "build.log").open("w") as log:
        result = subprocess.run(command, cwd=work, env=env, stdout=log,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"Build failed: {work / 'build.log'}")
    binary = work / "obj" / "Vtb_flow_bus_timing"
    for name, expected in [
        ("normal", "PASS: queued bus timing"),
        ("orphan", "FCOV timing: response without accepted request"),
        ("overflow", "FCOV timing: pending queue overflow"),
        ("timestamp_overflow", "FCOV timing: timestamp overflow"),
        ("grant_overflow", "FCOV timing: grant delay overflow"),
    ]:
        command = [str(binary)] + ([] if name == "normal" else ["+" + name])
        with (work / (name + ".log")).open("w") as log:
            result = subprocess.run(command, cwd=work, env=env, stdout=log,
                                    stderr=subprocess.STDOUT)
        text = (work / (name + ".log")).read_text()
        if expected not in text or ((result.returncode == 0) != (name == "normal")):
            raise SystemExit(f"{name} failed: {work / (name + '.log')}")
        print(f"PASS: {name}")
    print(f"Preserved logs: {work}")


if __name__ == "__main__":
    main()
