#!/usr/bin/env python3
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Native regression of the production context points, taps and exclusions.

Run from sim with the VCS modules loaded. All licensed tools use submit -i;
artifacts go into a fresh sim/temp/context_events_<uuid> directory.
--check DIRECTORY rechecks existing reports without running licensed tools.
The fixture uses the full IR pipeline domain and reduced S0/EX categories.
"""

import argparse
from collections import Counter
from itertools import product
import os
from pathlib import Path
import re
import uuid

from run_ex_semantics import instance, point, require, row_map, run


def extract(source, pattern):
    matches = re.findall(pattern, source, re.S)
    require(len(matches) == 1, ("production extraction", pattern))
    return matches[0]


def fixture(source):
    ir_type = extract(source, r"  typedef enum logic \[3:0\].*?} ir_context_e;")
    ir_enabled = extract(source, r"  function automatic bit ir_enabled.*?endfunction")
    classifier = extract(source, r"  function automatic ir_context_e classify_ir.*?endfunction")
    taps = extract(source, r"  assign ir0_dec =.*?(?=  if \(!CFG.IrStageBypass\[1\]\))")
    groups = [extract(source, r"\bcovergroup " + name + r"\b.*?\bendgroup")
              for name in ("cg_frontend", "cg_execution")]
    stage = extract(source, r"  for \(genvar i = 0; i < 6; i\+\+\).*?(?=    covergroup)")
    return """// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
module context_issuer import super_pkg::*; (
  input ir_dec_t ira_dec, irb_dec,
  input logic ira_is0
);
  ir_dec_t ir0_dec, ir1_dec;
  logic cmt_err_i = 0, handle_debug = 0, handle_irq = 0;
  logic [1:0] ir_any_err = 0;
  assign ir0_dec = ira_is0 ? ira_dec : irb_dec;
  assign ir1_dec = ira_is0 ? irb_dec : ira_dec;
endmodule

module kudu_top;
  import super_pkg::*;
`ifdef CHERIoT
  localparam bit CHERIoTEn = 1;
`else
  localparam bit CHERIoTEn = 0;
`endif
  bit clk_i = 0, rst_ni = 0, pmode = 0;
  typedef enum int {C_ALU_RI = 0, C_AMO = 11, C_ILLEGAL = 18, EMPTY = 31}
    context_category_e;
  localparam int Alu0Wb = 0, Alu1Wb = 1, LsifDly = 2, LsuReq = 3,
    MultEx2 = 4, MultWb = 5;
  logic [1:0] ir_valid, ir_cmplx_amo, ir_err;
  logic [5:0] ex_cmplx_amo = 0;
  logic [4:0] special_event;
  int s0_category[2], ex_category[6];
  logic ira_is0 = 1;
  ir_dec_t ira_dec, irb_dec, ir0_dec, ir1_dec, logical_dec[2];
  int ir_states[10] = '{0, 1, 2, 3, 4, 5, 8, 9, 16, 17};
  int ex_states[5] = '{0, 31, 11, 12, 13};
  assign ira_dec = ira_is0 ? logical_dec[0] : logical_dec[1];
  assign irb_dec = ira_is0 ? logical_dec[1] : logical_dec[0];
  context_issuer issuer_i(ira_dec, irb_dec, ira_is0);
""" + ir_type + """
  ir_context_e ir_context[2];
  function automatic bit category_enabled(int c);
    return c inside {C_ALU_RI, EMPTY};
  endfunction
  function automatic bit ex_enabled(int c, int stage);
    return category_enabled(c) || c == C_AMO;
  endfunction
""" + ir_enabled + classifier + taps + groups[0] + """
  cg_frontend u_frontend = new();
""" + stage + groups[1] + """
    cg_execution u_execution = new();
  end
  task automatic tick();
    #1; clk_i = 1; #1; clk_i = 0;
  endtask
  task automatic set_ir(int slot, int state, int mask);
    logical_dec[slot] = '0;
    ir_valid[slot] = !(state inside {8, 17});
    logical_dec[slot].pl_type = state == 9 ? PL_MULT : pl_type_e'(state >= 8 ? 0 : state);
    logical_dec[slot].insn = state == 9 ? 32'h02004033 : 32'h02000033;
    logical_dec[slot].is_cmplx = state inside {16, 17};
    logical_dec[slot].any_err = mask[slot + 1] && !mask[4];
    logical_dec[slot].is_brkpt = mask[3];
    logical_dec[slot].sysctl.valid = mask[0];
    logical_dec[slot].is_branch = state == 0;
    logical_dec[slot].ptaken = mask[4];
  endtask
  task automatic sample_context(int mask, int ir0, int ir1, int s0, int s1, int ex);
    issuer_i.cmt_err_i = mask[4];
    issuer_i.handle_debug = mask[3];
    issuer_i.ir_any_err = mask[2:1];
    issuer_i.handle_irq = mask[0];
    set_ir(0, ir0, mask);
    set_ir(1, ir1, mask);
    s0_category = '{s0, s1};
    foreach (ex_category[i]) ex_category[i] = ex >= 11 && ex <= 13 ? C_AMO : ex;
    ex_cmplx_amo = ex inside {12, 13} ? '1 : '0;
    #1;
    if (ir_context[0] !== (ir0 inside {8, 17} ? IR_EMPTY :
                           ir_context_e'(ir0 == 16 ? 0 : ir0)) ||
        ir_context[1] !== (ir1 inside {8, 17} ? IR_EMPTY :
                           ir_context_e'(ir1 == 16 ? 0 : ir1)) ||
        !ir_enabled(int'(ir_context[0])) || !ir_enabled(int'(ir_context[1])))
      $fatal(1, "pipeline tap mismatch: %0d/%0d -> %0d/%0d",
             ir0, ir1, ir_context[0], ir_context[1]);
    if (ir_cmplx_amo !== {ir1 == 16, ir0 == 16})
      $fatal(1, "invalid or incorrectly ordered AMO qualification");
    if (ir_err !== (ir_valid & mask[2:1]) ||
        special_event !== {mask[4:3], (ir_valid & mask[2:1]), mask[0]})
      $fatal(1, "per-slot error qualification mismatch");
    tick();
  endtask
  initial begin
    // Exercise the full M-extension decode, including decoded faults.
    for (int funct3 = 0; funct3 < 8; funct3++) begin
      ir_dec_t d;
      d = '0;
      d.pl_type = PL_MULT;
      d.insn = 32'h02000033 | (32'(funct3) << 12);
      d.any_err = 1;
      if (classify_ir(d, 1) != (funct3 < 4 ? IR_MULT : IR_DIV) ||
          classify_ir(d, 0) != IR_EMPTY)
        $fatal(1, "M-extension classification mismatch");
      d.pl_type = PL_ALU;
      if (classify_ir(d, 1) != IR_ALU) $fatal(1, "pipeline override mismatch");
      d.pl_type = PL_MULT;
      d.insn[6:0] = OPCODE_CHERI;
      if (classify_ir(d, 1) != IR_MULT) $fatal(1, "CHERI classified as DIV");
      d.insn[6:0] = OPCODE_OP;
      d.insn[31:25] = 0;
      if (classify_ir(d, 1) != IR_MULT) $fatal(1, "non-M instruction classified as DIV");
    end
    sample_context(31, 16, 17, 0, 0, 12); // Reset must contribute no hits.
    rst_ni = 1;
    for (int mode = 0; mode <= int'(CHERIoTEn); mode++)
      for (int ordering = 0; ordering < 2; ordering++) begin
        pmode = mode;
        ira_is0 = ordering;
        if ($test$plusargs("exhaustive")) begin
          for (int mask = 0; mask < 32; mask++)
            foreach (ir_states[ir0])
              foreach (ir_states[ir1])
                for (int s0 = 0; s0 < 2; s0++)
                  for (int s1 = 0; s1 < 2; s1++)
                    foreach (ex_states[ex])
                      sample_context(mask, ir_states[ir0], ir_states[ir1],
                                     s0 == 0 ? 0 : 31, s1 == 0 ? 0 : 31, ex_states[ex]);
        end else begin
          for (int mask = 0; mask < 32; mask++)
            sample_context(mask, 1, 2, 0, 0, 0);
        end
      end
    rst_ni = 0;
    sample_context(31, 16, 17, 0, 0, 12);
    if (ir_enabled(6) || ir_enabled(7) || ir_enabled(10))
      $fatal(1, "invalid pipeline encoding accepted");
    ir_valid = 0;
    logical_dec[0].pl_type = pl_type_e'('x);
    logical_dec[1].pl_type = pl_type_e'('x);
    #1;
    if (ir_context[0] !== IR_EMPTY || ir_context[1] !== IR_EMPTY)
      $fatal(1, "invalid slots exposed stale pipeline values");
    $display("PASS context pipeline fixture");
    $finish;
  end
endmodule
"""


EVENTS = ("none", "irq", "ir0_err", "ir1_err", "debug", "commit_error")
STAGES = ("frontend", "alu0_wb", "alu1_wb", "lsif_req_dly", "lsu_req",
          "mult_ex2", "mult_wb")
IR_VALUES = (0, 1, 2, 3, 4, 5, 8, 9)
IR_STATES = IR_VALUES + (16, 17)  # AMO and stale AMO in an invalid slot.
CATEGORIES = {0: "category_C_ALU_RI", 31: "category_EMPTY", 11: "category_C_AMO"}


def ir_bin(state):
    value = 0 if state == 16 else 8 if state == 17 else state
    return "pipeline_IR_" + {0: "LOCAL", 1: "ALU", 2: "LS", 3: "MULT",
                              4: "JAL", 5: "JALR", 8: "EMPTY", 9: "DIV"}[value]


def events(mask):
    return ["none"] if mask == 0 else [
        name for bit, name in enumerate(EVENTS[1:]) if mask & (1 << bit)]


def observed_mask(mask, ir0, ir1):
    if ir0 in (8, 17):
        mask &= ~2
    if ir1 in (8, 17):
        mask &= ~4
    return mask


def samples(exhaustive):
    if exhaustive:
        yield from product(range(32), IR_STATES, IR_STATES,
                           (0, 31), (0, 31), (0, 31, 11, 12, 13))
    else:
        for mask in range(32):
            yield mask, 1, 2, 0, 0, 0


def cross_key(frontend, ir0, ir1, event, s0, s1, ex):
    irs = (ir_bin(ir0), ir_bin(ir1), event)
    return ((CATEGORIES[s0], CATEGORIES[s1]) + irs if frontend else
            irs + (CATEGORIES[ex],))


def expected_cross(frontend, exhaustive, factor):
    result = Counter()
    for ir0, ir1, event, s0, s1, ex in product(
            IR_VALUES, IR_VALUES, EVENTS, (0, 31), (0, 31), CATEGORIES):
        if ir0 == 8 and (ir1 != 8 or event == "ir0_err"):
            continue
        if ir1 == 8 and event == "ir1_err":
            continue
        if frontend and s0 == 31 and s1 != 31:
            continue
        result[cross_key(frontend, ir0, ir1, event, s0, s1, ex)] = 0
    for mask, ir0, ir1, s0, s1, ex in samples(exhaustive):
        if not frontend and (ir0 == 16 or ir1 == 16 or ex in (12, 13)):
            continue
        for event in events(observed_mask(mask, ir0, ir1)):
            key = cross_key(frontend, ir0, ir1, event, s0, s1, 11 if ex in (12, 13) else ex)
            if key in result:
                result[key] += factor
    return dict(result)


def bins(body, name):
    return {label: int(count) for label, count in re.findall(
        r"^\s*(\w+(?:\[\d+\])?)\s+(\d+)\s+\d+\s+", point(body, name), re.M)}


def cross_bins(body, name, dimensions):
    parts = body.split(f"Summary for Cross {name}\n", 1)
    require(len(parts) == 2, ("missing cross", name))
    section = parts[1].split("Summary for ", 1)[0]
    axes = re.search(r"Samples crossed: ([^\n]+)", section)[1].split()
    domains = [set(bins(body, axis)) for axis in axes]
    require(len(domains) == dimensions, (name, axes))
    result = {}
    for line in section.splitlines():
        fields = re.findall(r"\[[^\]]+\]|\S+", line)
        if len(fields) < dimensions + 3:
            continue
        choices = []
        for field, domain in zip(fields[:dimensions], domains):
            values = domain if field == "*" else set(field.strip("[]").replace(",", " ").split())
            if not values or not values <= domain:
                break
            choices.append(values)
        if len(choices) != dimensions:
            continue
        count = fields[dimensions]
        require(count == "--" or count.isdigit(), ("bad cross count", line))
        keys = list(product(*choices))
        if count == "--":
            require(int(fields[dimensions + 2]) == len(keys), ("compressed holes", line))
        for key in keys:
            require(key not in result, ("duplicate cross bin", key))
            result[key] = 0 if count == "--" else int(count)
    return result


def check(root):
    for hardware, scenario in product((0, 1), ("marginal", "exhaustive")):
        work = root / f"hw{hardware}" / scenario
        log = (work / "simulation.log").read_text()
        require("PASS context pipeline fixture" in log, work)
        require(not re.search(r"(?:Error|Fatal)-", log), (work, log))
        report = (work / "report/grpinfo.txt").read_text()
        exhaustive = scenario == "exhaustive"
        factor = 2 * (hardware + 1)
        expected_points = {
            "cp_ir0": Counter({ir_bin(v): 0 for v in IR_VALUES}),
            "cp_ir1": Counter({ir_bin(v): 0 for v in IR_VALUES}),
            "cp_special_event": Counter({name: 0 for name in EVENTS}),
            "cp_special_event_value": Counter({f"mask_{v:02x}": 0 for v in range(32)}),
            "cp_ex_resident": Counter({name: 0 for name in CATEGORIES.values()}),
        }
        for mask, ir0, ir1, s0, s1, ex in samples(exhaustive):
            mask = observed_mask(mask, ir0, ir1)
            expected_points["cp_ir0"][ir_bin(ir0)] += factor
            expected_points["cp_ir1"][ir_bin(ir1)] += factor
            expected_points["cp_special_event_value"][f"mask_{mask:02x}"] += factor
            expected_points["cp_ex_resident"][CATEGORIES[11 if ex in (12, 13) else ex]] += factor
            for event in events(mask):
                expected_points["cp_special_event"][event] += factor
        for stage in STAGES:
            body = instance(report, f"FC_MA_CONTEXT.{stage}")
            frontend = stage == "frontend"
            for name, expected in expected_points.items():
                if frontend and name == "cp_ex_resident":
                    continue
                actual = bins(body, name)
                require(actual == dict(expected), (work, stage, name, actual, expected))
            name = "x_s0_ir_special" if frontend else "x_ir_special_ex"
            expected = expected_cross(frontend, exhaustive, factor)
            actual = cross_bins(body, name, 5 if frontend else 4)
            require(actual == expected, (work, stage, "cross mismatch",
                    "missing", list(expected.keys() - actual.keys())[:5],
                    "extra", list(actual.keys() - expected.keys())[:5],
                    "counts", [(k, actual[k], expected[k]) for k in actual.keys() &
                               expected.keys() if actual[k] != expected[k]][:5]))
            rows = row_map(body)
            require(set(rows) == ({"cp_s0_rdata0", "cp_s0_rdata1"} if frontend else
                    {"cp_ex_resident"}) |
                    {"cp_ir0", "cp_ir1", "cp_special_event", "cp_special_event_value", name},
                    (work, stage, "unexpected cross or point"))
            require(int(rows[name][0]) == len(expected), (work, stage, "cross denominator"))
        print(f"PASS hardware={hardware} {scenario}: eight IR bins, logical taps, "
              "event counts and all retained/excluded cross goals", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.check:
        check(args.check.resolve())
        return
    sim = Path(__file__).resolve().parent.parent
    os.chdir(sim)
    root = (Path("temp") / ("context_events_" + uuid.uuid4().hex[:12])).resolve()
    root.mkdir(parents=True, exist_ok=False)
    scratch = root / "tool_scratch"
    scratch.mkdir()
    os.environ["TMPDIR"] = str(scratch)
    print(f"Artifacts: {root}", flush=True)
    text = (sim / "fcov/kudu_fcov_context.sv").read_text()
    (root / "fixture.sv").write_text(fixture(text))
    rtl = sim.parent / "rtl"
    for hardware in (0, 1):
        build = root / f"hw{hardware}"
        build.mkdir()
        run(["submit", "-i", "vcs", "-full64", "-sverilog", "-timescale=1ns/1ps",
             "-top", "kudu_top", *(["+define+CHERIoT"] if hardware else []),
             "-cm", "line+assert", "-o", "simv",
             *[rtl / name for name in ("cheri_pkg.sv", "csr_pkg.sv", "super_pkg.sv")],
             root / "fixture.sv"], build, "compile.log")
        for scenario in ("marginal", "exhaustive"):
            work = build / scenario
            work.mkdir()
            run(["submit", "-i", build / "simv", f"+{scenario}",
                 "-cm", "line+assert", "-cm_dir", work / "run.vdb", "-cm_name", scenario],
                work, "simulation.log")
            run(["submit", "-i", "urg", "-full64", "-dir", build / "simv.vdb",
                 work / "run.vdb", "-report", work / "report", "-format", "both",
                 "-show", "tests"], work, "urg.log")
    check(root)
    print(f"Native context validation complete: {root}", flush=True)


if __name__ == "__main__":
    main()
