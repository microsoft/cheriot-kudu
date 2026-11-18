"""Small source-checker regressions; run python -m unittest discover -s sim/fcov."""
import contextlib
import io
import os
import shlex
import unittest
from unittest import mock

import check_binds
import check_syntax
import count_cov


class BindParserTests(unittest.TestCase):
    def test_nested_expressions_and_strings(self):
        text = '''bind top cov #(.Name("x)y"), .N(f(g(2)))) tap (
          .data(4'(unsigned'($countones(child.valid_q)))),
          .flag(child.flags.ready), .literal(1'b0), .*
        );'''
        problems = []
        binds = list(check_binds.parse_binds(text, {}, problems))
        self.assertEqual(problems, [])
        self.assertEqual([p for p, _, _ in binds[0][2]], ["data", "flag", "literal"])
        self.assertEqual(binds[0][2][0][1], "4'(unsigned'($countones(child.valid_q)))")
        self.assertEqual(binds[0][2][0][2], 2)

    def test_unresolved_target_is_reported(self):
        problems = []
        self.assertEqual(list(check_binds.parse_binds(
            "bind top.missing cov tap (.x(x));", {}, problems)), [])
        self.assertIn("cannot resolve bind target", problems[0])

    def test_bad_root_is_not_a_struct_field(self):
        mods = {
            "top": "module top; child child_i (); endmodule",
            "child": "module child;\nlogic flag;\nendmodule",
        }
        for signal, expected in (("flag", 0), ("typo", 1)):
            text = "bind top cov tap (.x(child_i.%s), .zero(1'b0));" % signal
            with mock.patch.object(check_binds, "module_bodies", return_value=mods), \
                    mock.patch.object(check_binds, "package_symbols", return_value=set()), \
                    mock.patch("builtins.open", mock.mock_open(read_data=text)), \
                    contextlib.redirect_stdout(io.StringIO()):
                # Put the instantiation on its own line, as in the RTL.
                mods["top"] = "module top;\nchild child_i ();\nendmodule"
                self.assertEqual(check_binds.main(), expected)


class CensusTests(unittest.TestCase):
    def test_inline_auto_cross_and_bin_declarations(self):
        text = '''
          // covergroup fake; cp: coverpoint dummy; endgroup
          covergroup cg;
            option.name = "FC_TEST";
            a: coverpoint bit_a; b: coverpoint bit_b { option.weight = 0; }
            c: coverpoint pair { bins each[] = {[0:3]};
              wildcard bins one = {2'b1?}; illegal_bins bad = {4}; }
            xy: cross a, b { bins both = binsof(a) && binsof(b);
                            ignore_bins unused = binsof(a); }
          endgroup
          cg instance0 = new();
          bind top cov instance_cov (.*);
          bind top.child cov instance_cov2 (.*);
        '''
        rows, binds = count_cov.census([text])
        row = rows["FC_TEST"]
        self.assertEqual([row[k] for k in ("types", "new_decls", "cps", "auto_cps",
                                           "crosses", "bins", "illegal_bins", "ignore_bins")],
                         [1, 1, 3, 2, 1, 3, 1, 1])
        self.assertEqual(binds["cov"], 2)


class FileListTests(unittest.TestCase):
    def test_new_modules_are_accepted_in_list_order(self):
        text = """$verifRoot/fcov/kudu_fcov_pkg.sv
                  $verifRoot/fcov/new_context.sv
                  $verifRoot/fcov/kudu_fcov_bind.sv"""
        with mock.patch("builtins.open", mock.mock_open(read_data=text)), \
                mock.patch.object(os.path, "isfile", return_value=True):
            paths = check_syntax.coverage_sources()
        self.assertEqual([os.path.basename(p) for p in paths],
                         ["kudu_fcov_pkg.sv", "new_context.sv", "kudu_fcov_bind.sv"])

    def test_bind_must_remain_last(self):
        with mock.patch("builtins.open", mock.mock_open(
                read_data="$verifRoot/fcov/kudu_fcov_bind.sv\n$verifRoot/fcov/new.sv")), \
                mock.patch.object(os.path, "isfile", return_value=True):
            with self.assertRaisesRegex(ValueError, "must be last"):
                check_syntax.coverage_sources()

    def test_matrix_passes_configuration_and_feature_modes(self):
        with mock.patch("sys.argv", ["check_syntax.py", "--matrix"]), \
                mock.patch.object(check_syntax, "rtl_sources", return_value=[]), \
                mock.patch.object(check_syntax, "coverage_sources", return_value=[]), \
                mock.patch.object(check_syntax, "elaborate", return_value=0) as elaborate:
            self.assertEqual(check_syntax.main(), 0)
        self.assertEqual([(c.args[0], c.args[1]) for c in elaborate.call_args_list],
                         [(cfg, mode) for cfg in check_syntax.CONFIGS for mode in (True, False)])


class ElaborationTests(unittest.TestCase):
    def test_branch_observation_mapping_and_sampling(self):
        try:
            import pyslang
            from pyslang import driver
        except ImportError:
            self.skipTest("pyslang is not installed")

        widths = {
            "cp_kind": 3, "cp_mapping": 1, "cp_issued": 1,
            "cp_branch_outcome": 4, "cp_compare_operands": 3,
            "cp_branch_direction": 2, "cp_branch_prediction": 2,
            "cp_mispredict": 4,
            "cp_jalr_prediction": 2, "cp_jalr_target_low": 2,
            "cp_jalr_immediate": 12, "cp_cjalr_errors": 3,
        }
        for config in ("KuduCfg1", "KuduCfg2"):
            for cheriot in (False, True):
                with self.subTest(config=config, cheriot=cheriot):
                    d = driver.Driver()
                    d.addStandardArgs()
                    args = ["slang", "-DRVFI=1", "--top", "kudu_top",
                            "-GCFG=kudu_cfg_pkg::" + config,
                            "-GCHERIoTEn=%d" % cheriot]
                    if cheriot:
                        args.append("-DCHERIoT=1")
                    args += check_syntax.rtl_sources() + check_syntax.coverage_sources()
                    self.assertTrue(d.parseCommandLine(shlex.join(args)))
                    self.assertTrue(d.processOptions())
                    self.assertTrue(d.parseAllSources())
                    comp = d.createCompilation()
                    comp.getAllDiagnostics()
                    assignments = [{}, {}]
                    points = [{}, {}]
                    groups = {}

                    def visit(node):
                        if isinstance(node, pyslang.ast.Symbol) and node.parentScope is not None \
                                and node.parentScope.isUninstantiated:
                            return
                        if isinstance(node, pyslang.ast.ContinuousAssignSymbol) and isinstance(
                                node.assignment, pyslang.ast.AssignmentExpression):
                            symbol = node.assignment.left.getSymbolReference()
                            if symbol is not None and ".u_fcov_branch_unit.gen_slot[" in symbol.hierarchicalPath:
                                self.assertIn(".branch_unit_i.", symbol.hierarchicalPath)
                                slot = int(symbol.hierarchicalPath.split(".gen_slot[")[1][0])
                                assignments[slot][symbol.name] = (symbol, node.assignment.right)
                        elif isinstance(node, pyslang.ast.CoverpointSymbol) and (
                                ".u_fcov_branch_unit.gen_slot[" in node.hierarchicalPath):
                            self.assertIn(".branch_unit_i.", node.hierarchicalPath)
                            slot = int(node.hierarchicalPath.split(".gen_slot[")[1][0])
                            points[slot][node.name] = node
                        elif isinstance(node, pyslang.ast.CovergroupType) and (
                                ".u_fcov_branch_unit.gen_slot[" in node.hierarchicalPath):
                            slot = int(node.hierarchicalPath.split(".gen_slot[")[1][0])
                            groups[slot] = node

                    comp.getRoot().visit(visit)
                    self.assertEqual(set(groups), {0, 1})

                    for slot in range(2):
                        self.assertIn("@(posedgeclk_iiff(rst_ni&&eval_valid))",
                                      "".join(str(groups[slot].syntax).split()))
                        self.assertEqual({n: p.type.bitWidth for n, p in points[slot].items()}, widths)
                        observed = assignments[slot]
                        branch = ""  # branch-unit signals are ports of the monitor
                        issuer = "kudu_top.issuer_i."
                        expected = {
                            "dec": "((Slot == 0) == %sira_is0_i) ? %sira_dec_i : %sirb_dec_i"
                                   % (branch, branch, branch),
                            "resolved_data": (
                                "((Slot == 0) == %sira_is0_i) ? %sira_full_data2_i : %sirb_full_data2_i"
                                % (branch, branch, branch)),
                            "eval_valid": (
                                "%sctrl_fsm_cs[CSM_DECODE] && %sir_valid_i[Slot] && "
                                "!%sir_hazard[Slot] && !%scmt_err_i && !dec.any_err && "
                                "(dec.is_branch || dec.is_jal || dec.is_jalr)"
                                % (issuer, issuer, issuer, issuer)),
                            "issued": "Slot == 0 ? %sir0_issued : %sir1_issued" % (issuer, issuer),
                            "taken": branch + "branch_info_o.branch_taken[Slot]",
                            "mispredict": "{%s}" % ", ".join(
                                branch + "branch_info_o." + name + "[Slot]"
                                for name in ("mis_jalr", "mis_jal", "mis_not_taken", "mis_taken")),
                            "jalr_target": "Slot == 0 ? %sir0_jalr_target_o : %sir1_jalr_target_o"
                                           % (branch, branch),
                            "cjalr_errors": "Slot == 0 ? %sir0_cjalr_err_o : %sir1_cjalr_err_o"
                                            % (branch, branch),
                        }
                        self.assertEqual(set(observed), set(expected))
                        # Lock the sampling policy and physical/ordered correspondence;
                        # hierarchy expressions cannot be constant-evaluated by pyslang.
                        for name, syntax in expected.items():
                            self.assertEqual("".join(str(observed[name][1].syntax).split()),
                                             "".join(syntax.split()))
                        mask = points[slot]["cp_cjalr_errors"].find("mask")
                        self.assertTrue(mask.isArray)
                        self.assertEqual([
                            int(e.eval(pyslang.ast.EvalContext(points[slot]["cp_cjalr_errors"])).value)
                            for e in (mask.values[0].left, mask.values[0].right)], [0, 7])

    def check_register_coverpoint(self, node, slot, source, port):
        import pyslang

        comparison = source is not None and port is not None
        self.assertEqual(node.type.bitWidth, 1 if comparison else 5)
        if comparison:
            for name, value in (("different", 0), ("same", 1)):
                b = node.find(name)
                self.assertEqual(b.binsKind, pyslang.ast.CoverageBinSymbol.Bins)
                self.assertEqual(len(b.values), 1)
                self.assertEqual(int(b.values[0].eval(
                    pyslang.ast.EvalContext(node)).value), value)
        else:
            b = node.find("reg_")
            self.assertTrue(b.isArray)
            self.assertEqual(b.binsKind, pyslang.ast.CoverageBinSymbol.Bins)
            self.assertEqual(len(b.values), 1)
            bounds = b.values[0]
            self.assertEqual([int(e.eval(pyslang.ast.EvalContext(node)).value)
                              for e in (bounds.left, bounds.right)], [0, 31])

        def evaluate(address, write_address, valid=3, ren=3, we=1):
            values = {}
            if source is not None:
                dec_name = ("ira_dec_o", "irb_dec_o")[slot]
                dec_type = node.lookupName(dec_name).type.canonicalType
                values[dec_name] = (
                    (address << dec_type.find("rs%d" % source).bitOffset) |
                    (ren << dec_type.find("rf_ren").bitOffset))
                values["ir_valid_o"] = valid
            if port is not None:
                values["rf_waddr%d_i" % port] = write_address
                values["rf_we%d_i" % port] = we
            context = pyslang.ast.EvalContext(node)
            context.pushEmptyFrame()
            for name, value in values.items():
                symbol = node.lookupName(name)
                context.createLocal(symbol, pyslang.ConstantValue(
                    pyslang.SVInt("%d'h%x" % (symbol.type.bitWidth, value))))
            result = (int(node.coverageExpr.eval(context).value),
                      int(node.iffExpr.eval(context).value))
            self.assertEqual(len(context.diagnostics), 0)
            return result

        for address in range(32):
            for write_address in (address, (address + 1) % 32):
                expected = int(address == write_address) if comparison else (
                    address if source is not None else write_address)
                self.assertEqual(evaluate(address, write_address), (expected, 1))
        for valid in range(4) if source is not None else (0,):
            for ren in range(4) if source is not None else (0,):
                for we in (0, 1) if port is not None else (1,):
                    enabled = bool(we) if port is not None else True
                    if source is not None:
                        enabled &= bool(valid & (1 << slot)) and bool(ren & (1 << (source - 1)))
                    self.assertEqual(evaluate(17, 17, valid, ren, we)[1], int(enabled))

    def test_actual_discard_count_and_fsm_widths(self):
        try:
            import pyslang
            from pyslang import driver
        except ImportError:
            self.skipTest("pyslang is not installed")

        for config, depth in (("KuduCfg1", 3), ("KuduCfg2", 2)):
            with self.subTest(config=config):
                d = driver.Driver()
                d.addStandardArgs()
                args = [
                    "slang", "-DRVFI=1", "-DCHERIoT=1", "--top", "kudu_top",
                    "-GCFG=kudu_cfg_pkg::" + config, "-GCHERIoTEn=1",
                    "-GUseDWMult=0", "-GRvfiDumpEn=1",
                ] + check_syntax.rtl_sources() + check_syntax.coverage_sources()
                self.assertTrue(d.parseCommandLine(shlex.join(args)))
                self.assertTrue(d.processOptions())
                self.assertTrue(d.parseAllSources())
                comp = d.createCompilation()
                comp.getAllDiagnostics()
                checked = set()
                register_points = {
                    "cp_rs%d_%d" % (source, slot): (slot, source, None)
                    for slot in range(2) for source in (1, 2)}
                register_points.update({
                    "cp_rf_waddr%d" % port: (None, None, port)
                    for port in range(3)})
                register_points.update({
                    "cp_rf_waddr%d_rs%d_%d" % (port, source, slot): (slot, source, port)
                    for slot in range(2) for source in (1, 2) for port in range(3)})
                checked_registers = set()
                checked_write_bindings = set()

                def visit(node):
                    if isinstance(node, pyslang.ast.InstanceSymbol) and node.name == "u_fcov_id":
                        for connection in node.portConnections:
                            name = connection.port.name
                            if name in ("rf_waddr0_i", "rf_waddr1_i", "rf_waddr2_i"):
                                expr = connection.expression
                                self.assertEqual(expr.type.bitWidth, 5)
                                self.assertEqual(
                                    expr.getSymbolReference().hierarchicalPath,
                                    node.hierarchicalPath.rsplit(".", 1)[0] + "." + name)
                                checked_write_bindings.add(name)
                    if not isinstance(node, pyslang.ast.CoverpointSymbol):
                        return
                    if node.name in register_points and ".u_fcov_id." in node.hierarchicalPath:
                        self.check_register_coverpoint(node, *register_points[node.name])
                        checked_registers.add(node.name)
                    expr = node.coverageExpr
                    if node.name == "cp_discard":
                        self.assertEqual(node.type.bitWidth, depth + 1)
                        self.assertIsInstance(expr, pyslang.ast.ConcatenationExpression)
                        self.assertEqual(
                            [(e.getSymbolReference().name, e.type.bitWidth)
                             for e in expr.operands],
                            [("branch_discard_q", depth), ("discard_req_q", 1)])
                        checked.add("discard")
                    elif node.name == "cp_fifo_occupancy":
                        self.assertEqual(node.type.bitWidth, 32)
                        checked.add("occupancy")
                    elif node.name in ("cp_err0", "cp_err1") and ".u_fcov_id." in node.hierarchicalPath:
                        self.assertEqual(node.type.bitWidth, 3)
                        for value, name in enumerate((
                                "none", "permission", "bounds", "illegal_instruction",
                                "illegal_compressed", "fetch", "multiple", "reserved")):
                            b = node.find(name)
                            self.assertIsInstance(b, pyslang.ast.CoverageBinSymbol)
                            self.assertEqual(
                                b.binsKind, pyslang.ast.CoverageBinSymbol.IllegalBins
                                if value == 7 else pyslang.ast.CoverageBinSymbol.Bins)
                            self.assertEqual(len(b.values), 1)
                            self.assertEqual(
                                int(b.values[0].eval(pyslang.ast.EvalContext(node)).value), value)
                        checked.add(node.name)
                    elif ".u_fcov_cmplx." in node.hierarchicalPath:
                        symbol = expr.getSymbolReference()
                        if symbol is not None and symbol.name == "cmplx_fsm_cs":
                            self.assertEqual(node.type.bitWidth, 2)
                            checked.add(symbol.name)
                            if node.name == "cp_transition":
                                checked.add("transition")

                comp.getRoot().visit(visit)
                self.assertEqual(checked, {
                    "discard", "occupancy", "cp_err0", "cp_err1",
                    "cmplx_fsm_cs", "transition"})
                self.assertEqual(checked_registers, set(register_points))
                self.assertEqual(checked_write_bindings, {
                    "rf_waddr0_i", "rf_waddr1_i", "rf_waddr2_i"})

    def test_error_classifier_all_raw_masks(self):
        try:
            import pyslang
        except ImportError:
            self.skipTest("pyslang is not installed")

        comp = pyslang.ast.Compilation()
        for name in ("cheri_pkg.sv", "csr_pkg.sv", "super_pkg.sv"):
            comp.addSyntaxTree(pyslang.syntax.SyntaxTree.fromFile(
                os.path.join(check_syntax.RTL, name)))
        comp.addSyntaxTree(pyslang.syntax.SyntaxTree.fromFile(
            os.path.join(check_syntax.FCOV, "kudu_fcov_pkg.sv")))
        declarations = [
            "localparam result%d = fcov_err_kind(ir_errs_t'(5'd%d));" % (mask, mask)
            for mask in range(32)]
        comp.addSyntaxTree(pyslang.syntax.SyntaxTree.fromText(
            "module error_category_fixture; import super_pkg::*; import kudu_fcov_pkg::*; "
            + " ".join(declarations) + " endmodule"))
        fixture = comp.getRoot().topInstances[0].body
        singles = {0: 0, 16: 1, 8: 2, 4: 3, 2: 4, 1: 5}
        for mask in range(32):
            with self.subTest(mask=mask):
                expected = singles.get(mask, 6)
                self.assertEqual(int(fixture.find("result%d" % mask).value.value), expected)

    def test_hierarchy_observations_allow_warnings_not_bad_paths(self):
        try:
            import pyslang
            from pyslang import driver
        except ImportError:
            self.skipTest("pyslang is not installed")

        for field, expected in (("signal_i", 0), ("missing", 1)):
            with self.subTest(field=field):
                compilation = pyslang.ast.Compilation()
                compilation.addSyntaxTree(pyslang.syntax.SyntaxTree.fromText(
                    "module kudu_top; logic signal_i; cov monitor(); endmodule "
                    "module cov; wire observed = kudu_top.%s; endmodule" % field,
                    name=os.path.join(check_syntax.FCOV, "hierarchy_fixture.sv")))
                fake_driver = mock.Mock()
                fake_driver.createCompilation.return_value = compilation
                with mock.patch.object(driver, "Driver", return_value=fake_driver), \
                        contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(check_syntax.elaborate("KuduCfg1", True, []), expected)

    def test_rtl_only_errors_fail(self):
        try:
            import pyslang
            from pyslang import driver
        except ImportError:
            self.skipTest("pyslang is not installed")

        compilation = pyslang.ast.Compilation()
        compilation.addSyntaxTree(pyslang.syntax.SyntaxTree.fromText(
            "module kudu_top; missing_module child(); endmodule",
            name="rtl_only_fixture.sv"))
        fake_driver = mock.Mock()
        fake_driver.createCompilation.return_value = compilation
        output = io.StringIO()
        with mock.patch.object(driver, "Driver", return_value=fake_driver), \
                contextlib.redirect_stdout(output):
            self.assertEqual(check_syntax.elaborate("KuduCfg1", True, []), 1)
        self.assertIn("total errors: 1", output.getvalue())
        self.assertIn("unknown module", output.getvalue())
        self.assertIn("fcov diagnostics: 0", output.getvalue())


if __name__ == "__main__":
    unittest.main()
