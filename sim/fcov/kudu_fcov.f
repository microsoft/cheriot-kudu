// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Functional coverage model for cheriot-kudu.
// Implements doc/functional_coverage_plan.md.
//
// Compile after the RTL: every module here is bound into the DUT, and
// kudu_fcov_bind.sv must come last.
//
// Define KUDU_FCOV_OFF to disable the coverage modules and their binds.

$verifRoot/fcov/kudu_fcov_pkg.sv
$verifRoot/fcov/kudu_fcov_isa.sv
$verifRoot/fcov/kudu_fcov_csr.sv
$verifRoot/fcov/kudu_fcov_if.sv
$verifRoot/fcov/kudu_fcov_id.sv
$verifRoot/fcov/kudu_fcov_issue.sv
$verifRoot/fcov/kudu_fcov_ex.sv
$verifRoot/fcov/kudu_fcov_context.sv
$verifRoot/fcov/kudu_fcov_lsu.sv
$verifRoot/fcov/kudu_fcov_cmt.sv
$verifRoot/fcov/kudu_fcov_top.sv
$verifRoot/fcov/kudu_fcov_bind.sv
