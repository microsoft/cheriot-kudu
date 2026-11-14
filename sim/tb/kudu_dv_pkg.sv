// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package kudu_dv_pkg;
 // import cheri_pkg::*;

  parameter logic [31:0] DRAMStartAddr  = 32'h8000_0000;
  parameter logic [31:0] TsMapStartAddr = 32'h8300_0000;

  typedef struct packed {
    logic [7:0]    flag;
    logic          is_cap;
    logic [3:0]    amo_flag;
    logic          we;
    logic [3:0]    be;
    logic [29:0]   addr32;
    logic [64:0]   wdata;
    logic [64:0]   rdata;
    logic          err;
    logic          sc_fail;
  } mem_cmd_t;

  typedef struct packed {
    logic  [3:0] instr_gnt_wmax;
    logic  [3:0] instr_resp_wmax;
    logic  [2:0] instr_err_rate;   
    logic [32:0] instr_err_addr;  // bit 32 == valid
 
    logic  [3:0] data_gnt_wmax;
    logic  [3:0] data_resp_wmax;
    logic  [2:0] data_err_rate;
    logic [32:0] data_err_addr;

    logic  [2:0] intr_rate;
    logic  [2:0] dbg_req_rate;
  } sys_cfg_t;

endpackage
