// Copyright Microsoft Corporation 
// Licensed under the Apache License, Version 2.0, see LICENSE for details. 
// SPDX-License-Identifier: Apache-2.0
package kudu_cfg_pkg;

  // Pipeline stage configuration:
  //   1: 5-stage total, 1-0-1, InstrRdataBypass : 0, IrStageBypass : 01
  //   2: 4-stage total, 0-1-0, InstrRdataBypass : 1, IrStageBypass : 10
  //   3: 6-stage total, 1-1-1, InstrRdataBypass : 0, IrStageBypass : 00

  typedef struct packed {
    // bit        CHERIoTEn;
    bit        DCacheEn;
    bit [31:0] HeapBase;
    bit [31:0] TSMapSize;
    bit [31:0] DmHaltAddr;
    bit [31:0] DmExcAddr;
    bit        DbgTriggerEn;
    bit [31:0] BrkptNum;

    bit        DualIssue;
    bit        EarlyLoad;
    bit        UnalignedFetch;
    bit        RV32M;
    bit        RV32B;
    bit        RV32A;

    bit        IfRdataBypass;
    bit [1:0]  IrStageBypass;
    bit        IfCompDecEn;
    bit        IrCompDecEn;
    bit [31:0] IrS0Depth;

    bit        PredictUseBtb;
    bit        PredictIbufEn;
    bit [31:0] PredictBhtSize;
    bit        PredictRA;
    bit [20:0] RALimitHi;
    bit [20:0] RALimitLo;

    bit [31:0] PrefetchDepth;
    bit        AltEnable;
    bit        CJALRErrEn;
  } kudu_cfg_t;

  // 5-stage pipeline configuration
  parameter kudu_cfg_t KuduCfg1 = '{
    DCacheEn       : 1'b1,
    HeapBase       : 32'h8000_0000,
    TSMapSize      : 1024,
    DmHaltAddr     : 32'h84000000,
    DmExcAddr      : 32'h84000008,
    DbgTriggerEn   : 1'b1,
    BrkptNum       : 2,
    DualIssue      : 1'b1,
    EarlyLoad      : 1'b1,
    UnalignedFetch : 1'b0,
    RV32M          : 1'b1,
    RV32B          : 1'b1,
    RV32A          : 1'b1,
    IfRdataBypass  : 1'b0,
    IrStageBypass  : 2'b01,       
    IfCompDecEn    : 1'b0,
    IrCompDecEn    : 1'b1,
    PredictUseBtb  : 1'b0,
    PredictIbufEn  : 1'b0,
    PredictBhtSize : 32, 
    PredictRA      : 1'b1,
    RALimitHi      : 21'h080040,  
    RALimitLo      : 21'h080000,
    PrefetchDepth  : 3,
    IrS0Depth      : 4,
    AltEnable      : 1'b1,
    CJALRErrEn     : 1'b1
  };

  // 5-stage pipeline configuration
  parameter kudu_cfg_t KuduCfg1x = '{
    DCacheEn       : 1'b1,
    HeapBase       : 32'h8000_0000,
    TSMapSize      : 1024,
    DmHaltAddr     : 32'h84000000,
    DmExcAddr      : 32'h84000008,
    DbgTriggerEn   : 1'b1,
    BrkptNum       : 2,
    DualIssue      : 1'b1,
    EarlyLoad      : 1'b1,
    UnalignedFetch : 1'b0,
    RV32M          : 1'b1,
    RV32B          : 1'b1,
    RV32A          : 1'b1,
    IfRdataBypass  : 1'b0,
    IrStageBypass  : 2'b01,       
    IfCompDecEn    : 1'b0,
    IrCompDecEn    : 1'b1,
    PredictUseBtb  : 1'b0,
    PredictIbufEn  : 1'b0,
    PredictBhtSize : 32, 
    PredictRA      : 1'b1,
    RALimitHi      : 21'h080040,  
    RALimitLo      : 21'h080000,
    PrefetchDepth  : 3,
    IrS0Depth      : 4,
    AltEnable      : 1'b1,
    CJALRErrEn     : 1'b0   // disable CJALR errors (not compatible with CHERIoT 1.0)
  };

  // 4-stage pipeline configuration
  parameter kudu_cfg_t KuduCfg2 = '{
    DCacheEn       : 1'b1,
    HeapBase       : 32'h8000_0000,
    TSMapSize      : 1024,
    DmHaltAddr     : 32'h84000000,
    DmExcAddr      : 32'h84000008,
    DbgTriggerEn   : 1'b1,
    BrkptNum       : 2,
    DualIssue      : 1'b1,
    EarlyLoad      : 1'b1,
    UnalignedFetch : 1'b0,
    RV32M          : 1'b1,
    RV32B          : 1'b1,
    RV32A          : 1'b1,
    IfRdataBypass  : 1'b1,
    IrStageBypass  : 2'b10,       
    IfCompDecEn    : 1'b1,
    IrCompDecEn    : 1'b0,
    PredictUseBtb  : 1'b1,         // use table lookup insteand of compute target address for timing
    PredictIbufEn  : 1'b0,
    PredictBhtSize : 16,           // smaller BHT table to help timing 
    PredictRA      : 1'b1,
    RALimitHi      : 21'h080040,  
    RALimitLo      : 21'h080000,
    PrefetchDepth  : 2,
    IrS0Depth      : 2,
    AltEnable      : 1'b0,         // Lowwer branch overhead in 4-stage configuration 
    CJALRErrEn     : 1'b1
  };

  // 6-stage pipeline configuration
  parameter kudu_cfg_t KuduCfg3 = '{
    DCacheEn       : 1'b1,
    HeapBase       : 32'h8000_0000,
    TSMapSize      : 1024,
    DmHaltAddr     : 32'h84000000,
    DmExcAddr      : 32'h84000008,
    DbgTriggerEn   : 1'b1,
    BrkptNum       : 2,
    DualIssue      : 1'b1,
    EarlyLoad      : 1'b1,
    UnalignedFetch : 1'b0,
    RV32M          : 1'b1,
    RV32B          : 1'b1,
    RV32A          : 1'b1,
    IfRdataBypass  : 1'b0,
    IrStageBypass  : 2'b00,       
    IfCompDecEn    : 1'b0,
    IrCompDecEn    : 1'b1,
    PredictUseBtb  : 1'b0,
    PredictIbufEn  : 1'b0,
    PredictBhtSize : 32, 
    PredictRA      : 1'b1,
    RALimitHi      : 21'h080040,  
    RALimitLo      : 21'h080000,
    PrefetchDepth  : 3,
    IrS0Depth      : 4,
    AltEnable      : 1'b1,
    CJALRErrEn     : 1'b1
  };
endpackage
