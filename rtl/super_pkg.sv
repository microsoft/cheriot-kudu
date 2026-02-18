// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package super_pkg;
  import cheri_pkg::*;

`ifdef CHERIoT
  parameter int unsigned MemW  = 65;
  parameter int unsigned RegW  = $bits(reg_cap_t);
  parameter int unsigned OpW   = $bits(op_cap_t);
  parameter int unsigned FullW = $bits(full_cap_t);
`else
  parameter int unsigned RegW  = 32;
  parameter int unsigned OpW   = 32;
  parameter int unsigned MemW  = 32;
  parameter int unsigned FullW = 32;
`endif

  typedef enum logic [2:0] {
    PL_LOCAL,
    PL_ALU,
    PL_LS,
    PL_MULT,
    PL_JAL,
    PL_JALR
  } pl_type_e;

  typedef struct packed {
    logic perm_vio;                // cheri permission violation
    logic bound_vio;               // cheri bound violation
    logic illegal_insn;
    logic illegal_c_insn;
    logic fetch_err;               // memory fetch error
  } ir_errs_t;

  typedef struct packed {
    logic [31:0] insn;
    logic [31:0] pc;
    ir_errs_t    errs;             
    logic        is_comp;          // instr is compressed 
    logic        is_branch;
    logic        is_jal;
    logic        is_jalr;
    logic [15:0] c_insn;           // for trace only
    logic        ptaken;
    logic [31:0] ptarget;
  } ir_reg_t;

  parameter ir_reg_t NULL_IR_REG = ir_reg_t'(0);

  typedef struct packed {
    logic valid;
    logic csrw;
    logic mret;
    logic dret;
    logic wfi;
    logic ecall;
    logic ebrk;
    logic cjalr;
    logic fencei;
  } sysctl_t;

  parameter sysctl_t NULL_SYSCTL = sysctl_t'(0);

  typedef struct packed {
    logic cscrrw;
    logic csetbounds;
    logic csetboundsimm;
    logic csetboundsex;
    logic csetboundsrndn;
    logic cseal;
    logic cunseal;
    logic candperm;
    logic csetaddr;
    logic cincaddr;
    logic cincaddrimm;
    logic csub;
    logic csethigh;
    logic ctestsub;
    logic cseteqx;
    logic cgetperm;
    logic cgettype;
    logic cgetbase;
    logic cgethigh;
    logic cgettop;
    logic cgetlen;
    logic cgettag;
    logic crrl;
    logic cram;
    logic cgetaddr;
    logic cmove;
    logic ccleartag;
    logic auipcc;      // do we need this one or just expand rv32 auipc
    logic auicgp;
    logic clc;
    logic csc;
  } cheri_op_t;

  typedef struct packed {
    logic [31:0] insn;
    logic [31:0] pc;
    logic        any_err;
    ir_errs_t    errs;   
    logic        is_comp;
    logic        is_branch;
    logic        is_jal;
    logic        is_jalr;
    logic        is_csr;
    pl_type_e    pl_type;  
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    logic [4:0]  rd;
    logic [1:0]  rf_ren;
    logic        rf_we;   
    logic [15:0] c_insn;          // for trace only
    logic        ptaken;
    logic [31:0] ptarget;
    logic [31:0] btarget;
    logic [31:0] pc_nxt;
    sysctl_t     sysctl;
    logic        is_cheri;
    cheri_op_t   cheri_op;
    logic        is_cmplx;
    logic        is_brkpt;
  } ir_dec_t;

  typedef struct packed {
    logic [4:0]  pl;
    logic [31:0] pc;              // for simulation debug only
  } sbd_fifo_t;

  typedef struct packed {
    logic [4:0] a0;
    logic [4:0] a1;
  } rf_raddr2_t;

  typedef struct packed {
    logic [RegW-1:0] d0;
    logic [RegW-1:0] d1;
  } rf_rdata2_t;

  typedef struct packed {
    logic [OpW-1:0] d0;
    logic [OpW-1:0] d1;
  } op_data2_t;

  typedef struct packed {
    logic [FullW-1:0] d0;
    logic [FullW-1:0] d1;
  } full_data2_t;

  typedef struct packed {
    logic            we;
    logic            wrsv;
    logic [4:0]      waddr;
    logic [RegW-1:0] wdata;
    logic [31:0]     pc;
    logic            err;
    logic [5:0]      mcause;
    logic [31:0]     mtval;
    logic            is_cap;
  } pl_out_t;

  typedef struct packed {
    logic [1:0]     valid;
    logic [4:0]     addr0;
    logic [4:0]     addr1;
    logic [OpW-1:0] data0;
    logic [OpW-1:0] data1;
  } pl_fwd_t;

  parameter pl_fwd_t NULL_PL_FWD = pl_fwd_t'(0); 

  typedef struct packed {
    logic [1:0]  valid;
    logic [4:0]  rd0;
    logic [4:0]  rd1;
  } waw_act_t;

  typedef struct packed {
    logic               is_csr;
    logic               is_load;
    logic               is_cap;
    logic [3:0]         amo_flag;  // amo1, amo0, sc, lr             
    logic               cheri_err;
    logic               align_err_only;
    logic [4:0]         cheri_cause;    
    logic [1:0]         data_type;    
    logic [3:0]         clrperm;
    logic               sign_ext;
    logic [MemW-1:0]    wdata;     // only used in LS case
    logic [31:0]        addr;
    logic               rf_we;
    logic [4:0]         rs1;
    logic [4:0]         rd;
    logic [31:0]        insn;          
    logic [31:0]        pc;
    logic               early_load;
    logic               cache_ok;
    logic               cs2_valid;
    logic [PERMS_W-1:0] cs2_perms;
    logic [FullW-1:0]   cs1_fcap;
  } lsu_req_info_t;

  parameter lsu_req_info_t NULL_LSU_REQ_INFO = lsu_req_info_t'(0);

  typedef struct packed {
    logic [1:0]  mispredict_taken;
    logic [1:0]  mispredict_not_taken;
    logic [1:0]  branch_taken;
  } branch_info_t;

  typedef struct packed {
    logic [1:0]  is_branch;
    logic [1:0]  is_jal;
    logic [1:0]  taken;
    logic [31:0] pc0;
    logic [31:0] pc1;
    logic [31:0] target0;
    logic [31:0] target1;
  } ex_bp_info_t;

  typedef struct packed {
    logic [31:0] pc;
    logic [5:0]  mcause;
    logic [31:0] mtval;
  } cmt_err_info_t;

  parameter cmt_err_info_t NULL_CMT_ERR_INFO = cmt_err_info_t'(0);

  typedef enum logic [6:0] {
    OPCODE_LOAD     = 7'h03,
    OPCODE_MISC_MEM = 7'h0f,
    OPCODE_OP_IMM   = 7'h13,
    OPCODE_AUIPC    = 7'h17,
    OPCODE_STORE    = 7'h23,
    OPCODE_AMO      = 7'h2f,
    OPCODE_OP       = 7'h33,
    OPCODE_LUI      = 7'h37,
    OPCODE_BRANCH   = 7'h63,
    OPCODE_JALR     = 7'h67,
    OPCODE_JAL      = 7'h6f,
    OPCODE_SYSTEM   = 7'h73,
    OPCODE_CHERI    = 7'h5b,
    OPCODE_AUICGP   = 7'h7b
  } opcode_e;

  ////////////////////
  // ALU operations //
  ////////////////////

  typedef enum logic [6:0] {
    // Arithmetics
    ALU_ADD,
    ALU_SUB,

    // Logics
    ALU_XOR,
    ALU_OR,
    ALU_AND,

    // Shifts
    ALU_SRA,
    ALU_SRL,
    ALU_SLL,

    // Set lower than
    ALU_SLT,
    ALU_SLTU,

    // RV32B zba
    ALU_SH1ADD,
    ALU_SH2ADD,
    ALU_SH3ADD,
 
    // RV32B zbb
    ALU_XNOR,
    ALU_ORN,
    ALU_ANDN,
    ALU_CLZ,
    ALU_CTZ,
    ALU_CPOP,
    ALU_MAX,
    ALU_MAXU,
    ALU_MIN,
    ALU_MINU,
    ALU_SEXTB,
    ALU_SEXTH,
    ALU_ZEXTH,
    ALU_ROL,
    ALU_ROR,
    ALU_ORCB,
    ALU_REV8,
 
    // RV32B zbc
    ALU_CLMUL,
    ALU_CLMULH,
    ALU_CLMULR,

    // RV32B zbs
    ALU_BCLR,
    ALU_BSET,
    ALU_BINV,
    ALU_BEXT

  } alu_op_e;
 
  typedef enum logic [1:0] {
    // Multiplier/divider
    MD_OP_MULL,
    MD_OP_MULH,
    MD_OP_DIV,
    MD_OP_REM
  } md_op_e;

 // Operand a selection
  typedef enum logic[1:0] {
    OP_A_REG_A,
    OP_A_FWD,
    OP_A_CURRPC,
    OP_A_IMM
  } op_a_sel_e;

  // Immediate a selection
  typedef enum logic {
    IMM_A_Z,
    IMM_A_ZERO
  } imm_a_sel_e;

  // Operand b selection
  typedef enum logic {
    OP_B_REG_B,
    OP_B_IMM
  } op_b_sel_e;

  // Immediate b selection
  typedef enum logic [2:0] {
    IMM_B_I,
    IMM_B_S,
    IMM_B_B,
    IMM_B_U,
    IMM_B_J,
    IMM_B_INCR_PC,
    IMM_B_INCR_ADDR,
    IMM_B_C20
  } imm_b_sel_e;

  typedef enum logic [3:0] {
    CSM_RESET          = 4'h0,
    CSM_BOOT_SET       = 4'h1,
    CSM_DECODE         = 4'h2,
    CSM_CMT_FLUSH      = 4'h3,
    CSM_WAIT_TRVK      = 4'h4,
    CSM_GO_SPECIAL     = 4'h5,
    CSM_WAIT_CMT0      = 4'h6,
    CSM_WAIT_CMT1      = 4'h7,
    CSM_ISSUE_SPECIAL  = 4'h8,
    CSM_WAIT_FINAL     = 4'h9,
    CSM_WAIT_CMPLX     = 4'ha,
    CSM_SLEEP          = 4'hb
  } ctrl_fsm_e;     

  typedef enum logic [2:0] {NULL, EXEC, SYSCTL, ICJALR, CMPLX, IRQ, DEBUG} special_case_e;

  typedef enum logic [2:0]  {
    IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT,
    WAIT_RVALID_MIS_GNTS_DONE
  } ls_fsm_e;

  //typedef enum logic [2:0] {CRX_IDLE, CRX_WAIT_RESP} cap_rx_fsm_t;


endpackage
