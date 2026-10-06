// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Shared types and helper functions for the Kudu functional coverage model.
// See doc/functional_coverage_plan.md.

package kudu_fcov_pkg;
  import super_pkg::*;

  // --------------------------------------------------------------------------
  // Instruction category (Appendix A of the coverage plan).
  //
  // Shared category axis for decode, execution and instruction-context
  // coverage. Simultaneous context crosses retain these detailed categories.
  //
  // Derived from saved decoder flags and the expanded instruction encoding:
  // the capability-dependency flag is not an instruction-family identifier.
  // --------------------------------------------------------------------------
  typedef enum logic [4:0] {
    IC_ALU_RI,          // register-immediate integer ALU
    IC_ALU_RR,          // register-register integer ALU
    IC_ALU_SHIFT,       // shifts (barrel shifter operand corner cases)
    IC_BITMANIP,        // Zba / Zbb / Zbc / Zbs
    IC_MUL,
    IC_DIV,
    IC_BRANCH,
    IC_JAL,
    IC_JALR,
    IC_LS_INT,          // integer load / store
    IC_LS_CAP,          // capability load / store (CLC / CSC)
    IC_AMO,             // LR / SC / AMO*
    IC_CSR,
    IC_SCR,             // CSPECIALRW
    IC_CHERI_INSPECT,   // CGET*, CTESTSUBSET, CRRL, CRAM
    IC_CHERI_MODIFY,    // CSETBOUNDS*, CSETADDR, CINCADDR, CANDPERM, ...
    IC_CHERI_SEAL,      // CSEAL / CUNSEAL
    IC_SYS,             // ECALL, EBREAK, MRET, DRET, WFI, FENCE.I
    IC_ILLEGAL
  } kudu_instr_cat_e;

  // Optional reduced axis for coarse crosses; not used by the simultaneous
  // stage-context model, which explicitly requires detailed category products.
  typedef enum logic [2:0] {
    SC_ALU, SC_MULDIV, SC_CTRL, SC_MEM, SC_ATOMIC, SC_SYSREG, SC_CHERI, SC_BAD
  } kudu_instr_scat_e;

  // --------------------------------------------------------------------------
  // Category derivation
  // --------------------------------------------------------------------------
  function automatic bit fcov_is_cheri_category(kudu_instr_cat_e category);
    return category inside {IC_LS_CAP, IC_SCR, IC_CHERI_INSPECT,
                            IC_CHERI_MODIFY, IC_CHERI_SEAL};
  endfunction

  function automatic kudu_instr_cat_e fcov_instr_cat(ir_dec_t d);
    opcode_e    opcode;
    logic [2:0] funct3;
    logic [6:0] funct7;

    opcode = opcode_e'(d.insn[6:0]);
    funct3 = d.insn[14:12];
    funct7 = d.insn[31:25];

    if (d.errs.illegal_insn | d.errs.illegal_c_insn) return IC_ILLEGAL;

    // System instructions are flagged by the decoder, not by opcode alone:
    // CSR accesses share OPCODE_SYSTEM with ECALL / EBREAK / MRET / WFI.
    // is_csr includes CSPECIALRW in ir_decoder.
    if (d.cheri_op.cscrrw)                                return IC_SCR;
    if (d.is_csr)                                         return IC_CSR;
    if (d.sysctl.mret | d.sysctl.dret | d.sysctl.wfi |
        d.sysctl.ecall | d.sysctl.ebrk | d.sysctl.fencei) return IC_SYS;
    if (d.is_brkpt)                                       return IC_SYS;

    // CHERI. cscrrw is checked first: it is an SCR access, not a capability
    // manipulation, and it is the only CHERI op with system side effects.
    // is_cheri is an issuer dependency flag, also set for ordinary jumps and
    // integer loads/stores. Only the operation vector identifies CHERI ops.
    if (|d.cheri_op) begin
      if (d.cheri_op.clc | d.cheri_op.csc)       return IC_LS_CAP;
      if (d.cheri_op.cseal | d.cheri_op.cunseal) return IC_CHERI_SEAL;
      if (d.cheri_op.cgetperm | d.cheri_op.cgettype | d.cheri_op.cgetbase |
          d.cheri_op.cgethigh | d.cheri_op.cgettop  | d.cheri_op.cgetlen  |
          d.cheri_op.cgettag  | d.cheri_op.cgetaddr | d.cheri_op.ctestsub |
          d.cheri_op.cseteqx  | d.cheri_op.crrl     | d.cheri_op.cram)
        return IC_CHERI_INSPECT;
      return IC_CHERI_MODIFY;
    end

    if (d.is_branch) return IC_BRANCH;
    if (d.is_jal)    return IC_JAL;
    if (d.is_jalr)   return IC_JALR;

    case (opcode)
      OPCODE_AMO:      return IC_AMO;
      OPCODE_LOAD,
      OPCODE_STORE:    return IC_LS_INT;
      OPCODE_LUI,
      OPCODE_AUIPC,
      OPCODE_AUICGP:   return IC_ALU_RI;
      OPCODE_MISC_MEM: return IC_SYS;

      OPCODE_OP: begin
        if (funct7 == 7'h01) begin
          // RV32M shares OPCODE_OP; funct3[2] separates MUL* from DIV*/REM*
          return funct3[2] ? IC_DIV : IC_MUL;
        end else if ((funct7 == 7'h20) &&
                     (funct3 inside {3'b100, 3'b110, 3'b111})) begin
          return IC_BITMANIP;   // XNOR / ORN / ANDN share SUB/SRA's funct7
        end else if ((funct7 == 7'h00) || (funct7 == 7'h20)) begin
          if (funct3 inside {3'b001, 3'b101}) return IC_ALU_SHIFT;
          return IC_ALU_RR;
        end else begin
          return IC_BITMANIP;   // Zba / Zbb / Zbc / Zbs register forms
        end
      end

      OPCODE_OP_IMM: begin
        if (funct3 inside {3'b001, 3'b101}) begin
          // SLLI / SRLI / SRAI are shifts. RORI / BCLRI / BEXTI / BINVI /
          // BSETI / CLZ / CTZ / CPOP / SEXT.* share the same funct3 and are
          // distinguished only by funct7 -- this is the split that a coverpoint
          // on alu_op_e cannot see.
          if ((funct7 == 7'h00) || (funct7 == 7'h20)) return IC_ALU_SHIFT;
          return IC_BITMANIP;
        end
        return IC_ALU_RI;
      end

      default: return IC_ILLEGAL;
    endcase
  endfunction

  function automatic kudu_instr_scat_e fcov_instr_scat(kudu_instr_cat_e c);
    case (c)
      IC_ALU_RI, IC_ALU_RR, IC_ALU_SHIFT, IC_BITMANIP: return SC_ALU;
      IC_MUL, IC_DIV:                                  return SC_MULDIV;
      IC_BRANCH, IC_JAL, IC_JALR:                      return SC_CTRL;
      IC_LS_INT, IC_LS_CAP:                            return SC_MEM;
      IC_AMO:                                          return SC_ATOMIC;
      IC_CSR, IC_SCR, IC_SYS:                          return SC_SYSREG;
      IC_CHERI_INSPECT, IC_CHERI_MODIFY,
      IC_CHERI_SEAL:                                   return SC_CHERI;
      default:                                         return SC_BAD;
    endcase
  endfunction

  // --------------------------------------------------------------------------
  // Controller FSM decode.
  //
  // issuer.ctrl_fsm_cs is a 16-bit one-hot vector (issuer.sv:518) whose bit
  // positions are the ctrl_fsm_e values (super_pkg.sv:370-381), assigned as
  // "1 << CSM_x". The RTL has no decode function, so this is it. A vector that
  // is not one-hot is a design failure and is caught by cp_fsm_onehot.
  // --------------------------------------------------------------------------
  function automatic ctrl_fsm_e fcov_fsm_dec(logic [15:0] onehot);
    for (int i = 0; i < 16; i++) begin
      if (onehot[i]) return ctrl_fsm_e'(i);
    end
    return ctrl_fsm_e'(4'hf);   // no bit set is also not a legal state
  endfunction

  // --------------------------------------------------------------------------
  // Value classification for the architectural operand / result coverpoints.
  // --------------------------------------------------------------------------
  typedef enum logic [2:0] {
    VC_ZERO, VC_ONE, VC_ALL_ONES, VC_MIN_INT, VC_MAX_INT, VC_OTHER
  } fcov_vclass_e;

  function automatic fcov_vclass_e fcov_vclass(logic [31:0] v);
    case (v)
      32'h0000_0000: return VC_ZERO;
      32'h0000_0001: return VC_ONE;
      32'hffff_ffff: return VC_ALL_ONES;   // also -1
      32'h8000_0000: return VC_MIN_INT;
      32'h7fff_ffff: return VC_MAX_INT;
      default:       return VC_OTHER;
    endcase
  endfunction

  // Observed bus delay bucket. The plan requires these to be *measured* on the
  // bus rather than read back from a testbench parameter: a knob proves the
  // knob was set, counted cycles prove the core saw the delay.
  typedef enum logic [1:0] { DLY_0, DLY_1, DLY_2PLUS } fcov_delay_e;

  function automatic fcov_delay_e fcov_delay(int unsigned n);
    if (n == 0) return DLY_0;
    if (n == 1) return DLY_1;
    return DLY_2PLUS;
  endfunction

  // ir_errs_t is a 5-bit struct, not an enum (super_pkg.sv:29-35), so more than
  // one bit can be set on the same instruction. Any coverpoint over it needs a
  // "multiple" bin or it silently merges those cases into whichever bit the
  // if-chain happens to test first.
  typedef enum logic [2:0] {
    ERR_NONE, ERR_PERM_VIO, ERR_BOUND_VIO, ERR_ILLEGAL_INSN,
    ERR_ILLEGAL_C_INSN, ERR_FETCH, ERR_MULTIPLE
  } fcov_err_kind_e;

  function automatic fcov_err_kind_e fcov_err_kind(ir_errs_t e);
    if ($countones(e) > 1) return ERR_MULTIPLE;
    if (e.perm_vio)       return ERR_PERM_VIO;
    if (e.bound_vio)      return ERR_BOUND_VIO;
    if (e.illegal_insn)   return ERR_ILLEGAL_INSN;
    if (e.illegal_c_insn) return ERR_ILLEGAL_C_INSN;
    if (e.fetch_err)      return ERR_FETCH;
    return ERR_NONE;
  endfunction

  // Which arm of the branch predictor's six-way priority chain fired
  // (branch_predict.sv:305-335). Only one redirect per cycle is structurally
  // possible, which is why cp_pdt_taken == 2'b11 is illegal_bins. Per-slot
  // coverpoints reach 100% without ever exercising the jalr1 arm, so this
  // function is the coverpoint that actually matters for the chain.
  typedef enum logic [2:0] {
    PDT_NONE, PDT_BR0, PDT_JAL0, PDT_JALR0, PDT_BR1, PDT_JAL1, PDT_JALR1
  } fcov_pdt_src_e;

  function automatic fcov_pdt_src_e fcov_pdt_src(logic [1:0] br_go,
                                                 logic [1:0] jal_go,
                                                 logic [1:0] jalr_go);
    if (br_go[0])   return PDT_BR0;
    if (jal_go[0])  return PDT_JAL0;
    if (jalr_go[0]) return PDT_JALR0;
    if (br_go[1])   return PDT_BR1;
    if (jal_go[1])  return PDT_JAL1;
    if (jalr_go[1]) return PDT_JALR1;
    return PDT_NONE;
  endfunction

  // Reason slot 1 did not issue while ir_valid_i[1] was set. Issue is strictly
  // in order (issuer.sv:304, :312, :736-737), so "ir0 did not issue" is a
  // first-class reason and not an error.
  typedef enum logic [3:0] {
    SUP_NONE, SUP_IR0_NOT_ISSUED, SUP_HAZARD, SUP_ANY_ERR, SUP_SYSCTL,
    SUP_CMPLX, SUP_BRKPT, SUP_SINGLE_STEP, SUP_CJALR_SERIALISE, SUP_MISPREDICT0
  } fcov_suppress_e;

endpackage
