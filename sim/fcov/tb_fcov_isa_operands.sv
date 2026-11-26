// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
module kudu_top;
`ifdef CHERIoT
  parameter bit CHERIoTEn = 1;
`else
  parameter bit CHERIoTEn = 0;
`endif
  tracer trace();
endmodule

module tracer;
  import cheri_pkg::*;
  import super_pkg::*;
  import tracer_pkg::*;
  logic clk_i = 0;
  logic rst_ni = 0;
  logic cheri_pmode_i = 0;
  logic issue_cmplx = 0;
  logic [5:0] wr_ptr = 0;
  instr_trace_t issued_instr[2];
  logic [$bits(instr_trace_t)-1:0] instr_trace_fifo[64];
  logic [5:0] rd_ptr = 0, rd_ptr_nxt = 0;
  logic [1:0] cmt_instr_err = 0;
  logic [$bits(instr_trace_t)-1:0] amo_instr_q = 0;
  logic amo_retire = 0;
  logic tsafe_en_i = 0, trvk_en = 0, trvk_clrtag = 0;
  logic [5:0] final_wr_ptr = 0, final_rd_ptr = 0;
  instr_trace_t final_fifo[64];
  bit is_cmt0[64];
  typedef enum {AMO_T_IDLE, AMO_T_WAIT0, AMO_T_WAIT1} amo_state_e;
  amo_state_e amo_state = AMO_T_IDLE;
  ir_reg_t compressed_in, compressed_out;
  int expected[131072];
  logic [63:0] vectors[1056];
  int instruction, reference, value, count;
  instr_trace_t t;
  mem_cap_t capability;
  mem_cap_t result_capability;
  string test_case;
  logic [31:0] family_words[24] = '{
    32'h00008133, 32'h00008063, 32'h00018083, 32'h00018023,
    32'h1000202f, 32'h1800202f, 32'h60001013, 32'h00008086,
    32'h1000005b, 32'h2200005b, 32'hfe80005b, 32'hfe90005b,
    32'hfe40005b, 32'h1600005b, 32'h0200005b, 32'h00000017,
    32'h0000205b, 32'h0000105b, 32'h0000007b, 32'h00008082,
    32'h00004080, 32'h00006080, 32'h0000e080, 32'h00005073
  };
  logic [31:0] scalar_values[7] = '{
    0, 1, 32'hffffffff, 32'h80000000, 32'h7fffffff, 17, 32'h80000011
  };
  always #5 clk_i = !clk_i;
  compressed_decoder #(.CHERIoTEn(1)) expander (
    .clk_i, .rst_ni, .cheri_pmode_i, .instr_i(compressed_in), .instr_o(compressed_out)
  );
  kudu_fcov_isa monitor (.*);
  function automatic instr_trace_t fill_cmt_info(instr_trace_t trace_in, bit first, bit second);
    return trace_in;
  endfunction

  task automatic prepare(logic [31:0] word32, bit mode);
    t = '0;
    t.rvfi.valid = 1;
    t.rvfi.insn = word32;
    t.ir_dec.insn = word32;
    t.ir_dec.cheri_op = mode ? '1 : '0;
    t.rvfi.rs1_addr = 3;
    t.rvfi.rs2_addr = 4;
    t.rvfi.rs1_rdata = 17;
    t.rvfi.rs2_rdata = 19;
  endtask

  task automatic check_source(logic [31:0] word32, bit mode,
                               bit source1, bit source2, bit cap1, bit cap2);
    prepare(word32, mode);
    assert (monitor.instruction_id(t, mode) != monitor.ISA_UNKNOWN) else $fatal;
    assert (monitor.uses_source(monitor.instruction_id(t, mode), 0) == source1 &&
            monitor.uses_source(monitor.instruction_id(t, mode), 1) == source2 &&
            monitor.capability_source(monitor.instruction_id(t, mode), mode, 0) == cap1 &&
            monitor.capability_source(monitor.instruction_id(t, mode), mode, 1) == cap2)
      else $fatal(1, "source roles %h mode %b", word32, mode);
  endtask

  initial begin
    issued_instr[0] = '0;
    issued_instr[1] = '0;
    compressed_in = '0;
    foreach (instr_trace_fifo[i]) instr_trace_fifo[i] = '0;
    foreach (final_fifo[i]) final_fifo[i] = '0;
    if (!$value$plusargs("CASE=%s", test_case)) test_case = "semantics";
    if (test_case inside {"pairs", "permissions"}) begin
      int fd, fields, mode, kind, rs1, rs2;
      logic [31:0] word32;
      mem_cap_t source1, source2;
      fd = $fopen($sformatf("../%s.hex", test_case), "r");
      if (!fd) $fatal(1, "cannot open source-pair vectors");
      while (!$feof(fd)) begin
        fields = $fscanf(fd, "%h %h %h %h %h %h %h\n",
                         word32, mode, kind, rs1, rs2, source1, source2);
        if (fields != 7) $fatal(1, "invalid source-pair vector");
        prepare(word32, 1'(mode));
        t.rvfi.rs1_addr = 5'(rs1);
        t.rvfi.rs2_addr = 5'(rs2);
        t.rvfi.rs1_rdata = MemW'(source1);
        t.rvfi.rs2_rdata = MemW'(source2);
        t.rvfi.trap = kind inside {1, 2};
        t.is_ex = kind == 1;
        t.rvfi.intr = kind == 3;
        t.rvfi.valid = kind != 4;
        cheri_pmode_i = !1'(mode);
        monitor.sample_entry(t, 1'(mode));
      end
      $fclose(fd);
    end else if (test_case == "families") begin
      // Identical cursor patterns exercise both roles without conflating them.
      for (int mode = 0; mode <= 1; mode++) begin
        for (int tag = 0; tag <= 1; tag++) begin
          foreach (family_words[w]) begin
            foreach (scalar_values[v]) begin
              prepare(family_words[w], 1'(mode));
              // RSVD is set only untagged: a tagged RSVD is an illegal bin.
              capability = '{1'(tag), 1'(!tag), 6'h35, 3'd0, 5'd19,
                             8'h81, 9'h101, scalar_values[v]};
              t.rvfi.rs1_addr = 8;
              t.rvfi.rs2_addr = 9;
              if (family_words[w] == 32'h0000007b) t.rvfi.rs1_addr = 3;
              if (family_words[w] == 32'h0200005b) t.rvfi.rs1_addr = 0;
              t.rvfi.rs1_rdata = MemW'(capability);
              t.rvfi.rs2_rdata = MemW'(capability);
              t.rvfi.rd_addr = 5;
              t.rvfi.rd_wdata = MemW'(capability);
              // The live mode intentionally disagrees with the saved mode.
              cheri_pmode_i = !1'(mode);
              monitor.sample_entry(t, 1'(mode));
            end
          end
        end
      end
    end else if (test_case == "semantics") begin
      $readmemh("../expected.hex", expected);
      $readmemh("../vectors.hex", vectors);
      foreach (vectors[i]) begin
        prepare(vectors[i][31:0], vectors[i][32]);
        assert (int'(monitor.instruction_id(t, vectors[i][32])) == int'(vectors[i] >> 33))
          else $fatal(1, "32-bit identity vector %d word %h", i, vectors[i][31:0]);
      end
      for (int mode = 0; mode < 2; mode++) begin
        cheri_pmode_i = 1'(mode);
        for (int word16 = 0; word16 < 65536; word16++) begin
          prepare(32'(word16), 1'(mode));
          instruction = monitor.instruction_id(t, 1'(mode));
          reference = expected[mode * 65536 + word16];
          // Low bits 11 are ordinary 32-bit encodings, not compressed cases.
          if ((word16 & 3) != 3)
            assert (instruction == reference)
              else $fatal(1, "compressed %h mode %d got %d expected %d",
                          word16, mode, instruction, reference);
          compressed_in.insn = 32'(word16);
          #1;
          t.ir_dec.insn = compressed_out.insn;
          if ((word16 & 3) != 3 && instruction != monitor.ISA_UNKNOWN &&
              monitor.immediate_kind(monitor.instruction_id(t, 1'(mode))) != monitor.IMM_NONE) begin
            assert (monitor.immediate_goal(monitor.instruction_id(t, 1'(mode)), 1'(mode),
                      monitor.immediate_class(monitor.instruction_id(t, 1'(mode)),
                                              monitor.immediate_value(t, monitor.instruction_id(t, 1'(mode))))))
              else $fatal(1, "compressed immediate class %h mode %d", word16, mode);
          end
        end
      end
      check_source(32'h60001013, 0, 1, 0, 0, 0); // CLZ
      check_source(32'h08004033, 0, 1, 0, 0, 0); // ZEXT.H
      check_source(32'h1000202f, 1, 1, 0, 1, 0); // LR.W
      check_source(32'h1800202f, 1, 1, 1, 1, 0); // SC.W
      check_source(32'h00005073, 1, 0, 0, 0, 0); // CSRRWI
      check_source(32'h00001073, 1, 1, 0, 0, 0); // CSRRW
      check_source(32'h00008086, 1, 0, 1, 0, 0); // C.MV
      check_source(32'hfe80005b, 1, 1, 0, 0, 0); // CRRL
      check_source(32'hfe90005b, 1, 1, 0, 0, 0); // CRAM
      check_source(32'hfe00005b, 1, 1, 0, 1, 0); // CGETPERM
      check_source(32'h2800005b, 1, 1, 1, 1, 1); // CSUB
      check_source(32'h2c00005b, 1, 1, 1, 1, 0); // CSETHIGH
      check_source(32'h1600005b, 1, 1, 1, 1, 1); // CSEAL
      check_source(32'h0200005b, 1, 1, 0, 1, 0); // CSCRRW
      check_source(32'h0000007b, 1, 1, 0, 1, 0); // AUICGP
      check_source(32'h00000017, 1, 0, 0, 0, 0); // AUIPCC
      for (int immediate = 0; immediate < 4096; immediate++) begin
        prepare((32'(immediate) << 20) | 32'h13, 0);
        value = monitor.immediate_value(t, monitor.ISA_ADDI);
        assert (value == (immediate < 2048 ? immediate : immediate - 4096)) else $fatal;
        prepare((32'(immediate) << 20) | 32'h205b, 1);
        value = monitor.immediate_value(t, monitor.ISA_CSETBOUNDSIMM);
        assert (value == immediate) else $fatal;
      end
      for (int immediate = 0; immediate < 32; immediate++) begin
        prepare((32'(immediate) << 15) | 32'h5073, 0);
        assert (monitor.immediate_value(t, monitor.ISA_CSRRWI) == immediate) else $fatal;
        prepare((32'(immediate) << 20) | 32'h60005013, 0);
        assert (monitor.immediate_value(t, monitor.ISA_RORI) == immediate) else $fatal;
      end
      assert (!monitor.source_register(monitor.ISA_C_LW, 0, 0, 7)) else $fatal;
      assert (monitor.source_register(monitor.ISA_C_LW, 0, 0, 8)) else $fatal;
      assert (!monitor.source_register(monitor.ISA_ADD, 1, 0, 16)) else $fatal;
      assert (monitor.source_register(monitor.ISA_ADD, 0, 0, 31)) else $fatal;
      assert (!monitor.source_register(monitor.ISA_AUICGP, 1, 0, 2)) else $fatal;
      assert (monitor.source_register(monitor.ISA_AUICGP, 1, 0, 3)) else $fatal;
      assert (monitor.operand_size(0) == 0) else $fatal;
      for (int size = 1; size <= 32; size++) begin
        assert (monitor.operand_size(32'b1 << (size - 1)) == size) else $fatal;
        assert (monitor.operand_size(32'hffffffff >> (32 - size)) == size) else $fatal;
      end
    end else if (test_case == "cd") begin
      capability = '{1'b1, 1'b0, 6'h35, 3'd5, 5'd19, 8'h81, 9'h101, 32'h80000000};
      // CMOVE preserves each field; the live mode pin is deliberately zero.
      prepare(32'hfea181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(capability);
      monitor.sample_entry(t, 1);
      // Clear-tag preserves metadata, but cannot produce a tagged result.
      prepare(32'hfeb181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      result_capability = capability;
      result_capability.valid = 0;
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(result_capability);
      monitor.sample_entry(t, 1);
      // Integer-returning CHERI instructions must not sample capability CD.
      prepare(32'hfe4181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = 1;
      monitor.sample_entry(t, 1);
      prepare(32'hfe8181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(capability);
      monitor.sample_entry(t, 1);
      prepare(32'h000181b3, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(capability);
      monitor.sample_entry(t, 1);
      prepare(32'h280181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rs2_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = 0;
      monitor.sample_entry(t, 1);
      // Both capability sources of CSEAL/CUNSEAL have matching-field crosses.
      prepare(32'h160181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rs2_rdata = MemW'(capability);
      result_capability = capability;
      result_capability.valid = 0;
      result_capability.otype = 6;
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(result_capability);
      monitor.sample_entry(t, 1);
      prepare(32'h180181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rs2_rdata = MemW'(capability);
      result_capability = capability;
      result_capability.otype = 0;
      result_capability.cperms = 6'h15;
      result_capability.valid = 0;
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(result_capability);
      monitor.sample_entry(t, 1);
      // Read-only SCR: destination is meaningful, the dummy CS1 is not.
      prepare(32'h03d001db, 1);
      t.rvfi.rs1_addr = 0;
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(capability);
      monitor.sample_entry(t, 1);
      // Source coverage survives an execute fault, CD coverage does not.
      prepare(32'hfea181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(capability);
      t.rvfi.trap = 1;
      t.is_ex = 1;
      monitor.sample_entry(t, 1);
      t.is_ex = 0;
      monitor.sample_entry(t, 1);
      t.rvfi.trap = 0;
      t.rvfi.rd_addr = 0;
      t.rvfi.rd_wdata = 0;  // RVFI reports zero data for x0 (cp_rd.x0 is illegal)
      monitor.sample_entry(t, 1);
      // A preserved grouped mantissa bin must retain its diagonal goal.
      capability.base9 = 3;
      capability.top8 = 3;
      prepare(32'hfea181db, 1);
      t.rvfi.rs1_rdata = MemW'(capability);
      t.rvfi.rd_addr = 5;
      t.rvfi.rd_wdata = MemW'(capability);
      monitor.sample_entry(t, 1);
      if (kudu_top.CHERIoTEn) begin
        assert (!monitor.capability_destination(monitor.ISA_CGETTAG, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CGETPERM, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CRRL, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CSUB, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CTESTSUB, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CSETEQX, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CSC, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_ADD, 1)) else $fatal;
        assert (!monitor.capability_destination(monitor.ISA_CMOVE, 0)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CMOVE, 0, monitor.CF_TAG, 0, 1)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CMOVE, 0, monitor.CF_CPERMS, 1, 2)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CMOVE, 0, monitor.CF_BASE, 3, 257)) else $fatal;
        assert (monitor.source_destination_goal(monitor.ISA_CMOVE, 0, monitor.CF_BASE, 3, 3)) else $fatal;
        assert (monitor.source_destination_goal(monitor.ISA_CMOVE, 0, monitor.CF_BASE, 2, 3)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CUNSEAL, 0, monitor.CF_OTYPE, 3, 1)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CCLEARTAG, 0, monitor.CF_TAG, 1, 1)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CSETBOUNDS, 0, monitor.CF_TAG, 0, 1)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CSEAL, 1, monitor.CF_TAG, 0, 1)) else $fatal;
        assert (!monitor.destination_field_goal(monitor.ISA_CSETHIGH, monitor.CF_TAG, 1)) else $fatal;
        assert (!monitor.destination_field_goal(monitor.ISA_CSETBOUNDS, monitor.CF_CEXP, 6)) else $fatal;
        assert (monitor.destination_field_goal(monitor.ISA_CSETBOUNDS, monitor.CF_CEXP, 7)) else $fatal;
        assert (!monitor.destination_field_goal(monitor.ISA_CSETBOUNDSRNDN, monitor.CF_CEXP, 7)) else $fatal;
        assert (!monitor.destination_field_goal(monitor.ISA_CSETBOUNDSIMM, monitor.CF_CEXP, 26)) else $fatal;
        assert (monitor.destination_field_goal(monitor.ISA_CSETBOUNDSIMM, monitor.CF_CEXP, 27)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CINCADDR, 0, monitor.CF_CEXP, 7, 8)) else $fatal;
        assert (!monitor.source_destination_goal(monitor.ISA_CUNSEAL, 1, monitor.CF_CPERMS, 3, 35)) else $fatal;
      end
    end else if (test_case == "revocation") begin
      if (kudu_top.CHERIoTEn) begin
        #12;
        rst_ni = 1;
        tsafe_en_i = 1;
        capability = '{1'b1, 1'b0, 6'h35, 3'd0, 5'd19, 8'h81, 9'h101, 32'h80000000};
        @(negedge clk_i);
        cheri_pmode_i = 1;
        wr_ptr = 0;
        prepare(32'h0001b283, 1);
        t.ir_dec.cheri_op = '0;
        t.ir_dec.cheri_op.clc = 1;
        t.is_ex = 1;
        t.rvfi.rs1_rdata = MemW'(capability);
        t.rvfi.rd_addr = 5;
        t.rvfi.rd_wdata = MemW'(capability);
        issued_instr[0] = t;
        instr_trace_fifo[0] = t;
        issued_instr[1] = t;
        instr_trace_fifo[1] = t;
        @(negedge clk_i);
        issued_instr[0] = '0;
        issued_instr[1] = '0;
        rd_ptr_nxt = 2;
        cheri_pmode_i = 0;
        @(negedge clk_i);
        rd_ptr = 2;
        final_fifo[0] = t;
        final_fifo[1] = t;
        final_wr_ptr = 2;
        trvk_en = 0;
        repeat (2) @(negedge clk_i); // No CD hit while CLC waits for revocation.
        trvk_en = 1;
        trvk_clrtag = 1;
        @(negedge clk_i);
        final_rd_ptr = 1;
        trvk_clrtag = 0;
        @(negedge clk_i);
        final_rd_ptr = 2;
        trvk_en = 0;
      end
    end else if (test_case == "tap") begin
      #12;
      rst_ni = 1;
      @(negedge clk_i);
      prepare(32'h00008133, 0);
      issued_instr[0] = t;
      instr_trace_fifo[62] = t;
      prepare(32'h40008133, 0);
      issued_instr[1] = t;
      instr_trace_fifo[63] = t;
      wr_ptr = 62;
      @(negedge clk_i);
      issued_instr[0] = '0;
      issued_instr[1] = '0;
      cheri_pmode_i = kudu_top.CHERIoTEn;
      rd_ptr = 62;
      rd_ptr_nxt = 0;
      cmt_instr_err = 1; // Older retirees must not disappear at a commit error.
      @(negedge clk_i);
      rd_ptr = 0;
      cmt_instr_err = 0;
      prepare(kudu_top.CHERIoTEn ? 32'h160201db : 32'h00008133, kudu_top.CHERIoTEn);
      t.is_ex = 1;
      t.rvfi.trap = 1;
      issued_instr[0] = t;
      instr_trace_fifo[0] = t;
      wr_ptr = 0;
      @(negedge clk_i);
      issued_instr[0] = '0;
      cheri_pmode_i = 0;
      rd_ptr_nxt = 1;
      @(negedge clk_i);
      rd_ptr = 1;
      cheri_pmode_i = kudu_top.CHERIoTEn;
      prepare(32'h0001a12f, kudu_top.CHERIoTEn);
      t.is_ex = 1;
      t.is_amo = 1;
      amo_instr_q = t;
      instr_trace_fifo[1] = t;
      rd_ptr_nxt = 2; // Normal FIFO walk must not double-count the AMO.
      issue_cmplx = 1;
      @(negedge clk_i);
      rd_ptr = 2;
      issue_cmplx = 0;
      cheri_pmode_i = 0;
      amo_state = AMO_T_WAIT1;
      amo_retire = 1;
      @(negedge clk_i);
      amo_retire = 0;
      cheri_pmode_i = kudu_top.CHERIoTEn;
      prepare(32'h1801a12f, kudu_top.CHERIoTEn);
      t.is_ex = 1;
      t.is_amo = 1;
      t.rvfi.trap = 1;
      amo_instr_q = t;
      issue_cmplx = 1;
      @(negedge clk_i);
      issue_cmplx = 0;
      cheri_pmode_i = 0;
      amo_state = AMO_T_WAIT0;
      amo_retire = 1;
      @(negedge clk_i);
      amo_retire = 0;
    end else if (test_case == "bins") begin
      cheri_pmode_i = kudu_top.CHERIoTEn;
      prepare(32'h00008133, 0);
      monitor.sample_entry(t, 0);
      prepare(32'h60009113, 0);
      monitor.sample_entry(t, 0);
      prepare(32'hfff00113, 0);
      t.rvfi.rs1_addr = 0;
      t.rvfi.rs1_rdata = 0;
      monitor.sample_entry(t, 0);
      prepare(32'h3401d173, 0);
      monitor.sample_entry(t, 0);
      prepare(32'h00008086, 0);
      monitor.sample_entry(t, 0);
      if (kudu_top.CHERIoTEn) begin
        capability = '{1'b1, 1'b0, 6'h35, 3'd5, 5'd19, 8'h81, 9'h101, 32'h80000000};
        prepare(32'h160201db, 1);
        t.rvfi.rs1_rdata = MemW'(capability);
        t.rvfi.rs2_rdata = MemW'(capability ^ 65'h10000000000000000);
        monitor.sample_entry(t, 1);
        prepare(32'hfe8181db, 1);
        monitor.sample_entry(t, 1);
        prepare(32'h03d001db, 1);
        t.rvfi.rs1_addr = 0;
        monitor.sample_entry(t, 1); // SCR read has no capability write-source.
      end
      // None of these packets may contribute operand goals.
      prepare(32'h00008133, 0);
      t.rvfi.valid = 0;
      monitor.sample_entry(t, 0);
      t.rvfi.valid = 1;
      t.rvfi.intr = 1;
      monitor.sample_entry(t, 0);
      t.rvfi.intr = 0;
      t.rvfi.trap = 1;
      monitor.sample_entry(t, 0);
    end else begin
      $fatal(1, "Unknown CASE=%s", test_case);
    end
    $display("PASS ISA operands %s hardware=%0d", test_case, kudu_top.CHERIoTEn);
    $finish;
  end
endmodule
