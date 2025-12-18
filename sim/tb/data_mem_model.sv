// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef DII_SIM
import "DPI-C" function longint unsigned instr_mem_read64( longint unsigned addr);
`endif

//
// data interface/memory model
//
module data_mem_model import kudu_dv_pkg::*; # (
  parameter bit UnalignedFetch = 1'b1
) (
  input  logic              clk,
  input  logic              rst_n,

  input  logic [2:0]        INSTR_ERR_RATE,   
  input  logic [3:0]        INSTR_GNT_WMAX,
  input  logic [3:0]        INSTR_RESP_WMAX,
  input  logic              instr_err_enable,
 
  input  logic [2:0]        DATA_ERR_RATE,   
  input  logic [3:0]        DATA_GNT_WMAX,
  input  logic [3:0]        DATA_RESP_WMAX,
  input  logic              data_err_enable,

  input  logic              instr_req,
  input  logic [31:0]       instr_addr,
                            
  output logic              instr_gnt,
  output logic              instr_rvalid,
  output logic [63:0]       instr_rdata,
  output logic              instr_err,
 
  input  logic              data_req,
  input  logic              data_we,
  input  logic [3:0]        data_be,
  input  logic              data_is_cap,
  input  logic [3:0]        data_amo_flag,
  input  logic [31:0]       data_addr,
  input  logic [64:0]       data_wdata,
  input  logic [7:0]        data_flag,

  output logic              data_gnt,
  output logic              data_rvalid,
  output logic [64:0]       data_rdata,
  output logic              data_err,
  output logic              data_sc_resp,
  output mem_cmd_t          data_resp_info,

  input  logic              tsmap_cs,
  input  logic [15:0]       tsmap_addr,
  output logic [31:0]       tsmap_rdata,

  output logic [3:0]        err_enable_vec, 
  output logic [2:0]        intr_ack,
  output logic              debug_req,
  output logic              uart_stop_sim
);
 
  // we only support DW=65 now
  localparam int unsigned DW = 65;

  localparam int unsigned DRAM_AW32   = 16; 
  localparam int unsigned DRAM_AW     = DRAM_AW32-1; 

  localparam int unsigned TSRAM_AW    = 10; 
  localparam int unsigned NMMRI       = 128/32;
  localparam int unsigned NMMRO       = 64/32;

  localparam int unsigned DBGROM_AW   = 10; 

  logic          mem_cs;
  logic          mem_is_cap;
  logic [3:0]    mem_amo_flag;
  logic          mem_we;
  logic [3:0]    mem_be;
  logic [29:0]   mem_addr32;
  logic [DW-1:0] mem_wdata;
  logic [DW-1:0] mem_rdata;
  logic          mem_err;
  logic          mem_sc_resp;

  // simple unified memory system model
  logic [DW-1:0]      dram[0:2**DRAM_AW-1];
  logic [DRAM_AW-1:0] dram_addr;
  logic [DW-1:0]      dram_rdata;
  logic               dram_sel, dram_cs;
  logic               dram_err_schd;

  logic [31:0]         tsram[0:2**TSRAM_AW-1];
  logic [TSRAM_AW-1:0] tsram_p0_addr32;
  logic [31:0]         tsram_p0_rdata;
  logic                tsram_p0_sel, tsram_p0_cs;
  logic                tsram_p0_err_schd;
  logic [TSRAM_AW-1:0] tsram_p1_addr32;

  logic [31:0]         mmreg_rdata;
  logic                mmreg_sel, mmreg_cs;
  logic [7:0]          mmreg_addr32;

  logic                uart_cs0, uart_cs1;
  logic [7:0]          uart_addr32;

  logic [7:0]          mem_flag;

  logic [DW-1:0]        dbgrom[0:2**DBGROM_AW-1];
  logic [DBGROM_AW-1:0] dbgrom_addr;
  logic [DW-1:0]        dbgrom_rdata;
  logic                 dbgrom_sel, dbgrom_cs;


  ////////////////////////////////////////////////////////////////////////////////////////
  //  Data access port
  ////////////////////////////////////////////////////////////////////////////////////////

  mem_obi_if #(
    .DW         (DW),
    .sample_delay (1)
  ) u_data_if (
    .clk_i          (clk),
    .rst_ni         (rst_n),
    .GNT_WMAX       (DATA_GNT_WMAX),
    .RESP_WMAX      (DATA_RESP_WMAX),
    .data_req       (data_req),
    .data_we        (data_we),
    .data_be        (data_be),
    .data_is_cap    (data_is_cap),
    .data_amo_flag  (data_amo_flag),
    .data_addr      (data_addr),
    .data_wdata     (data_wdata),
    .data_flag      (data_flag),
    .data_gnt       (data_gnt),
    .data_rvalid    (data_rvalid),
    .data_rdata     (data_rdata),
    .data_err       (data_err),
    .data_sc_resp   (data_sc_resp),
    .data_resp_info (data_resp_info),
    .mem_cs         (mem_cs),
    .mem_is_cap     (mem_is_cap),
    .mem_amo_flag   (mem_amo_flag),
    .mem_we         (mem_we),
    .mem_be         (mem_be),
    .mem_flag       (mem_flag),
    .mem_addr32     (mem_addr32),
    .mem_wdata      (mem_wdata),
    .mem_rdata      (mem_rdata),
    .mem_err        (mem_err),
    .mem_sc_resp    (mem_sc_resp)
  );

  //
  // memory signals (sampled @posedge clk)
  //
  logic dram_sel_q, tsram_p0_sel_q, mmreg_sel_q, dbgrom_sel_q;
  logic dram_word_sel;
  logic dbgrom_word_sel;
  logic mem_req_isr, mem_req_stkz;
  logic dram_lr_status_q;

  assign mem_req_stkz = mem_flag[2];
  assign mem_req_isr  = mem_flag[0];

  assign mem_rdata = dram_sel_q ? dram_rdata : (tsram_p0_sel_q ? {33'h0, tsram_p0_rdata} : 
                                               (mmreg_sel_q ? {33'h0, mmreg_rdata} : 
                                               (dbgrom_sel_q ? {1'h0, dbgrom_rdata} : 
                                               65'h0)));

  assign mem_sc_resp = dram_sel? ~dram_lr_status_q : 1'b0;

  // mem_err is in the mem_cs
  assign mem_err   = (DATA_ERR_RATE == 0) ? (mem_cs & (~dram_sel & ~tsram_p0_sel & ~uart_cs0 & ~uart_cs1 & ~mmreg_sel)) :
                     (~mem_req_isr & dram_sel ? dram_err_schd : (tsram_p0_sel ? tsram_p0_err_schd : 1'b0));

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      dram_sel_q        <= 1'b0;
      tsram_p0_sel_q    <= 1'b0;
      mmreg_sel_q       <= 1'b0;
      dbgrom_sel_q      <= 1'b0;
      dram_lr_status_q  <= 1'b0;
    end else begin
      dram_sel_q        <= dram_sel;
      tsram_p0_sel_q    <= tsram_p0_sel;
      mmreg_sel_q       <= mmreg_sel;  
      dbgrom_sel_q      <= dbgrom_sel;

      if (dram_cs & ~mem_we & mem_amo_flag[0])
        dram_lr_status_q <= 1'b1;
      else if (dram_cs & mem_we)
        dram_lr_status_q <= 1'b0;

    end
  end

  //
  // DRAM (data RAM)
  // starting at 0x8000_0000
  //
  // don't generate memory access if
  //   - responds with an error, or
  //   - accesses from stkz is supposed to be ignored.
  assign dram_addr   = mem_addr32[DRAM_AW:1]; 
  assign dram_sel    = mem_cs & mem_addr32[29] & (mem_addr32[28:DRAM_AW32+1] == 0);   
  assign dram_cs     = dram_sel & ~mem_err;   

  assign dram_word_sel = mem_addr32[0];

  always @(posedge clk) begin
    if (dram_cs && mem_we && mem_is_cap) begin
      dram[dram_addr] <= mem_wdata;
    end else if (dram_cs && mem_we && (~mem_amo_flag[1] | dram_lr_status_q) && dram_word_sel) begin
      if(mem_be[0])
        dram[dram_addr][39:32]  <= mem_wdata[7:0];
      if(mem_be[1])
        dram[dram_addr][47:40] <= mem_wdata[15:8];
      if(mem_be[2])
        dram[dram_addr][55:48] <= mem_wdata[23:16];
      if(mem_be[3])
        dram[dram_addr][63:56] <= mem_wdata[31:24];
    end else if (dram_cs && mem_we && (~mem_amo_flag[1] | dram_lr_status_q)) begin
      if(mem_be[0])
        dram[dram_addr][7:0]  <= mem_wdata[7:0];
      if(mem_be[1])
        dram[dram_addr][15:8] <= mem_wdata[15:8];
      if(mem_be[2])
        dram[dram_addr][23:16] <= mem_wdata[23:16];
      if(mem_be[3])
        dram[dram_addr][31:24] <= mem_wdata[31:24];
    end
     
      // CPU should always take care of driving the tag bit
    if (dram_cs && mem_we) dram[dram_addr][64]  <= mem_wdata[64];

    if (dram_cs && ~mem_we && mem_is_cap)
      dram_rdata <= dram[dram_addr];  
    else if (dram_cs && ~mem_we && dram_word_sel)
      dram_rdata <= {33'h0, dram[dram_addr][63:32]};  
    else if (dram_cs && ~mem_we)
      dram_rdata <= {33'h0, dram[dram_addr][31:0]};  

  end

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      dram_err_schd    <= 1'b0;
    end else begin
      if (~data_err_enable)
        dram_err_schd <= 1'b0;
      else if (dram_sel)
        dram_err_schd <= (DATA_ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-DATA_ERR_RATE))==0);

    end
  end 

  //
  // TSRAM (dual port RAM)
  //
  // starting at 0x8300_0000 byte address 
  assign tsram_p0_addr32 = mem_addr32[TSRAM_AW-1:0];
  assign tsram_p0_sel    = mem_cs && (mem_addr32[29:22] == 8'h83) && 
                           (mem_addr32[21] == 0) && (mem_addr32[20:DRAM_AW+2] == 0);
  assign tsram_p0_cs     = tsram_p0_sel & ~mem_err;

  assign tsram_p1_addr32 = tsmap_addr[TSRAM_AW-1:0];

  always @(posedge clk, negedge rst_n) begin
    int i;
    if (~rst_n) begin
      for (i=0; i<2**TSRAM_AW; i++) tsram[i] = 32'h0; // initialize tsram to match sail
    end else begin
      if (tsram_p0_cs && mem_we) begin
        // p0 read/write
        if(mem_be[0])
          tsram[tsram_p0_addr32][7:0]  <= mem_wdata[7:0];
        if(mem_be[1])
          tsram[tsram_p0_addr32][15:8] <= mem_wdata[15:8];
        if(mem_be[2])
          tsram[tsram_p0_addr32][23:16] <= mem_wdata[23:16];
        if(mem_be[3])
          tsram[tsram_p0_addr32][31:24] <= mem_wdata[31:24];
      end else if (tsram_p0_cs)
        tsram_p0_rdata <= tsram[tsram_p0_addr32];  

        // p1 readonly
      if (tsmap_cs)
        tsmap_rdata <= tsram[tsram_p1_addr32];
      else 
        tsmap_rdata <= 32'h0;
    end
  end

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      tsram_p0_err_schd <= 1'b0;
    end else begin
      if (~data_err_enable)
        tsram_p0_err_schd <= 1'b0;
      else if (tsram_p0_sel)
        tsram_p0_err_schd <= (DATA_ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-DATA_ERR_RATE))==0);
    end
  end 
 
  //
  // MMREG (memory-mapped registers)
  //
  // 0x8380_0000: scratch register 0,1
  // 0x8380_0100: TB error_enable, Intr_ack
  // 0x8380_0140: Debug ROM communication registers
  // 
  //
  logic [64:0] tbre_ctrl_vec;
  logic        tbre_stat, tbre_stat_q;
  logic [7:0]  tbre_flag;
  logic        tbre_done;
  logic [30:0] tbre_epoch;
  logic [7:0]  mmreg_addr32_q;
  logic        tbre_err, stkz_active, stkz_err;
  logic [31:0] scratch_reg0, scratch_reg1;
  logic [7:0]  dbg_req_cnt, dbg_ack_cnt;
  logic [31:0] dcsr_r, dcsr_w;
  logic        tmatch_ctrl0, tmatch_ctrl1;
  logic [31:0] tmatch_val0, tmatch_val1;

  // starting at 0x8380_0000 byte address 
  assign mmreg_addr32 = mem_addr32[7:0];
  assign mmreg_sel    = mem_cs && (mem_addr32[29:22] == 8'h83) && 
                        (mem_addr32[21] == 1) && (mem_addr32[20:8] == 0);
  assign mmreg_cs     = mmreg_sel;

  always_comb begin
    case (mmreg_addr32_q[7:0])
      8'h00: mmreg_rdata = scratch_reg0;  
      8'h01: mmreg_rdata = scratch_reg1;  
      8'h50: mmreg_rdata = {dbg_req_cnt, dbg_ack_cnt, 16'h0};
      8'h51: mmreg_rdata = dcsr_r;       // test read, debug rom write
      8'h52: mmreg_rdata = dcsr_w;       // test write, debug rom read
      8'h53: mmreg_rdata = {29'h0, tmatch_ctrl0, 2'b00};
      8'h54: mmreg_rdata = {29'h0, tmatch_ctrl1, 2'b00};
      8'h55: mmreg_rdata = tmatch_val0;
      8'h56: mmreg_rdata = tmatch_val1;
      default: mmreg_rdata = 32'hdead_beef; 
    endcase
  end
  
 always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      mmreg_addr32_q    <= 0;
      intr_ack          <= 3'h0;
      debug_req         <= 1'b0;
      err_enable_vec    <= 4'h0;
      scratch_reg0      <= 32'h0; 
      scratch_reg1      <= 32'h0;
      dbg_req_cnt       <= 8'h0; 
      dbg_ack_cnt       <= 8'h0; 
      dcsr_r            <= 32'h0;
      dcsr_w            <= 32'h0;
      tmatch_ctrl0      <= 1'b0;
      tmatch_ctrl1      <= 1'b0;
      tmatch_val0       <= 32'h0;
      tmatch_val1       <= 32'h0;
    end
    else begin
      mmreg_addr32_q <= mmreg_addr32;

      if (tbre_done) tbre_epoch <= tbre_epoch + 1;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h00))  // 0x8380_0000
        scratch_reg0 <= mem_wdata[31:0];
      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h01))  // 0x8380_0004
        scratch_reg1 <= mem_wdata[31:0];

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h40))  // 0x8380_0100
        err_enable_vec <= mem_wdata[3:0];

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h41))  // 0x8380_0104
        intr_ack <= mem_wdata[2:0];
      else
        intr_ack <= 3'h0;

      // debug related registers
      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h50))  begin // 0x8380_0140
        debug_req   <= mem_wdata[0];
        dbg_req_cnt <= dbg_req_cnt + {7'h0, mem_wdata[0]};
        dbg_ack_cnt <= dbg_ack_cnt + {7'h0, ~mem_wdata[0]};
      end

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h51))  // 0x8380_0144
        dcsr_r  <= mem_wdata;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h52))  // 0x8380_0148
        dcsr_w  <= mem_wdata;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h53))  // 0x8380_014c
        tmatch_ctrl0  <= mem_wdata[2];

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h54))  // 0x8380_0150
        tmatch_ctrl1  <= mem_wdata[2];

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h55))  // 0x8380_0154
        tmatch_val0  <= mem_wdata;

      if (mmreg_cs && mem_we && (mmreg_addr32 == 'h56))  // 0x8380_0158
        tmatch_val1  <= mem_wdata;

    end
  end 
  
  //
  // 0x8380_0200: UART (also aliased to 0x1000_0000)
  //
  assign uart_addr32 = mem_addr32[7:0];
  assign uart_cs0    = mem_cs && (mem_addr32[29:22] == 8'h83) && (mem_addr32[21:8] == 14'h2000);
  assign uart_cs1    = mem_cs && (mem_addr32[29:22] == 8'h10) && (mem_addr32[21:8] == 14'h0000);

`ifdef RISCV_TEST_SUITE
  logic tohost_cs0, tohost_cs1;
  assign tohost_cs0   = mem_cs && (mem_addr32[29:0] == 30'h2000_2000);
  assign tohost_cs1   = mem_cs && (mem_addr32[29:0] == 30'h2000_2001);

  // tohost print out pass/fail message
  //   - pass:  0x01 to cs0,  followed by 0x0 to cs1 
  //   - fail:  any value not 0x01 to cs0, followed by 0x0 to cs1 
  initial begin
    uart_stop_sim = 1'b0;
    @(posedge rst_n);

    while (1) begin
      @(posedge clk);
      if (tohost_cs0 && (mem_wdata == 32'h1)) begin
        while (~tohost_cs1) @(posedge clk);
        if (tohost_cs1 && (mem_wdata == 32'h0)) begin
          $display("RISCV Test passed :)");
          uart_stop_sim = 1'b1;
          repeat (100) @(posedge clk);
        end
      end else if (tohost_cs0) begin
        while (~tohost_cs1) @(posedge clk);
        if (tohost_cs1 && (mem_wdata == 32'h0)) begin
          $display("RISCV Test failed :(");
          uart_stop_sim = 1'b1;
          repeat(100) @(posedge clk);
        end
      end
    end
  end
`else
  // UART printout
  initial begin
    uart_stop_sim = 1'b0;
    @(posedge rst_n);

    while (1) begin
      @(posedge clk);
      if ((uart_cs0 && mem_we && (uart_addr32 == 'h80)) || 
          (uart_cs1 && mem_we && (uart_addr32 == 'h00)))  
        if (mem_wdata[7]) 
          uart_stop_sim = 1'b1;
       else 
          $write("%c", mem_wdata[7:0]);
    end
  end
`endif

  //
  // Debug ROM
  // starting at 0x8400_0000
  //
  assign dbgrom_addr   = mem_addr32[DRAM_AW:1]; 
  assign dbgrom_sel    = mem_cs & (mem_addr32[29:24] == 6'h21) && (mem_addr32[23:DRAM_AW32+1] == 0);   
  assign dbgrom_cs     = dbgrom_sel & ~mem_err;   

  assign dbgrom_word_sel = mem_addr32[0];

  always @(posedge clk) begin
    if (dbgrom_cs && ~mem_we && mem_is_cap)
      dbgrom_rdata <= dbgrom[dbgrom_addr];  
    else if (dbgrom_cs && ~mem_we && dbgrom_word_sel)
      dbgrom_rdata <= {33'h0, dbgrom[dbgrom_addr][63:32]};  
    else if (dbgrom_cs && ~mem_we)
      dbgrom_rdata <= {33'h0, dbgrom[dbgrom_addr][31:0]};  
  end

  ////////////////////////////////////////////////////////////////////////////////////////
  //  Instruction fetch port
  ////////////////////////////////////////////////////////////////////////////////////////
  logic          instr_mem_cs;
  logic [29:0]   instr_mem_addr32;
  logic [63:0]   instr_mem_rdata;
  logic          instr_mem_err;

  mem_obi_if #(
    .DW         (64),
    .sample_delay (2)
  ) u_instr_if (
    .clk_i          (clk),
    .rst_ni         (rst_n),
    .GNT_WMAX       (INSTR_GNT_WMAX),
    .RESP_WMAX      (INSTR_RESP_WMAX),
    .data_req       (instr_req),
    .data_we        (1'b0),
    .data_be        (4'hf),
    .data_is_cap    (1'b0),
    .data_amo_flag  (4'h0),
    .data_addr      (instr_addr),
    .data_wdata     (64'h0),
    .data_flag      (8'h0),
    .data_gnt       (instr_gnt),
    .data_rvalid    (instr_rvalid),
    .data_rdata     (instr_rdata),
    .data_err       (instr_err),
    .data_sc_resp   (),
    .data_resp_info (),
    .mem_cs         (instr_mem_cs),
    .mem_is_cap     (),
    .mem_amo_flag   (),
    .mem_we         (),
    .mem_be         (),
    .mem_flag       (),
    .mem_addr32     (instr_mem_addr32),
    .mem_wdata      (),
    .mem_rdata      (instr_mem_rdata),
    .mem_err        (instr_mem_err),
    .mem_sc_resp    (1'b0)
  );


`ifdef DII_SIM
  // DII sim uses a sparse memory model spanns the entire address range, thus address decoding needed
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      instr_mem_rdata <= 0;
    end else begin
      instr_mem_rdata <= instr_mem_read64({instr_mem_addr32, 2'b00});
    end
  end

  assign instr_mem_err = 1'b0;
`else
  logic instr_dram_sel, instr_dbgrom_sel;
  logic instr_dram_sel_q, instr_dbgrom_sel_q;

  logic [63:0] instr_dram_rdata, instr_dbgrom_rdata;

  logic [DRAM_AW-1:0]   instr_dram_addr; 
  logic [DBGROM_AW-1:0] instr_dbgrom_addr;

  assign instr_mem_rdata = instr_dram_sel_q ? instr_dram_rdata : 
                           instr_dbgrom_sel_q ? instr_dbgrom_rdata : 64'h0;

  assign instr_mem_err = 1'b0;

  assign instr_dram_sel    = instr_mem_cs & instr_mem_addr32[29] & (instr_mem_addr32[28:DRAM_AW32+1] == 0);   
  assign instr_dram_addr   = instr_mem_addr32[DRAM_AW-1:1];

  assign instr_dbgrom_addr = instr_mem_addr32[DRAM_AW:1]; 
  assign instr_dbgrom_sel  = instr_mem_cs & (instr_mem_addr32[29:24] == 6'h21) && (instr_mem_addr32[23:DRAM_AW32+1] == 0);   
 
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      instr_dram_sel_q     <= 1'b0;
      instr_dbgrom_sel_q   <= 1'b0;
    end else begin
      instr_dram_sel_q     <= instr_dram_sel;
      instr_dbgrom_sel_q   <= instr_dbgrom_sel;
    end
  end 

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      instr_dram_rdata   <= 0;
      instr_dbgrom_rdata <= 0;
    end else begin
      if (instr_dram_sel & (~instr_mem_addr32[0] | ~UnalignedFetch)) 
        instr_dram_rdata <= dram[instr_dram_addr];
      else if  (instr_dram_sel & instr_mem_addr32[0])
        instr_dram_rdata <= {dram[instr_dram_addr+1][31:0], dram[instr_dram_addr][63:32]};

      if (instr_dbgrom_sel  & (~instr_mem_addr32[0] | ~UnalignedFetch))
        instr_dbgrom_rdata <= dbgrom[instr_dbgrom_addr];  
      else if  (instr_dbgrom_sel & instr_mem_addr32[0])
        instr_dbgrom_rdata <= {dbgrom[instr_dbgrom_addr+1][31:0], dbgrom[instr_dbgrom_addr][63:32]};
      
    end
  end
`endif

endmodule
