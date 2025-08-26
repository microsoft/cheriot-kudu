// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// instr interface/memory model
//
module instr_mem_model # (
  parameter bit UnalignedFetch = 1'b1
) ( 
  input  logic        clk,
  input  logic        rst_n,

  input  logic [2:0]  ERR_RATE,    
  input  logic [3:0]  GNT_WMAX,
  input  logic [3:0]  RESP_WMAX,
  input  logic        err_enable,

  input  logic        instr_req,
  input  logic [31:0] instr_addr,

  output logic        instr_gnt,
  output logic        instr_rvalid,
  output logic [63:0] instr_rdata,
  output logic        instr_err
);

  localparam int unsigned DW          = 64; 
  localparam int unsigned IRAM_AW     = 15;  
  localparam int unsigned IRAM_AW32   = 16; 
  localparam int unsigned DBGROM_AW   = 10; 
  localparam int unsigned DBGROM_AW32 = 11; 
 
  logic          mem_cs;
  logic [DW-1:0] mem_din;
  logic [DW-1:0] mem_rdata;
  logic [29:0]   mem_addr32;
  logic          mem_err;

  logic [IRAM_AW-1:0] iram_addr;
  logic               iram_err, iram_err_q;
  logic [DW-1:0]      iram_rdata;
  reg   [DW-1:0]      iram[0:2**IRAM_AW-1];
  logic               iram_sel, iram_cs;

  logic [DW-1:0]        dbgrom[0:2**DBGROM_AW-1];
  logic [DBGROM_AW-1:0] dbgrom_addr;
  logic [DW-1:0]        dbgrom_rdata;
  logic                 dbgrom_sel, dbgrom_cs;

 
  mem_obi_if #(
    .DW         (DW),
    .sample_delay (2)
  ) u_mem_obj_if (
    .clk_i        (clk),
    .rst_ni       (rst_n),
    .GNT_WMAX     (GNT_WMAX),
    .RESP_WMAX    (RESP_WMAX),
    .data_req     (instr_req),
    .data_we      (1'b0),
    .data_be      (4'hf),
    .data_is_cap  (1'b0),
    .data_addr    (instr_addr),
    .data_wdata   (64'h0),
    .data_flag    (8'h0),
    .data_gnt     (instr_gnt),
    .data_rvalid  (instr_rvalid),
    .data_rdata   (instr_rdata),
    .data_err     (instr_err),
    .data_resp_info (),
    .mem_cs       (mem_cs),
    .mem_is_cap   (),
    .mem_we       (),
    .mem_be       (),
    .mem_flag     (),
    .mem_addr32   (mem_addr32),
    .mem_wdata    (),
    .mem_rdata    (mem_rdata),
    .mem_err      (mem_err)
  );
 
  //
  // memory signals (sampled @posedge clk)
  //
  logic iram_sel_q, dbgrom_sel_q;

  assign mem_rdata = iram_sel_q ? iram_rdata : (dbgrom_sel_q ? dbgrom_rdata : 64'h0); 

  // mem_err is in the mem_cs
  assign mem_err   = (ERR_RATE == 0) ? (mem_cs & ~iram_sel & ~dbgrom_sel) :
                     (iram_sel ? iram_err : 1'b0);

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      iram_sel_q        <= 1'b0;
      dbgrom_sel_q      <= 1'b0;
    end else begin
      iram_sel_q        <= iram_sel;
      dbgrom_sel_q      <= dbgrom_sel;
    end
  end


  assign iram_addr = mem_addr32[IRAM_AW:1];
  assign iram_sel  = mem_cs & mem_addr32[29] & (mem_addr32[28:IRAM_AW32+1] == 0);   
  assign iram_cs   = iram_sel & ~mem_err;   

  if (UnalignedFetch) begin
    always @(posedge clk) begin
      if (iram_cs && ~mem_addr32[0])
        iram_rdata <= iram[iram_addr];  
      else if (iram_cs)
        iram_rdata <= {iram[iram_addr+1][31:0], iram[iram_addr][63:32]};
    end
  end else begin
    always @(posedge clk) begin
      if (iram_cs) 
        iram_rdata <= iram[iram_addr];  
    end
  end

  localparam logic [31:0] err_keepout_base = 32'h8000_0000;
  localparam logic [31:0] err_keepout_top  = 32'h8000_01ff;

  assign iram_err = iram_err_q && ((mem_addr32 < err_keepout_base[31:2]) || 
                                   (mem_addr32 > err_keepout_top[31:2]));

  always @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
      iram_err_q    <= 1'b0;
    end else begin
      if (~err_enable)
        iram_err_q    <= 1'b0;
      else if (iram_cs)
        iram_err_q <=  (ERR_RATE == 0) ? 1'b0 : ($urandom()%(2**(8-ERR_RATE))==0);

    end
  end 
 
  // Debug ROM
  // starting at 0x8400_0000
  //
  assign dbgrom_addr   = mem_addr32[DBGROM_AW:1];
  assign dbgrom_sel    = mem_cs & (mem_addr32[29:24] == 6'h21) && (mem_addr32[23:DBGROM_AW32+1] == 0);   
  assign dbgrom_cs     = dbgrom_sel & ~mem_err;   

  if (UnalignedFetch) begin
    always @(posedge clk) begin
      if (dbgrom_cs && ~mem_addr32[0])
      dbgrom_rdata <= dbgrom[dbgrom_addr];  
      else if (dbgrom_cs)
        dbgrom_rdata <= {dbgrom[dbgrom_addr+1][31:0], dbgrom[dbgrom_addr][63:32]};
    end
  end else begin
    always @(posedge clk) begin
      if (dbgrom_cs) 
        dbgrom_rdata <= dbgrom[dbgrom_addr];  
    end
  end


endmodule
