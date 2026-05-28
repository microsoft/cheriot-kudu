// DPI import wrapper for tracer_dpi.cpp.
//
// Include/import this after rvfi_t and the CHERI capability width parameters
// are visible. The C++ top-level DPI symbol is decode_rvfi_instr. This wrapper
// keeps the SystemVerilog side convenient by accepting rvfi_t and flattening
// only scalar fields; capability payloads are passed as packed bit vectors so
// the C++ side can reproduce cheri_pkg::trace_reg_fmt/trace_mem_fmt exactly.
//

import "DPI-C" function string decode_rvfi_instr(
    input int unsigned     insn,
    input byte unsigned    trap,
    input byte unsigned    intr,
    input byte unsigned    rs1_addr,
    input byte unsigned    rs2_addr,
    input byte unsigned    rs3_addr,
    input int  unsigned    rs1_rdata_lo,
    input int unsigned       rs2_rdata_lo,
    input int unsigned       rs3_rdata_lo,
    input longint unsigned       rs1_rdata_hi,
    input longint unsigned       rs2_rdata_hi,
    input longint unsigned       rs3_rdata_hi,
    input byte unsigned    rd_addr,
    input int unsigned       rd_wdata_lo,
    input longint unsigned       rd_wdata_hi,
    input int unsigned     pc_rdata,
    input int unsigned     pc_wdata,
    input int unsigned     mem_addr,
    input byte unsigned    mem_rmask,
    input byte unsigned    mem_wmask,
    input int unsigned       mem_rdata_lo,
    input int unsigned       mem_wdata_lo,
    input longint unsigned       mem_rdata_hi,
    input longint unsigned       mem_wdata_hi,
    input byte unsigned    cheri_pmode
);

// Wrapper name avoids colliding with the imported DPI symbol above.
function automatic string decode_rvfi_instr_dpi(
    input rvfi_t rvfi_data,
    input logic  cheri_pmode
);
  int unsigned rs1_rdata_lo;
  int unsigned rs2_rdata_lo;
  int unsigned rs3_rdata_lo;
  longint unsigned rs1_rdata_hi;
  longint unsigned rs2_rdata_hi;
  longint unsigned rs3_rdata_hi;

  int unsigned rd_wdata_lo;
  longint unsigned rd_wdata_hi;

  int unsigned mem_rdata_lo;
  int unsigned mem_wdata_lo;
  longint unsigned mem_rdata_hi;
  longint unsigned mem_wdata_hi;

  rs1_rdata_hi = trace_reg_fmt(rvfi_data.rs1_rdata);
  rs2_rdata_hi = trace_reg_fmt(rvfi_data.rs2_rdata);
  rs3_rdata_hi = trace_reg_fmt(rvfi_data.rs3_rdata);
  rd_wdata_hi  = trace_reg_fmt(rvfi_data.rd_wdata);
  mem_rdata_hi = trace_reg_fmt(rvfi_data.mem_rdata);  // rvfi_t defines mem_rdata as REG_W
  mem_wdata_hi = trace_mem_fmt(rvfi_data.mem_wdata);
  //$display("mem_rdata=%x, mem_rdata_hi = %x", rvfi_data.mem_rdata, mem_rdata_hi);

  rs1_rdata_lo = rvfi_data.rs1_rdata[31:0];  
  rs2_rdata_lo = rvfi_data.rs2_rdata[31:0];
  rs3_rdata_lo = rvfi_data.rs3_rdata[31:0];
  mem_rdata_lo = rvfi_data.mem_rdata[31:0];
  mem_wdata_lo = rvfi_data.mem_wdata[31:0];
  rd_wdata_lo  = rvfi_data.rd_wdata[31:0];
  //$display("rs1_rdata=%x, rs1_rdata_hi = %x", rvfi_data.rs1_rdata, rs1_rdata_hi);

  if (rvfi_data.trap && (rvfi_data.insn[6:0] == 7'h03))
    $display("load fault: pc = %x, PA = %x", rvfi_data.pc_rdata, rvfi_data.mem_addr);

  return decode_rvfi_instr(
      rvfi_data.insn,
      byte'(rvfi_data.trap),
      byte'(rvfi_data.intr),
      byte'(rvfi_data.rs1_addr),
      byte'(rvfi_data.rs2_addr),
      byte'(rvfi_data.rs3_addr),
      rs1_rdata_lo,
      rs2_rdata_lo,
      rs3_rdata_lo,
      rs1_rdata_hi,
      rs2_rdata_hi,
      rs3_rdata_hi,
      byte'(rvfi_data.rd_addr),
      rd_wdata_lo,
      rd_wdata_hi,
      rvfi_data.pc_rdata,
      rvfi_data.pc_wdata,
      rvfi_data.mem_addr,
      byte'(rvfi_data.mem_rmask),
      byte'(rvfi_data.mem_wmask),
      mem_rdata_lo,
      mem_wdata_lo,
      mem_rdata_hi,
      mem_wdata_hi,
      byte'(cheri_pmode)
  );
endfunction
