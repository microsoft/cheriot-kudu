
`timescale 1ns/1ps


module tb_fifo;

  logic         clk;
  logic         rst_n;

  logic [1:0]   wr_valid;
  logic [31:0]  wr_data0;
  logic [31:0]  wr_data1;
  logic [1:0]   wr_rdy; 

  logic [1:0]   rd_rdy;
  logic [1:0]   rd_valid;
  logic [31:0]  rd_data0;
  logic [31:0]  rd_data1;
`ifdef STAGE_FIFO
  stage_fifo # (.Depth(2), .Width(32)) dut (
    .clk_i      (clk      ),
    .rst_ni     (rst_n    ),
    .flush_i    (1'b0     ),
    .wr_valid_i (wr_valid ),
    .wr_data0_i (wr_data0 ),
    .wr_data1_i (wr_data1 ),
    .wr_rdy_o   (wr_rdy   ),
    .rd_rdy_i   (rd_rdy   ),
    .rd_valid_o (rd_valid ),
    .rd_data0_o (rd_data0 ),
    .rd_data1_o (rd_data1 )
    );
`else
  dual_fifo # (.Depth(8), .Width(32), .PplRead(1'b1), .WrThrough(1'b1)) dut (
    .clk_i      (clk      ),
    .rst_ni     (rst_n    ),
    .flush_i    (1'b0     ),
    .wr_valid_i (wr_valid ),
    .wr_data0_i (wr_data0 ),
    .wr_data1_i (wr_data1 ),
    .wr_rdy_o   (wr_rdy   ),
    .rd_rdy_i   (rd_rdy   ),
    .rd_valid_o (rd_valid ),
    .rd_data0_o (rd_data0 ),
    .rd_data1_o (rd_data1 )
  );
`endif

  logic [1:0] wr_num, rd_num;
  logic [31:0] wr_total, rd_total;


  assign wr_num = (wr_rdy[1] & wr_valid[1]) + (wr_rdy[0] & wr_valid[0]);
  assign rd_num = (rd_rdy[0] & rd_valid[0]) + (rd_rdy[1] & rd_valid[1]);

  // Generate clk
  initial begin
    clk = 1'b0;
    forever begin
      #5 clk = ~clk;
    end
  end

  initial begin
    rst_n = 1'b1;
    #0 $fsdbDumpfile("tb_fifo.fsdb");
    $fsdbDumpvars(0, "+all", tb_fifo); 
    #1;
    rst_n = 1'b0;

    repeat (3) @(posedge clk)
    rst_n = 1'b1;
  end

  logic [31:0] rand1;
  logic [31:0] src_data;

  // write side
  initial begin
    int i;

    rand1 = 0;

    @(posedge rst_n);
    repeat (3) @(posedge clk)

    while (i < 1000) begin
      @(posedge clk);
      rand1 = $urandom();
      #1;  // sample status from read side
      i++;
    end

    rand1 = 0;
    repeat (100) @(posedge clk);

    $display("%d words written, %d words read", wr_total, rd_total);
    repeat (10) @(posedge clk);
    $finish;
  end

  assign wr_data1 = wr_data0 + 1;
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      wr_valid <= 2'b00;
      wr_data0 <= 32'h12345678;
      wr_total <= 0;
    end else begin
      wr_valid <= {rand1[1] & rand1[0], rand1[0]};
      
      wr_data0 <= wr_data0 + wr_num;
      wr_total <= wr_total + wr_num;
    end
  end

  logic [31:0] exp_data;
  logic [31:0] rand2;

  // read side
  initial begin
    int i;

    rand2 = 0;
    @(posedge rst_n);
    repeat (3) @(posedge clk)

    while (1) begin
      @(posedge clk);
      #1;
      rand2 = $urandom();
      if (rd_valid[0] && rd_rdy[0] && (rd_data0 != exp_data)) 
        $error("Rx0: %x != %x", rd_data0, exp_data);
      if (rd_valid[1] & rd_rdy[1] && (rd_data1 != (exp_data+1))) 
        $error("Rx1: %x != %x", rd_data1, (exp_data+1));
    end

  end

  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      rd_rdy   <= 2'b00;
      rd_total <= 0;
      exp_data <= 32'h12345678;
    end else begin
      rd_rdy <= {rand2[1] & rand2[0], rand2[0]};
      exp_data <= exp_data + rd_num;
      rd_total <= rd_total + rd_num;
    end
  end 


endmodule
