module kudu_branch_log #(
  parameter string log_fname = "./kudu.branch.log"
) ( 
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        start_stop
);

  `define ISSUER dut.issuer_i

  logic log_enable;
  int fd;
  int line_cnt;

  logic [1:0]  ir_branch, ir_taken, ir_miss;
  logic [31:0] ir_pc[2], ir_target[2];

  // map RTL signals
  assign ir_branch   = {(`ISSUER.ir1_issued & `ISSUER.ir1_dec.is_branch),
                        (`ISSUER.ir0_issued & `ISSUER.ir0_dec.is_branch)};
  assign ir_miss     = `ISSUER.branch_mispredict;
  assign ir_taken    = `ISSUER.branch_info_i.branch_taken;

  assign ir_pc[1]     = `ISSUER.ir1_dec.pc;
  assign ir_pc[0]     = `ISSUER.ir0_dec.pc;
  assign ir_target[1] = `ISSUER.ir1_dec.btarget;
  assign ir_target[0] = `ISSUER.ir0_dec.btarget;

  always_ff  @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      log_enable   <= 1'b0;
    end else begin
      if (start_stop) log_enable <= ~log_enable;
    end
  end

  initial begin
    int i;
    string flag_str1, flag_str2;
    @(posedge rst_ni);
    line_cnt = 0;

    repeat (3) @(posedge clk_i);
    while (~log_enable) @(posedge clk_i);

    fd = $fopen(log_fname, "w");
    if (fd == 0) $error("Error: branch_log: failed to open file");

    $fdisplay(fd, "Line Number\tPC\t\tTarget\tTaken\tMispredict");
    while (log_enable) begin
      @(posedge clk_i);
      for (i = 0; i<2; i++) begin
        if (ir_branch[i]) begin
          flag_str1 = ir_miss[i] ? "MISS" : "";
          flag_str2 = (ir_pc[i] < ir_target[i]) ? "FWD" : "BKWD";
          $fdisplay(fd, "%d\t%8x\t%8x\t%d\t%d\t%s\t%s", 
                    line_cnt, ir_pc[i], ir_target[i], ir_taken[i], ir_miss[i], flag_str1, flag_str2);
          line_cnt += 1;
        end
      end
    end

    $fclose(fd);
  end

endmodule
