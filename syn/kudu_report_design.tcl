
write -format verilog -hier -output "${outdir}/kudu_top.gates.v"
write -format ddc -hier -output "${outdir}/kudu_top.ddc"

report_area -hier >  "${outdir}/kudu_area.rpt"
report_reference -hier >>  "${outdir}/kudu_area.rpt"

report_resources -hier > "${outdir}/kudu_resrc.rpt"
report_power -hier > "${outdir}/kudu_power.rpt"

report_timing -max_paths 100 > "${outdir}/kudu_timing.rpt"
report_timing -from clk -to clk -max_paths 100 > "${outdir}/kudu_timing_internal.rpt"

report_timing -from io_vclk -to clk -max_paths 50 > "${outdir}/kudu_timing_io.rpt"
report_timing -from clk -to io_vclk -max_paths 50 >> "${outdir}/kudu_timing_io.rpt"
report_timing -from io_vclk -to io_vclk -max_paths 50 >> "${outdir}/kudu_timing_io.rpt"
report_timing -from [get_ports data_rdata_i*] -to clk -nworst 10 >> "${outdir}/kudu_timing_io.rpt"
report_timing -from [get_ports instr_rdata_i*] -to clk -nworst 10 >> "${outdir}/kudu_timing_io.rpt"
report_timing -from clk -to [get_ports instr_req_o] -nworst 10 >> "${outdir}/kudu_timing_io.rpt"
report_timing -from clk -to [get_ports instr_addr*o] -nworst 10 >> "${outdir}/kudu_timing_io.rpt"
report_timing -from clk -to [get_ports data_req_o] -nworst 10 >> "${outdir}/kudu_timing_io.rpt"

report_timing -to  alu_pipeline0_i/ex2_reg_reg\[wdata\]\[64\]/D -max_paths 10 >> "${outdir}/kudu_timing_internal.rpt"
report_timing -to  alu_pipeline0_i/ex2_reg_reg\[wdata\]\[65\]/D -max_paths 10 >> "${outdir}/kudu_timing_internal.rpt"
report_timing -to  alu_pipeline0_i/ex2_reg_reg\[wdata\]\[66\]/D -max_paths 10 >> "${outdir}/kudu_timing_internal.rpt"
report_timing -to  alu_pipeline0_i/ex2_reg_reg\[wdata\]\[67\]/D -max_paths 10 >> "${outdir}/kudu_timing_internal.rpt"
report_timing -to  alu_pipeline0_i/ex2_reg_reg\[wdata\]\[68\]/D -max_paths 10 >> "${outdir}/kudu_timing_internal.rpt"
