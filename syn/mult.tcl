#dc_shell-t:  Tcl mode
#dc_shell -topo: topo mode

#
set tech_id "028lp_topo"
set setupdir "setup_${tech_id}"
set outdir "mult_out"

source ${setupdir}/mtk028lp_libs.tcl
source ${setupdir}/mtk028lp_dont_use.tcl

define_design_lib WORK -path ./work
analyze -format sverilog -work WORK ../../misc/mult.sv
elaborate -work WORK mult32

source ${setupdir}/mtk028lp_layers.tcl

if {![info exists TCLK]} {
  set TCLK 2.0
}
echo "TCLK=$TCLK"

create_clock -name clk -period $TCLK [get_port clk_i]
create_clock -name io_vclk -period $TCLK 

set_input_delay  1.0 -clock io_vclk [get_ports op_*_i]
set_output_delay 1.0 -clock io_vclk [get_ports result_o]

# dc_topo doesn't support compile. Has to go compile_ultra
echo "Compiling "
#set_autoungroup_options -start_level 3  # this is not supported in 2020.09-SP1
compile_ultra -no_autoungroup
#compile_ultra 


