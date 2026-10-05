#dc_shell-t:  Tcl mode
#dc_shell -topo: topo mode

#
if {![info exists run_id]} {
  set run_id "028lp_topo"
}

set tech_id "028lp_topo"
set design_dir "../.."
set outdir "rpt_${run_id}"
exec mkdir -p $outdir
set setupdir "setup_${tech_id}"


source ${setupdir}/xx_libs.tcl
source ${setupdir}/xx_dont_use.tcl

source ../super_read_design.tcl

source ${setupdir}/xx_layers.tcl

if {![info exists TCLK]} {
  set TCLK 2.0
}
echo "TCLK=$TCLK"

create_clock -name clk -period $TCLK [get_port clk_i]
create_clock -name io_vclk -period $TCLK 

if {![info exists IO_DLY]} { 
  set IO_DLY 1.0
}

if {![info exists IMEM_DLY]} { 
  set IMEM_DLY 1.0
}

if {![info exists DMEM_DLY]} { 
  set DMEM_DLY 1.0
}

echo "IO_DLY=$IO_DLY, IMEM_DLY=$IMEM_DLY, DMEM_DLY=$DMEM_DLY "

#remove_input_delay [get_ports clk_i]
#remove_input_delay [get_ports rst_ni]

set_input_delay  [expr $IO_DLY*0.5] -clock io_vclk [get_ports irq*_i]
set_input_delay  [expr $IO_DLY] -clock io_vclk [get_ports tsmap*_i]
set_output_delay [expr $IO_DLY] -clock io_vclk [get_ports tsmap*_o]

set_input_delay  [expr $DMEM_DLY*1.2] -clock io_vclk [get_ports data*_i]
set_output_delay [expr $DMEM_DLY*0.8] -clock io_vclk [get_ports data*_o]
set_input_delay  [expr $IMEM_DLY*1.2] -clock io_vclk [get_ports instr*_i]
set_output_delay [expr $IMEM_DLY*0.8] -clock io_vclk [get_ports instr*_o]

remove_input_delay [get_ports data_rvalid_i]
remove_input_delay [get_ports data_err_i]
set_input_delay [expr $DMEM_DLY*0.5] -clock io_vclk [get_ports data_rvalid_i]
set_input_delay [expr $DMEM_DLY*0.5] -clock io_vclk [get_ports data_err_i]

source ../super_false_path.sdc

# dc_topo doesn't support compile. Has to go compile_ultra
echo "Compiling "
#set_autoungroup_options -start_level 3  # this is not supported in 2020.09-SP1
compile_ultra -no_autoungroup
#compile_ultra 

source ../super_report.tcl

