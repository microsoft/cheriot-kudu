if  {![info exists CHERIoT]} {
  set Defs "SYNTHESIS"
} else {
  set Defs "SYNTHESIS CHERIoT "
}

echo $Defs;

set search_path "../../dw/libraries ../../dw/dw/dw02/lib/dw02 $search_path"
define_design_lib WORK -path ./work
set synthetic_library dw_foundation.sldb
set link_library "* $target_library $synthetic_library"

analyze -format sverilog -work WORK -define "$Defs"\
        -vcs "+incdir+${design_dir}/rtl/" [list  \
  ${design_dir}/rtl/cheri_pkg.sv         \
  ${design_dir}/rtl/csr_pkg.sv         \
  ${design_dir}/rtl/super_pkg.sv         \
  ${design_dir}/rtl/kudu_cfg_pkg.sv         \
  ${design_dir}/rtl/dual_fifo.sv         \
  ${design_dir}/rtl/stage_fifo.sv         \
  ${design_dir}/rtl/wt_fifo.sv         \
  ${design_dir}/rtl/waw_tracking_fifo.sv         \
  ${design_dir}/rtl/regfile.sv     \
  ${design_dir}/rtl/ir_decoder.sv        \
  ${design_dir}/rtl/ir_stage.sv           \
  ${design_dir}/rtl/issuer.sv            \
  ${design_dir}/rtl/fetch_fifo64.sv      \
  ${design_dir}/rtl/prefetch_buffer64.sv \
  ${design_dir}/rtl/compressed_decoder.sv\
  ${design_dir}/rtl/branch_predict.sv      \
  ${design_dir}/rtl/if_stage.sv          \
  ${design_dir}/rtl/alu_decoder.sv       \
  ${design_dir}/rtl/rv32_alu.sv         \
  ${design_dir}/rtl/cheri_alu.sv         \
  ${design_dir}/rtl/alu_pipeline.sv     \
  ${design_dir}/rtl/load_store_unit.sv  \
  ${design_dir}/rtl/dcache.sv  \
  ${design_dir}/rtl/lsu_if.sv  \
  ${design_dir}/rtl/cheri_trvk_stage.sv  \
  ${design_dir}/rtl/ls_pipeline.sv      \
  ${design_dir}/rtl/multdiv32.sv  \
  ${design_dir}/rtl/mult_pipeline.sv   \
  ${design_dir}/rtl/committer.sv        \
  ${design_dir}/rtl/branch_unit.sv      \
  ${design_dir}/rtl/cmplx_unit.sv      \
  ${design_dir}/rtl/ibex_counter.sv      \
  ${design_dir}/rtl/ibex_csr.sv      \
  ${design_dir}/rtl/cs_registers.sv      \
  ${design_dir}/rtl/kudu_top.sv ]

if {![info exists SUPER_PARAM]} {
  set SUPER_PARAM "CHERIoTEn=0,DataWidth=32,NoMult=1,DualIssue=1"
} 
echo "SUPER_PARAM = $SUPER_PARAM"

elaborate -work WORK -param $SUPER_PARAM kudu_top
