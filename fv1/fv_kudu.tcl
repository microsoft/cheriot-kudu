proc run_fv {Vdef} {
  clear -all
  set rtlRoot ../rtl

  analyze -sv17 $Vdef -f ./kudu.jp.f    

  elaborate -parameter CHERIoTEn 1 -parameter PipeCfg 1 -parameter DCacheEn 0 -top kudu_top
   
  # use clock rising edge only be default
  reset ~rst_ni
  clock clk_i

  #prove -bg -all
  prove -all
  puts "Done FV with $Vdef ----------------------------------------------"
}

proc run_all {} {
  redirect -file jp_out.log -force  {run_fv  "+define+KUDU_FORMAL_G0"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G1_0"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G1_1"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G1_2"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G2"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G3_0"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G3_1"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G4"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G5"}
}
