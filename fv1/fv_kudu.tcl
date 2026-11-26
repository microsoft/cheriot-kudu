proc run_fv {Vdef} {
  clear -all
  set rtlRoot ../rtl

  analyze -sv17 $Vdef -f ./kudu.jp.f    

  elaborate -parameter CHERIoTEn 1 -parameter CFG KuduCfg1 -top kudu_top
   
  # use clock rising edge only be default
  reset ~rst_ni
  clock clk_i

  #prove -bg -all
  prove -all
  puts "Done FV with $Vdef ----------------------------------------------"
}

# G0_Long: the targets only prove quickly once the helper lemmas (fv_long_help_*
# modules in module_fv_ext.sv) are proven and assumed. prove -all does not reliably
# reuse helpers proven during the same run, so prove them one by one in dependency
# order, turn each proven one into an assumption, then prove the rest (~5 min total).
proc run_fv_long {{Vdef "+define+KUDU_FORMAL_G0_Long"}} {
  clear -all
  set rtlRoot ../rtl

  analyze -sv17 $Vdef -f ./kudu.jp.f
  elaborate -parameter CHERIoTEn 1 -parameter CFG KuduCfg1 -top kudu_top
  reset ~rst_ni
  clock clk_i

  set helpers {
    AssertHxSbdValid AssertHxLsNotRdyHold AssertHbPlLegalAll AssertHbCnt
    AssertHfaAlu0Eq AssertHfaAlu1Eq AssertHfaMulEq AssertHfaAlu0Claim AssertHfaAlu1Claim
    AssertHfaMulEx2Claim AssertHfaMulWbClaim AssertHfaIraRdWe AssertHfaIrbRdWe AssertHfaCmplxNoLs
    AssertHfaLsCnt AssertHfaLsHold AssertHfaLsDly0 AssertHfaLsDly1 AssertHfaLsReqHead
    AssertHfaLsEntClaim AssertHfaLsFwdClaim
    AssertHpcSpecSetpc AssertHpcExcSetpc AssertHpcFsmOH AssertHpcS0Status AssertHpcS1Full
    AssertHpcIfAddrP AssertHpcBootEmpty AssertHpcS1PtakenCti0 AssertHpcS1PtakenCti1
    AssertHpcSpecValid AssertHpcStepUnk AssertHpcSpecCase AssertHpcS1Excl0 AssertHpcS1Excl1
    AssertHpcChainAll AssertHpcCmplxExcl AssertHpcCmplxExcl2 AssertHpcWbFv AssertHpcDcV0
    AssertHpcLsIfMatch AssertHpcLdWeIss AssertHpcLdWePend AssertHpcAmoNoCache AssertHpcFwdLiveAll
    AssertHpcFwdOH AssertHpcPLock AssertHpcStepEsc AssertHpcS1Pl0 AssertHpcS1Pl1
    AssertHpcFwdCanonLS AssertHpcFwdCanonM AssertHpcFwd0Canon AssertHpcAluQ AssertHpcFwdCanonA0
    AssertHpcFwdCanonA1 AssertHpcOpA AssertHpcOpB AssertHpcOpCanon AssertHpcPCjalrComb
    AssertHpcPCjalr AssertHpcPccAll
  }
  set all [get_property_list -include {type assert}]
  foreach h $helpers {
    foreach p $all {
      if {![string match "*.$h" $p]} continue
      # prove -property takes glob patterns, so generate-block brackets become ?
      prove -property [list [string map {[ ? ] ?} $p]] -engine_mode {N Tri AM I Hp} -time_limit 10m
      set st [get_property_info $p -list status]
      puts "Helper $st: $p"
      if {$st eq "proven"} { assume -from_assert $p -remove_original }
    }
  }

  prove -all
  puts "Done FV with $Vdef ----------------------------------------------"
}

proc run_all {} {
  redirect -file jp_out.log -force  {run_fv  "+define+KUDU_FORMAL_G0_0"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G1_0"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G1_1"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G2"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G3"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G4_0"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G4_1"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G5"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G6"}
  redirect -file jp_out.log -append {run_fv  "+define+KUDU_FORMAL_G7"}
  redirect -file jp_out.log -append {run_fv_long}

}
