clear -all
set rtlRoot ../rtl
#set primRoot ../../../prim

set Vdef "+define+KUDU_FORMAL_G1"
#set Vdef "+define+KUDU_FORMAL_G3"
analyze -sv17 $Vdef -f ./kudu.jp.f    

elaborate -parameter CHERIoTEn 1 -parameter PipeCfg 1 -parameter DCacheEn 0 -top kudu_top
 
# use clock rising edge only be default
reset ~rst_ni
clock clk_i

prove -bg -all

