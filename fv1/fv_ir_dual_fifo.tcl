clear -all

# use sv2017 standard
# +define+FETCH_CORRECT_FORMAL 

analyze -sv17 +define+FORMAL ../rtl/dual_fifo.sv    

# IR_stage S0 FIFO configuration
elaborate -parameter Depth 4 -parameter PplRead 1 -parameter Width 8 -parameter WrThrough 1 -top dual_fifo
 
# use clock rising edge only be default
reset ~rst_ni
clock clk_i

prove -bg -all

