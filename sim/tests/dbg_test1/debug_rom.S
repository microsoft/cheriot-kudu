.section .text
.globl _start

#.extern cheri_fault_handler

.macro LA_ABS reg, symbol
    lui             \reg, %hi(\symbol)
    addi            \reg, \reg, %lo(\symbol)
.endm

_start: 
    cspecialw 25, c5    # dscratch0/1
    cspecialw 26, c6

    # read relevant CSR registers (to show in trace)
    csrr x5, dcsr
    csrr x6, mepc       # mepc points to depc when in debug mode
    cspecialr c6, 24    # depcc

    #copy setup value from testbench registers
    li x5, 0x83800140
    csrr x6, dcsr
    csw x6, 4(c5)       # 0x83800144 (dcsr_r)
    clw x6, 8(c5)       # 0x83800148 (dcsr_w) 
    csrw dcsr, x6

    csrw tselect, x0    # tselect = 0 (trigger 0)
    clw x6, 12(c5)      # 0x8380014c (tmatch_ctrl0)
    csrw tdata1, x6
    clw x6, 20(c5)      # 0x83800154 (tmatch_val0)
    csrw tdata2, x6

    li x6, 1
    csrw tselect, x6    # tselect = 1 (trigger 1)
    clw x6, 16(c5)      # 0x83800150 (tmatch_ctrl1)
    csrw tdata1, x6
    clw x6, 24(c5)      # 0x83800158 (tmatch_val1)
    csrw tdata2, x6

    li x5, 0x83800140   # deassert debug_req
    csw x0, (c5)
    cspecialr c5, 25
    cspecialr c6, 26
    dret
