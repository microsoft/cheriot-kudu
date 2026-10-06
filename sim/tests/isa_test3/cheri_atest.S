#.option norelax

.section .text
#.globl cheri_fault_handler
.globl cheri_atest

.macro PRINTMSG reg, symbol
    lui        \reg, %hi(\symbol)
    addi       \reg, \reg, %lo(\symbol)
    csetaddr   c9, c6, \reg
    ccall      print_string
.endm

print_string:                           # print a string pointed by C9
    cincoffset csp, csp, -8
    csc c11, (csp)

    clb x11, (c9)
print_loop:
    csb x11, 512(c5)
    cincoffset c9, c9, 0x1
    clb x11, (c9)
    bne x11, x0, print_loop

    clc c11, (csp)
    cincoffset csp, csp, 8
    cret

#
#  Register allocation for this test
#
#   Globals
#   --  c2: as the stack capability (created at startup)
#   --  c3: as a "full" memory capability (entire address space)  
#   --  c4: base capability for code execution from SRAM (code r/x)
#   --  c5: base capability for peripheral accesses in tb_top 
#   --  c6: base capability for accessing SRAM (data and cap r/w)
#   --  c7: reserved for further use 
#
#   --  x1/cra: return address  
#   --  x10/a0: argument/return value for subroutines
#   --  x15/a5: is used to pass "argument" to the fault handler.
#
#   --  x8, x9(s0,s1): temp variables
#   --  x11-x14 (a1-a4): temp varaibles


#  ///////////////////////////////////////
#  --- CHERI fault hander 
#      - called by the exception handler (startup)
#  ///////////////////////////////////////

.align 4   # riscv vectors must be 4-bytes aligned

cheri_fault_handler:
    # save context to stack QQQ
    cincoffset csp, csp, -24    # SP-16
    csc cra, (csp) 
    csc c13, 8(csp) 
    csc c14, 16(csp) 

    addi x14, x0, 0
    beq x15, x14, case0         # load/store fault (cheri error)
    addi x14, x0, 1
    beq x15, x14, case1         # jump fault
    addi x14, x0, 3
    beq x15, x14, case3         # misc fault
    addi x14, x0, 5
    beq x15, x14, case5         # pcc fault
    addi x14, x0, 6
    beq x15, x14, case6         # pcc fault
    addi x14, x0, 7
    beq x15, x14, case7         # pcc fault
    addi x14, x0, 8 
    beq x15, x14, case8         # pcc fault

    j echo1

case0:   
    # cmove c12, c8             # not used
    j echo1

case1:
    #csetaddr c8, c4, x11       # not used
    j echo1

case3:
    #cspecialw mepcc, c8        # not used
    j echo1

case5:
    cspecialw mepcc, c8       # restart the faulted instruction with a good cap
    j echo1    

case6:
    cspecialr c13, mepcc
    cspecialw mscratchc, c13
    li x15, 7                 # move on the case 7 to recover from the fault
    j echo1    

case7:
    cspecialw mepcc, c8       # restart the faulted instruction with a good cap
    j echo1 
   
case8:
    cspecialw mepcc, c8       # restart the faulted instruction with a good cap
    j echo1    

echo1:
    addi x13, x0, 0x66                
    csb x13, 512(c5)                
    addi x13, x0, 0x61                
    csb x13, 512(c5)                
    addi x13, x0, 0x75                
    csb x13, 512(c5)                
    addi x13, x0, 0x6c                
    csb x13, 512(c5)                
    addi x13, x0, 0x74                
    csb x13, 512(c5)                
    addi x13, x15, 0x30      
    csb x13, 512(c5)
    addi x13, x0,0x20                
    csb x13, 512(c5)                
    addi x13, x0,0x4f                
    csb x13, 512(c5)                
    addi x13, x0,0x4b                
    csb x13, 512(c5)
    addi x13, x0, 0xa                
    csb x13, 512(c5)                
    addi x13, x0,0xd                
    csb x13, 512(c5)                

exit_handler:
    clc cra, (csp) 
    clc c13, 8(csp) 
    clc c14, 16(csp) 
    cincoffset csp, csp, 24    # SP+16
    mret             


#  ///////////////////////////////////////
#  init
#  ///////////////////////////////////////

test_init:
    # setup fault handler for this test suite
    cspecialr ct0, mtcc
1:  auipcc  ct1, %cheri_compartment_pccrel_hi(cheri_fault_handler)
    cincoffset ct1, ct1, %cheri_compartment_pccrel_lo(1b)
    csetaddr ct0, ct0, t1
    cspecialw mtcc, ct0

    cspecialrw c3, mtdc, c0    # read MTDC address 'd29, memory root

    lui x11, 0x83800   
    csetaddr c5, c3, x11      # set base address to 0x8400_0000
    csetboundsimm c5, c5, 0x800   # set bounds to 0x800
    addi x11, x0, 0x24            
    candperm c5, c5, x11      # load/store data permission only 

    lui x11, 0x80000   
    csetaddr c6, c3, x11      # set base address to 0x8000_0000
    lui x11, 0x4000   
    csetbounds c6, c6, x11    # set lengths to 0x400_0000
    addi x11, x0, 0x7f    
    candperm c6, c6, x11      # full mem data/cap permission only
   
    auipcc c4, 0             # get PCC capability
    lui x11, 0x80000   
    csetaddr c4, c4, x11      # set address to 0x8000_0000
    lui x11, 0x40   
    csetbounds c4, c4, x11    # set length to 0x80000
   
    cspecialr c7, mscratchc   # sealing root

    li a0, 0x0
    cret

#  ///////////////////////////////////////
#  Test PCC fetch faults and mepcc, test 1
#  ///////////////////////////////////////

test_misc:
    cincoffset csp, csp, -48    
    csc c8,  0(csp)                
    csc c9,  8(csp)                
    csc c11, 16(csp)                
    csc c12, 24(csp)                
    csc c13, 32(csp)                
    csc c14, 40(csp)

    fence 
    csrr x15, mcycle
    csrr x15, mcycle
    csrr x15, mcycle
    csrr x15, mcycle
    nop
    nop
    csrr x14, mcycle
    csrr x13, mcycle

    #c.lwsp x10, 16
    .half 0x5866                

misc_exit:
    clc c8,  0(csp)                
    clc c9,  8(csp)                
    clc c11, 16(csp)                
    clc c12, 24(csp)                
    clc c13, 32(csp)                
    clc c14, 40(csp)                
    cincoffset csp, csp, 48    
    cret

#  ///////////////////////////////////////
#  --- cheri_test (main test for CHERI instructions)
#  ///////////////////////////////////////

cheri_atest:
    # save register context so that we won't have issue talking with the C program 
    # note RISC-V uses x10/x11 (a0/a1) for args/return values, and x12-x17 (a2-7) for args
    cincoffset csp, csp, -64    
    csc c1, 0(csp)                
    csc c3, 8(csp)                
    csc c4, 16(csp)                
    csc c5, 24(csp)                
    csc c6, 32(csp)                
    csc c7, 40(csp)                
    csc c8, 48(csp)                
    csc c9, 56(csp)                

    ccall test_init
    PRINTMSG x11, hello_msg

    PRINTMSG x11, test_misc_msg
    ccall test_misc
    bne a0, x0, test_exit

test_exit:
    # restore register context
    clc c1, 0(csp)                
    clc c3, 8(csp)                
    clc c4, 16(csp)                
    clc c5, 24(csp)                
    clc c6, 32(csp)                
    clc c7, 40(csp)                
    clc c8, 48(csp)                
    clc c9, 56(csp)                
    cincoffset csp, csp, 64

    cret

.section .rodata

hello_msg :
  .string "Running assembly test suite\n"
test_misc_msg :
  .string "Testing MISC cases.. \n"

#.section .tohost
#tohost :
#  .dword 0
#fromhost :
#  .dword 0
