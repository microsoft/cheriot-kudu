#.option norelax

.section .text
.globl rv32_atest

.macro PRINTMSG reg, symbol
    lui       \reg, %hi(\symbol)
    addi      \reg, \reg, %lo(\symbol)
    mv        x9, \reg
    call      print_string
.endm

print_string:                           # print a string pointed by C9
    addi sp, sp, -4
    sw x11, (sp)

    lb x11, (x9)
print_loop:
    sb x11, 512(x5)
    addi x9, x9, 0x1
    lb x11, (x9)
    bne x11, x0, print_loop

    lw x11, (sp)
    addi sp, sp, 4
    ret

#  ///////////////////////////////////////
#  Exception Handler
#  ///////////////////////////////////////

.align 4   # riscv vectors must be 4-bytes aligned

rv32_handler:
    # save context to stack QQQ
    addi sp, sp, -16    # SP-16
    sw ra, (sp) 
    sw x5, 4(sp) 
    sw x13, 8(sp) 
    sw x14, 12(sp) 

    li x13, 0x3
    sw x13, 260(x5)             # send intr_ack

    addi x14, x0, 0
    beq x15, x14, case0         # load/store fault (cheri error)
    addi x14, x0, 1
    beq x15, x14, case1         # jump fault
case0:   
    mv x12, x8 
    j echo1

case1:
    mv x12, x8 
    j echo1

echo1:
    addi x13, x0, 0x66                
    sb x13, 512(x5)                
    addi x13, x0, 0x61                
    sb x13, 512(x5)                
    addi x13, x0, 0x75                
    sb x13, 512(x5)                
    addi x13, x0, 0x6c                
    sb x13, 512(x5)                
    addi x13, x0, 0x74                
    sb x13, 512(x5)                
    addi x13, x15, 0x30      
    sb x13, 512(x5)
    addi x13, x0,0x20                
    sb x13, 512(x5)                
    addi x13, x0,0x4f                
    sb x13, 512(x5)                
    addi x13, x0,0x4b                
    sb x13, 512(x5)
    addi x13, x0, 0xa                
    sb x13, 512(x5)                
    addi x13, x0,0xd                
    sb x13, 512(x5)                

exit_handler:
    lw ra, (sp)
    lw x5, 4(sp) 
    lw x13, 8(sp) 
    lw x14, 12(sp) 
    addi sp, sp, 16    # SP+16
    mret             

#
#  Register allocation for this test
#
#  x5: 0x8380_0000 (mm_reg/uart)


#  ///////////////////////////////////////
#  init
#  ///////////////////////////////////////

test_init:
    addi sp, sp, -16
    sw ra, (sp)
    sw t1, 4(sp)

    li x5, 0x83800000            # mmreg base 

1:  auipc  t1, %pcrel_hi(rv32_handler)
    addi t1, t1, %pcrel_lo(1b)
    csrw mtvec, t1
    
    lw ra, (sp)
    addi sp, sp, 16 
    ret

#  ///////////////////////////////////////
#  load/store test
#  ///////////////////////////////////////

test_lsft:
    addi sp, sp, -32
    sw ra,(sp)
    sw x8,4(sp) 
    sw x9, 8(sp) 
    sw x12, 12(sp) 
    sw x13, 16(sp) 
    sw x14, 20(sp) 
    sw x15, 24(sp) 

    li x15, 0     # exception case 0
    li x8, 0x80010000
    sw x8, (x8)   # initialize memory location

    li x12, 0x20
    lw x13, (x12)

    li x11, 0x10
    li x12, 0x20
    sw x13, (x12)
    li x12, 0x20
    lw x13, (x12)

lsft_exit:
    lw ra, (sp)
    lw x8,4(sp) 
    lw x9, 8(sp) 
    lw x12, 12(sp) 
    lw x13, 16(sp) 
    lw x14, 20(sp) 
    lw x15, 24(sp) 
    addi sp, sp, 32
    ret

#  ///////////////////////////////////////
#  Atomic instruction test
#  ///////////////////////////////////////

test_atomic:
    addi sp, sp, -32
    sw ra,(sp)
    sw x8,4(sp) 
    sw x9, 8(sp) 
    sw x12, 12(sp) 
    sw x13, 16(sp) 
    sw x14, 20(sp) 
    sw x15, 24(sp) 

    li x8, 0x80001000
    li x9, 0x55aaaa55
    sw x9, (x8)

    # make reservation, check LR load value
    lr.w x10, (x8)
    bne x9, x10, atomic_fail

    # check reservation is made correctly
    sc.w x10, x10, (x8)
    bne x10, x0, atomic_fail
    
    # previous sc should cancel reservation
    sc.w x10, x10, (x8)
    beq x10, x0, atomic_fail

    # make reservation again
    # check a store should cancel the reservation
    lr.w x10, (x8)
    sw x10, (x8)
    sc.w x10, x10, (x8)
    beq x10, x0, atomic_fail
    
    li a0, 0
    j atomic_exit

atomic_fail:
    li a0, 0x1
    j atomic_exit

atomic_exit:
    lw ra, (sp)
    lw x8,4(sp) 
    lw x9, 8(sp) 
    lw x12, 12(sp) 
    lw x13, 16(sp) 
    lw x14, 20(sp) 
    lw x15, 24(sp) 
    addi sp, sp, 32
    ret

#  ///////////////////////////////////////
#  Interrupt test
#  ///////////////////////////////////////

test_intr:
    addi sp, sp, -32
    sw ra,(sp)
    sw x8,4(sp) 
    sw x9, 8(sp) 
    sw x12, 12(sp) 
    sw x13, 16(sp) 
    sw x14, 20(sp) 
    sw x15, 24(sp) 

    li x9, 0x800              # enable machine-mode ext/tmr/sw interrupts
    csrs mie, x9

    li x15, 3     # exception case 0
  
    li x8, 0x83800100
    li x9, 0x4
    sw x9, (x8)   # enable interrupts in testbench

    li x13, 0x40
intr_wait1:
    addi x13, x13, -1
    nop           # do something random just to see where we take interrupts
    nop
    addi x13, x13, 1
    nop 
    nop
    addi x13, x13, -1
    bne x13, x0, intr_wait1
    
    li x9, 0x0
    sw x9, 256(x5)   # disable interrupts in testbench

    li x13, 0x10
intr_wait2:
    addi x13, x13, -1
    bne x13, x0, intr_wait2
    
intr_exit:
    lw ra, (sp)
    lw x8,4(sp) 
    lw x9, 8(sp) 
    lw x12, 12(sp) 
    lw x13, 16(sp) 
    lw x14, 20(sp) 
    lw x15, 24(sp) 
    addi sp, sp, 32
    ret

test_misc:
   csrr x15, mepc
   addi x14, x15, 4
   csrw mepc, x15  
   ret
   
#  ///////////////////////////////////////
#  Assembly Test Main
#  ///////////////////////////////////////

rv32_atest:
    addi sp, sp, -16
    sw ra, (sp)
    sw x13, 4(sp)
       
    # save register context so that we won't have issue talking with the C program 
    # note RISC-V uses x10/x11 (a0/a1) for args/return values, and x12-x17 (a2-7) for args

    call test_init
    PRINTMSG x11, hello_msg

    PRINTMSG x11, test_atomic_msg
    call test_atomic
    bne a0, x0, test_exit

    PRINTMSG x11, test_lsft_msg
    call test_lsft
    bne a0, x0, test_exit

    PRINTMSG x11, test_intr_msg
    call test_intr
    bne a0, x0, test_exit

    j test_exit

test_exit:
    # restore register context
    lw x13, 4(sp)
    lw ra, (sp)
    addi sp, sp, 16 
    ret

.section .rodata

hello_msg :
  .string "Entering assembly test..\n"
test_atomic_msg :
  .string "Testing LR/SC instructions.. \n"
test_lsft_msg :
  .string "Testing load/store faults.. \n"
test_intr_msg :
  .string "Testing interrupts.. \n"

#.section .tohost
#tohost :
#  .dword 0
#fromhost :
#  .dword 0
