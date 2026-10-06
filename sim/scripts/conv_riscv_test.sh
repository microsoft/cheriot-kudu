#!/bin/bash 
 
set -e 

source ../scripts/common_setup.sh
mkdir -p work
cd work
pwd

#export TESTNAME=hello_world
export TESTNAME=$1
export C_INC="-I$SRC -I$CSRC"
export LD_FILE=../link_test_rv32.ld

export ELF_INPUT=/home/kunyanliu/riscdev/riscv-tests/target/share/riscv-tests/isa/$TESTNAME
export BIN_OUTPUT=$TESTNAME.bin
export HEX_OUTPUT=$TESTNAME.vhx

$GCC_OBJCOPY -O binary -S $ELF_INPUT $BIN_OUTPUT
dd if=/dev/zero bs=1 count=128 of=pad.bin
cat pad.bin $BIN_OUTPUT > final.bin
$BIN2VHX final.bin > $HEX_OUTPUT

cp $HEX_OUTPUT ../../run/bin/

echo "Generating disassembled text.."
$GCC_OBJDUMP -xdCS $ELF_INPUT > $TESTNAME.dis

