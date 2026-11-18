#!/bin/bash
# Copyright Microsoft Corporation
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# build_prog.sh <flavour>[+DEFINE[=VALUE]...] <test source dir> <output dir>
#
# Builds one test program into <output dir> as <test>.vhx/.elf/.dis, where
# <test> is the basename of the source dir. Nothing is written anywhere else
# (in particular not sim/run/bin or sim/tests/work).
#
# Flavours:
#   cheri  CHERIoT clang: test_main.c + cheri_atest.S + common/csrc_cheri
#   dbg    same as cheri (kept for the regression's existing flavour name)
#   rv32   riscv-gnu gcc: test_main.c + rv32_atest.S + common/csrc_rv32
#   asm    riscv-gnu gcc, bare assembly: test.S linked with the test's link_test.ld
# "+NAME=VALUE" suffixes are passed to the compiler as -DNAME=VALUE.
#
# If the source dir has debug_rom.S it is also built, as debug_rom.vhx
# (clang + link_dbgrom.ld for cheri/dbg, gcc at 0x84000000 for rv32/asm).
# A link_test.ld / link_test_rv32.ld / link_dbgrom.ld in the source dir
# overrides the one in common/.

set -e

if [ $# -ne 3 ]; then
  echo "usage: $0 <flavour>[+DEF=VAL...] <test source dir> <output dir>" >&2
  exit 2
fi

SPEC=$1
SRC=$(readlink -f "$2")
OUT=$3
COMMON=$(dirname "$(readlink -f "$0")")
SCRIPT_DIR=$(readlink -f "$COMMON/../../scripts")

FLAVOUR=${SPEC%%+*}
DEFS=""
if [ "$SPEC" != "$FLAVOUR" ]; then
  IFS='+' read -ra PARTS <<< "${SPEC#*+}"
  for p in "${PARTS[@]}"; do [ -n "$p" ] && DEFS="$DEFS -D$p"; done
fi

source "$SCRIPT_DIR/common_setup.sh"
BIN2VHX="perl $SCRIPT_DIR/bin2vhx64.pl"

pick() {  # pick <file name>: the test's own copy if it has one, else common/
  if [ -f "$SRC/$1" ]; then echo "$SRC/$1"; else echo "$COMMON/$1"; fi
}

NAME=$(basename "$SRC")
mkdir -p "$OUT"
cd "$OUT"

CLANG_FLAGS="-target riscv32-unknown-unknown -mcpu=cheriot -mabi=cheriot -mxcheri-rvc -mrelax -Oz -nostdlib -DCHERIOT"
GCC_BASE="-static -mcmodel=medany -march=rv32imac_zicsr -mabi=ilp32 -nostartfiles -fvisibility=hidden -ffast-math -fno-common -fno-builtin-printf -std=gnu99 -nostdlib -ffreestanding"

case "$FLAVOUR" in
  cheri|dbg)
    CSRC=$COMMON/csrc_cheri
    INC="-I$SRC -I$CSRC"
    $CLANG $CLANG_FLAGS $DEFS $INC -c "$CSRC/startup.S"
    $CLANG $CLANG_FLAGS $DEFS $INC -T"$(pick link_test.ld)" -o "$NAME.elf" \
      "$SRC/test_main.c" "$SRC/cheri_atest.S" "$CSRC/cstart.c" "$CSRC/util.c" startup.o
    $LLVM_HOME/llvm-objdump -xdCS --mcpu=cheriot "$NAME.elf" > "$NAME.dis"
    ;;
  rv32)
    CSRC=$COMMON/csrc_rv32
    INC="-I$SRC -I$CSRC"
    $GCC $GCC_BASE $DEFS $INC -c "$CSRC/startup.S" "$CSRC/vector.S" "$SRC/rv32_atest.S"
    $GCC $GCC_BASE -DNDEBUG $DEFS $INC -O2 -T"$(pick link_test_rv32.ld)" -o "$NAME.elf" \
      "$SRC/test_main.c" "$CSRC/cstart.c" "$CSRC/util.c" startup.o vector.o rv32_atest.o
    $GCC_OBJDUMP -xdCS "$NAME.elf" > "$NAME.dis"
    ;;
  asm)
    $GCC -march=rv32imac_zicsr -mabi=ilp32 -nostdlib -nostartfiles -static $DEFS -I"$SRC" \
      -T"$SRC/link_test.ld" -o "$NAME.elf" "$SRC/test.S"
    $GCC_OBJDUMP -d "$NAME.elf" > "$NAME.dis"
    ;;
  *)
    echo "build_prog.sh: unknown flavour '$FLAVOUR'" >&2
    exit 2
    ;;
esac
$GCC_OBJCOPY -O binary -S "$NAME.elf" "$NAME.bin"
$BIN2VHX "$NAME.bin" > "$NAME.vhx"

if [ -f "$SRC/debug_rom.S" ]; then
  case "$FLAVOUR" in
    cheri|dbg)
      $CLANG $CLANG_FLAGS $DEFS -I"$SRC" -T"$(pick link_dbgrom.ld)" -o debug_rom.elf "$SRC/debug_rom.S"
      $LLVM_HOME/llvm-objdump -xdCS --mcpu=cheriot debug_rom.elf > debug_rom.dis
      ;;
    *)
      $GCC -march=rv32imac_zicsr -mabi=ilp32 -nostdlib -nostartfiles -static $DEFS -I"$SRC" \
        -Ttext=0x84000000 -o debug_rom.elf "$SRC/debug_rom.S"
      $GCC_OBJDUMP -d debug_rom.elf > debug_rom.dis
      ;;
  esac
  $GCC_OBJCOPY -O binary -S debug_rom.elf debug_rom.bin
  $BIN2VHX debug_rom.bin > debug_rom.vhx
fi
echo "BUILD OK $NAME ($SPEC) -> $OUT"
