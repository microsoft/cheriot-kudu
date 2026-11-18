/* Copyright Microsoft Corporation
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 * Memory map of the bare-assembly collide tests (gcc, rv32imac). */
OUTPUT_ARCH( "riscv" )
ENTRY(_start)
SECTIONS
{
  . = 0x80000000;
  .text.low : { *(.text.low) }
  . = 0x80001000;
  .text : { *(.text) }
  . = 0x80030000;
  .text.ferr : { *(.text.ferr) }
  . = 0x8003c000;
  .data : { *(.data) *(.bss) *(.sbss) }
}
