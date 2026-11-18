/* Copyright Microsoft Corporation
   Licensed under the Apache License, Version 2.0, see LICENSE for details.
   SPDX-License-Identifier: Apache-2.0 */
/* cheri_stress: ISR code right after startup, ISR data/stack in
   0x80000C00..0x80000FFF; the TB never injects bus errors below 0x80001000. */
SECTIONS
{
  . = 0x80000000;
  .pcc :
  {
    HIDDEN(__pcc_start = .);
  . = 0x80000080;
    startup.o(.text)
    . = ALIGN(0x40);
    *(.text.isr)
    ASSERT(. <= 0x80000C00, "isr code must stay below the isr data area");
    . = 0x80001000;
    *(.text .text.*);
    *(.data.rel.ro);
    *(.rodata .rodata.*);
    HIDDEN(__pcc_end = .);
  }

  . = 0x80006000;
  .cgp : ALIGN(0x8)
  {
    HIDDEN(__cgp_start = .);
    *(.data .data.*);
    *(.sdata .sdata.*);
    *(.bss .bss.*);
    *(.sbss .sbss.*);
    HIDDEN(__cgp_end = .);
  }

  __cap_relocs :
  {
    __cap_relocs = .;
  }
  __cap_relocs_end = .;
}
