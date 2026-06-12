#!/usr/bin/env python3

from elftools.elf.elffile import ELFFile
import argparse

def elf_to_mem16(elf_path, out_path, x_name="X", use_paddr=True, include_bss=True):
    with open(elf_path, "rb") as f, open(out_path, "w") as out:
        elf = ELFFile(f)

        for seg in elf.iter_segments():
            if seg["p_type"] != "PT_LOAD":
                continue

            base_addr = seg["p_paddr"] if use_paddr else seg["p_vaddr"]
            file_size = seg["p_filesz"]
            mem_size  = seg["p_memsz"]

            data = bytearray(seg.data())

            # Optional zero-fill for .bss-like part of PT_LOAD
            if include_bss and mem_size > file_size:
                data.extend(b"\x00" * (mem_size - file_size))

            # Emit 16-bit words
            for offset in range(0, len(data), 2):
                addr = base_addr + offset
                chunk = data[offset:offset + 2]

                # Pad final odd byte, if needed
                if len(chunk) == 1:
                    chunk.append(0)

                # Little-endian 16-bit word:
                # byte at addr is low byte, byte at addr+1 is high byte
                word = chunk[0] | (chunk[1] << 8)

                out.write(f"mem[{x_name},0x{addr:08X}] -> 0x{word:04X}\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("elf")
    parser.add_argument("out")
    parser.add_argument("--x", default="X", help="Name/index to put in mem[X,addr]")
    parser.add_argument("--vaddr", action="store_true", help="Use p_vaddr instead of p_paddr")
    parser.add_argument("--no-bss", action="store_true", help="Do not emit zero-fill for p_memsz > p_filesz")
    args = parser.parse_args()

    elf_to_mem16(
        args.elf,
        args.out,
        x_name=args.x,
        use_paddr=not args.vaddr,
        include_bss=not args.no_bss,
    )
