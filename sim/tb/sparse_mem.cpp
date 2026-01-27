#include <unordered_map>
#include <cstdint>
#include <fstream>
#include <regex>
#include <string>
#include <iostream>
#include <map>

/* ------------------------------------------------------------
 * Global sparse instruction memory
 *   key   : 64-bit aligned byte address
 *   value : 64-bit data word
 * ------------------------------------------------------------ */
static std::unordered_map<uint64_t, uint64_t> instr_mem;

/* ------------------------------------------------------------
 * instr_mem_init
 *  - Input file: 64-bit byte addr, 16-bit data
 *  - Accumulates into 64-bit aligned words
 *  - Missing lanes default to zero
 * ------------------------------------------------------------ */
extern "C" int instr_mem_init(const char* infile_name)
{
    instr_mem.clear();

    std::ifstream infile(infile_name);
    if (!infile.is_open())
        return -1;

    std::regex line_re(
        R"(mem\[X,0x([0-9A-Fa-f]+)\]\s*->\s*0x([0-9A-Fa-f]+))"
    );

    std::string line;

    while (std::getline(infile, line)) {
        std::smatch m;
        if (!std::regex_search(line, m, line_re))
            continue;

        uint64_t addr = std::stoull(m[1], nullptr, 16);
        uint16_t data16 =
            static_cast<uint16_t>(std::stoul(m[2], nullptr, 16));

        /* 64-bit aligned base address */
        uint64_t aligned_addr = addr & ~0x7ULL;

        /* 16-bit lane inside the 64-bit word */
        uint64_t lane = (addr & 0x7ULL) >> 1;  // 0..3

        if (lane >= 4)
            continue;  // should never happen for halfword-aligned input

        /* Fetch existing word (default = 0) */
        uint64_t word = instr_mem[aligned_addr];

        /* Clear and insert 16-bit lane */
        uint64_t shift = lane * 16;
        word &= ~(0xFFFFULL << shift);
        word |= (uint64_t(data16) << shift);

        instr_mem[aligned_addr] = word;
    }

    return 0;
}

/* ------------------------------------------------------------
 * instr_mem_read64
 *  - addr must be 64-bit aligned
 *  - returns assembled 64-bit word
 * ------------------------------------------------------------ */
extern "C" uint64_t instr_mem_read64(uint64_t addr)
{
    if (addr & 0x7) {
        std::cerr << "instr_mem_read64: unaligned address 0x"
                  << std::hex << addr << std::dec << "\n";
        return 0;
    }

    auto it = instr_mem.find(addr);
    if (it != instr_mem.end())
        return it->second;

    return 0;
}

/* ------------------------------------------------------------
 * instr_mem_dump
 *  - Dumps assembled 64-bit words sorted by address
 * ------------------------------------------------------------ */
extern "C" int instr_mem_dump(const char* filename)
{
    std::ofstream ofs(filename);
    if (!ofs.is_open())
        return -1;

    ofs << "INSTRUCTION MEMORY DUMP\n";
    ofs << "Entries: " << instr_mem.size() << "\n\n";

    std::map<uint64_t, uint64_t> ordered(
        instr_mem.begin(), instr_mem.end()
    );

    for (const auto& [addr, data] : ordered) {
        ofs << "addr=0x" << std::hex << addr
            << " data=0x" << data
            << std::dec << "\n";
    }

    return 0;
}

