#include <unordered_map>
#include <cstdint>
#include <fstream>
#include <regex>
#include <string>
#include <iostream>
#include <map>
#include <iomanip>

/* ------------------------------------------------------------
 * Global sparse memory model
 *   data map : 32-bit byte-addressed, byte data
 *   tag  map : 32-bit byte-addressed, byte tag
 *
 * Uninitialized reads return 0.
 * ------------------------------------------------------------ */
static std::unordered_map<uint32_t, uint8_t> sparse_mem_data;
static std::unordered_map<uint32_t, uint8_t> sparse_mem_tag;

/* ------------------------------------------------------------
 * sparse_mem_init
 *  - Input file format follows the old instr_mem input:
 *      mem[X,0xADDR] -> 0xDATA16
 *  - ADDR is a byte address.
 *  - DATA16 is 16-bit hex data.
 *  - Input is assumed 16-bit aligned.
 *  - Packs into byte map:
 *      lower 8 bits  -> sparse_mem_data[ADDR]
 *      upper 8 bits  -> sparse_mem_data[ADDR + 1]
 *  - Clears all previous data and tags.
 * ------------------------------------------------------------ */
extern "C" int sparse_mem_init(const char* infile_name)
{
    sparse_mem_data.clear();
    sparse_mem_tag.clear();

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

        uint32_t addr =
            static_cast<uint32_t>(std::stoul(m[1], nullptr, 16));
        uint16_t data16 =
            static_cast<uint16_t>(std::stoul(m[2], nullptr, 16));

        if (addr & 0x1u) {
            std::cerr << "sparse_mem_init: warning: unaligned 16-bit address 0x"
                      << std::hex << addr << std::dec << "\n";
        }

        sparse_mem_data[addr]     = static_cast<uint8_t>(data16 & 0xffu);
        sparse_mem_data[addr + 1] = static_cast<uint8_t>((data16 >> 8) & 0xffu);
    }

    return 0;
}

/* ------------------------------------------------------------
 * sparse_mem_read_data
 *  - Byte-addressed data read.
 *  - Uninitialized location returns 0.
 * ------------------------------------------------------------ */
extern "C" uint8_t sparse_mem_read_data(uint32_t addr)
{
    std::unordered_map<uint32_t, uint8_t>::const_iterator it =
        sparse_mem_data.find(addr);

    if (it != sparse_mem_data.end())
        return it->second;

    return 0;
}

/* ------------------------------------------------------------
 * sparse_mem_read_tag
 *  - Byte-addressed tag read.
 *  - Uninitialized location returns 0.
 * ------------------------------------------------------------ */
extern "C" uint8_t sparse_mem_read_tag(uint32_t addr)
{
    std::unordered_map<uint32_t, uint8_t>::const_iterator it =
        sparse_mem_tag.find(addr);

    if (it != sparse_mem_tag.end())
        return it->second;

    return 0;
}

/* ------------------------------------------------------------
 * sparse_mem_write_data
 *  - Byte-addressed data write.
 * ------------------------------------------------------------ */
extern "C" void sparse_mem_write_data(uint32_t addr, uint8_t data)
{
    sparse_mem_data[addr] = data;
}

/* ------------------------------------------------------------
 * sparse_mem_write_tag
 *  - Byte-addressed tag write.
 * ------------------------------------------------------------ */
extern "C" void sparse_mem_write_tag(uint32_t addr, uint8_t tag)
{
    sparse_mem_tag[addr] = tag;
}

/* ------------------------------------------------------------
 * sparse_mem_dump
 *  - Dumps data byte map and tag byte map separately.
 *  - Both sections are sorted by byte address.
 * ------------------------------------------------------------ */
extern "C" int sparse_mem_dump(const char* filename)
{
    std::ofstream ofs(filename);
    if (!ofs.is_open())
        return -1;

    std::map<uint32_t, uint8_t> ordered_data(
        sparse_mem_data.begin(), sparse_mem_data.end()
    );

    std::map<uint32_t, uint8_t> ordered_tag(
        sparse_mem_tag.begin(), sparse_mem_tag.end()
    );

    ofs << "SPARSE MEMORY DUMP\n";
    ofs << "\n";

    ofs << "DATA BYTE MAP\n";
    ofs << "Entries: " << ordered_data.size() << "\n";
    for (std::map<uint32_t, uint8_t>::const_iterator it = ordered_data.begin();
         it != ordered_data.end(); ++it) {
        ofs << "addr=0x" << std::hex << it->first
            << " data=0x" << std::setw(2) << std::setfill('0')
            << static_cast<unsigned int>(it->second)
            << std::setfill(' ') << std::dec << "\n";
    }

    ofs << "\n";

    ofs << "TAG BYTE MAP\n";
    ofs << "Entries: " << ordered_tag.size() << "\n";
    for (std::map<uint32_t, uint8_t>::const_iterator it = ordered_tag.begin();
         it != ordered_tag.end(); ++it) {
        ofs << "addr=0x" << std::hex << it->first
            << " tag=0x" << std::setw(2) << std::setfill('0')
            << static_cast<unsigned int>(it->second)
            << std::setfill(' ') << std::dec << "\n";
    }

    return 0;
}

