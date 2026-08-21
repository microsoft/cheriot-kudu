#include <elf.h>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <regex>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

#ifndef EM_RISCV
#define EM_RISCV 243
#endif

namespace {

using SparseByteMap = std::unordered_map<uint32_t, uint8_t>;

/*
 * Global, byte-addressed sparse memory.  Missing entries read as zero.
 * Capability tags are stored separately at the aligned capability address.
 */
SparseByteMap sparse_mem_data;
SparseByteMap sparse_mem_tag;

enum SparseMemStatus {
    SparseMemOk = 0,
    SparseMemOpenError = -1,
    SparseMemFormatError = -2,
    SparseMemIoError = -3,
};

int report_error(const char *function_name, int status,
                 const std::string &message)
{
    std::cerr << function_name << ": " << message << '\n';
    return status;
}

bool read_at(std::ifstream &input, uint64_t offset, void *destination,
             std::size_t size)
{
    if (offset > static_cast<uint64_t>(
                     std::numeric_limits<std::streamoff>::max()) ||
        size > static_cast<std::size_t>(
                   std::numeric_limits<std::streamsize>::max())) {
        return false;
    }

    input.clear();
    input.seekg(static_cast<std::streamoff>(offset), std::ios::beg);
    if (!input.good()) {
        return false;
    }

    input.read(static_cast<char *>(destination),
               static_cast<std::streamsize>(size));
    return input.good() ||
           input.gcount() == static_cast<std::streamsize>(size);
}

bool range_fits_file(uint64_t offset, uint64_t size, uint64_t file_size)
{
    return offset <= file_size && size <= file_size - offset;
}

bool range_fits_address_space(uint64_t address, uint64_t size)
{
    constexpr uint64_t AddressSpaceSize = uint64_t{1} << 32;
    return address < AddressSpaceSize && size <= AddressSpaceSize - address;
}

/*
 * Represent a zero-filled range by removing any entries already present.
 * This preserves correct behavior for overlapping PT_LOAD segments without
 * allocating map entries for a potentially large BSS region.
 */
void clear_range(SparseByteMap &memory, uint64_t start, uint64_t size)
{
    if (size == 0 || memory.empty()) {
        return;
    }

    const uint64_t end = start + size;
    for (SparseByteMap::iterator it = memory.begin(); it != memory.end();) {
        const uint64_t address = it->first;
        if (address >= start && address < end) {
            it = memory.erase(it);
        } else {
            ++it;
        }
    }
}

bool is_little_endian_host()
{
    const uint16_t value = 1;
    return *reinterpret_cast<const uint8_t *>(&value) == 1;
}

} // namespace

/*
 * Initialize sparse memory from the legacy DII text format:
 *
 *   mem[X,0xADDR] -> 0xDATA16
 *
 * ADDR is a byte address and DATA16 is stored little endian.  Existing data
 * and tags are cleared before the file is parsed.
 */
extern "C" int sparse_mem_init(const char *infile_name)
{
    sparse_mem_data.clear();
    sparse_mem_tag.clear();

    if (infile_name == nullptr) {
        return report_error("sparse_mem_init", SparseMemOpenError,
                            "input filename is null");
    }

    std::ifstream input(infile_name);
    if (!input.is_open()) {
        return report_error("sparse_mem_init", SparseMemOpenError,
                            std::string("cannot open '") + infile_name + "'");
    }

    const std::regex line_pattern(
        R"(mem\[X,0x([0-9A-Fa-f]+)\]\s*->\s*0x([0-9A-Fa-f]+))");

    std::string line;
    while (std::getline(input, line)) {
        std::smatch match;
        if (!std::regex_search(line, match, line_pattern)) {
            continue;
        }

        try {
            const unsigned long parsed_address =
                std::stoul(match[1].str(), nullptr, 16);
            const unsigned long parsed_data =
                std::stoul(match[2].str(), nullptr, 16);

            if (parsed_address > std::numeric_limits<uint32_t>::max() ||
                parsed_data > std::numeric_limits<uint16_t>::max()) {
                return report_error("sparse_mem_init", SparseMemFormatError,
                                    "address or data value is out of range");
            }

            const uint32_t address = static_cast<uint32_t>(parsed_address);
            const uint16_t data = static_cast<uint16_t>(parsed_data);

            if (address == std::numeric_limits<uint32_t>::max()) {
                return report_error(
                    "sparse_mem_init", SparseMemFormatError,
                    "16-bit word crosses the 32-bit address boundary");
            }

            if ((address & 1U) != 0) {
                std::cerr
                    << "sparse_mem_init: warning: unaligned 16-bit address 0x"
                    << std::hex << address << std::dec << '\n';
            }

            sparse_mem_data[address] = static_cast<uint8_t>(data & 0xffU);
            sparse_mem_data[address + 1] =
                static_cast<uint8_t>((data >> 8) & 0xffU);
        } catch (const std::exception &error) {
            return report_error("sparse_mem_init", SparseMemFormatError,
                                std::string("invalid input value: ") +
                                    error.what());
        }
    }

    if (input.bad()) {
        return report_error("sparse_mem_init", SparseMemIoError,
                            "error while reading input file");
    }

    return SparseMemOk;
}

/*
 * Initialize sparse memory directly from an ELF executable.
 *
 * The loader accepts ELF32, little-endian, RISC-V ET_EXEC files and copies
 * only PT_LOAD program segments.  Segment contents are placed at p_paddr.
 * The p_memsz - p_filesz tail is zero-filled sparsely.  Section headers are
 * deliberately ignored, so non-allocatable metadata sections are not loaded.
 *
 * Data memory is replaced only after the whole ELF has been validated and
 * read successfully.  ELF does not encode CHERIoT memory tags, so the tag map
 * is cleared on success.
 */
extern "C" int sparse_mem_init_elf(const char *elf_name)
{
    static const char *FunctionName = "sparse_mem_init_elf";

    if (elf_name == nullptr) {
        return report_error(FunctionName, SparseMemOpenError,
                            "input filename is null");
    }
    if (!is_little_endian_host()) {
        return report_error(FunctionName, SparseMemFormatError,
                            "this build requires a little-endian host");
    }

    std::ifstream input(elf_name, std::ios::binary);
    if (!input.is_open()) {
        return report_error(FunctionName, SparseMemOpenError,
                            std::string("cannot open '") + elf_name + "'");
    }

    input.seekg(0, std::ios::end);
    const std::streamoff file_end = input.tellg();
    if (file_end < 0) {
        return report_error(FunctionName, SparseMemIoError,
                            "cannot determine ELF file size");
    }
    const uint64_t file_size = static_cast<uint64_t>(file_end);

    Elf32_Ehdr elf_header{};
    if (!read_at(input, 0, &elf_header, sizeof(elf_header))) {
        return report_error(FunctionName, SparseMemIoError,
                            "cannot read ELF header");
    }

    if (std::memcmp(elf_header.e_ident, ELFMAG, SELFMAG) != 0) {
        return report_error(FunctionName, SparseMemFormatError,
                            "invalid ELF magic");
    }
    if (elf_header.e_ident[EI_CLASS] != ELFCLASS32) {
        return report_error(FunctionName, SparseMemFormatError,
                            "ELF file is not ELF32");
    }
    if (elf_header.e_ident[EI_DATA] != ELFDATA2LSB) {
        return report_error(FunctionName, SparseMemFormatError,
                            "ELF file is not little endian");
    }
    if (elf_header.e_ident[EI_VERSION] != EV_CURRENT ||
        elf_header.e_version != EV_CURRENT) {
        return report_error(FunctionName, SparseMemFormatError,
                            "unsupported ELF version");
    }
    if (elf_header.e_machine != EM_RISCV) {
        return report_error(FunctionName, SparseMemFormatError,
                            "ELF machine is not RISC-V");
    }
    if (elf_header.e_type != ET_EXEC) {
        return report_error(FunctionName, SparseMemFormatError,
                            "ELF type is not ET_EXEC");
    }
    if (elf_header.e_ehsize != sizeof(Elf32_Ehdr)) {
        return report_error(FunctionName, SparseMemFormatError,
                            "unexpected ELF header size");
    }
    if (elf_header.e_phnum == PN_XNUM) {
        return report_error(
            FunctionName, SparseMemFormatError,
            "extended program-header numbering is unsupported");
    }
    if (elf_header.e_phnum != 0 &&
        elf_header.e_phentsize != sizeof(Elf32_Phdr)) {
        return report_error(FunctionName, SparseMemFormatError,
                            "unexpected program-header size");
    }

    const uint64_t program_headers_size =
        static_cast<uint64_t>(elf_header.e_phnum) * elf_header.e_phentsize;
    if (!range_fits_file(elf_header.e_phoff, program_headers_size, file_size)) {
        return report_error(FunctionName, SparseMemFormatError,
                            "program-header table is outside the ELF file");
    }

    std::vector<Elf32_Phdr> load_segments;
    for (uint16_t index = 0; index < elf_header.e_phnum; ++index) {
        Elf32_Phdr program_header{};
        const uint64_t header_offset =
            static_cast<uint64_t>(elf_header.e_phoff) +
            static_cast<uint64_t>(index) * elf_header.e_phentsize;

        if (!read_at(input, header_offset, &program_header,
                     sizeof(program_header))) {
            return report_error(FunctionName, SparseMemIoError,
                                "cannot read a program header");
        }

        if (program_header.p_type != PT_LOAD) {
            continue;
        }
        if (program_header.p_filesz > program_header.p_memsz) {
            return report_error(FunctionName, SparseMemFormatError,
                                "PT_LOAD p_filesz is greater than p_memsz");
        }
        if (!range_fits_file(program_header.p_offset,
                             program_header.p_filesz, file_size)) {
            return report_error(FunctionName, SparseMemFormatError,
                                "PT_LOAD file range is outside the ELF file");
        }
        if (!range_fits_address_space(program_header.p_paddr,
                                      program_header.p_memsz)) {
            return report_error(FunctionName, SparseMemFormatError,
                                "PT_LOAD range exceeds 32-bit addressing");
        }

        load_segments.push_back(program_header);
    }

    if (load_segments.empty()) {
        return report_error(FunctionName, SparseMemFormatError,
                            "ELF file has no PT_LOAD segments");
    }

    SparseByteMap loaded_data;
    constexpr std::size_t BufferSize = 64 * 1024;
    std::vector<uint8_t> buffer(BufferSize);

    for (const Elf32_Phdr &segment : load_segments) {
        const uint64_t load_address = segment.p_paddr;

        // Establish the segment's zero-filled memory image first.  This also
        // handles overlaps with earlier PT_LOAD segments correctly.
        clear_range(loaded_data, load_address, segment.p_memsz);

        uint64_t bytes_remaining = segment.p_filesz;
        uint64_t file_offset = segment.p_offset;
        uint64_t memory_address = load_address;

        while (bytes_remaining != 0) {
            const std::size_t chunk_size = static_cast<std::size_t>(
                std::min<uint64_t>(bytes_remaining, buffer.size()));

            if (!read_at(input, file_offset, buffer.data(), chunk_size)) {
                return report_error(FunctionName, SparseMemIoError,
                                    "cannot read PT_LOAD contents");
            }

            for (std::size_t index = 0; index < chunk_size; ++index) {
                // A missing entry already reads as zero.  Omitting zero bytes
                // keeps executable and data images genuinely sparse.
                if (buffer[index] != 0) {
                    loaded_data[static_cast<uint32_t>(memory_address + index)] =
                        buffer[index];
                }
            }

            bytes_remaining -= chunk_size;
            file_offset += chunk_size;
            memory_address += chunk_size;
        }
    }

    sparse_mem_data.swap(loaded_data);
    sparse_mem_tag.clear();
    return SparseMemOk;
}

/* Overlay 65-bit address:data entries without clearing the ELF image. */
extern "C" int sparse_mem_load_addata(const char *addata_name)
{
    static const char *FunctionName = "sparse_mem_load_addata";
    if (addata_name == nullptr) {
        return report_error(FunctionName, SparseMemOpenError,
                            "input filename is null");
    }

    std::ifstream input(addata_name);
    if (!input.is_open()) {
        return report_error(FunctionName, SparseMemOpenError,
                            std::string("cannot open '") + addata_name + "'");
    }

    struct Entry {
        uint32_t address;
        uint64_t data;
        uint8_t tag;
    };
    std::vector<Entry> entries;
    std::string line;
    unsigned line_number = 0;
    while (std::getline(input, line)) {
        ++line_number;
        const std::size_t comment = line.find('#');
        if (comment != std::string::npos) {
            line.erase(comment);
        }
        line.erase(std::remove_if(line.begin(), line.end(),
                                  [](unsigned char character) {
                                      return std::isspace(character) != 0;
                                  }),
                   line.end());
        if (line.empty()) {
            continue;
        }

        const std::size_t colon = line.find(':');
        if (colon == std::string::npos ||
            line.find(':', colon + 1) != std::string::npos) {
            return report_error(
                FunctionName, SparseMemFormatError,
                "line " + std::to_string(line_number) +
                    ": expected address:data");
        }

        std::string address_text = line.substr(0, colon);
        std::string data_text = line.substr(colon + 1);
        if (data_text.compare(0, 2, "0x") == 0 ||
            data_text.compare(0, 2, "0X") == 0) {
            data_text.erase(0, 2);
        }
        if (data_text.empty() || data_text.size() > 17 ||
            !std::all_of(data_text.begin(), data_text.end(),
                         [](unsigned char character) {
                             return std::isxdigit(character) != 0;
                         })) {
            return report_error(
                FunctionName, SparseMemFormatError,
                "line " + std::to_string(line_number) +
                    ": invalid 65-bit data value");
        }

        try {
            std::size_t address_end = 0;
            const unsigned long long parsed_address =
                std::stoull(address_text, &address_end, 0);
            if (address_end != address_text.size() ||
                parsed_address > std::numeric_limits<uint32_t>::max() - 7ULL ||
                (parsed_address & 7ULL) != 0) {
                throw std::out_of_range("address must be aligned and 32-bit");
            }

            uint8_t tag = 0;
            if (data_text.size() == 17) {
                if (data_text[0] != '0' && data_text[0] != '1') {
                    throw std::out_of_range("tag bit must be zero or one");
                }
                tag = data_text[0] == '1';
                data_text.erase(0, 1);
            }
            const uint64_t data = std::stoull(data_text, nullptr, 16);
            entries.push_back({static_cast<uint32_t>(parsed_address),
                               data, tag});
        } catch (const std::exception &error) {
            return report_error(
                FunctionName, SparseMemFormatError,
                "line " + std::to_string(line_number) + ": " + error.what());
        }
    }

    if (input.bad()) {
        return report_error(FunctionName, SparseMemIoError,
                            "error while reading input file");
    }

    for (const Entry &entry : entries) {
        for (unsigned byte = 0; byte < 8; ++byte) {
            const uint32_t address = entry.address + byte;
            const uint8_t value =
                static_cast<uint8_t>(entry.data >> (byte * 8));
            if (value == 0) {
                sparse_mem_data.erase(address);
            } else {
                sparse_mem_data[address] = value;
            }
        }
        sparse_mem_tag[entry.address] = entry.tag;
    }
    return SparseMemOk;
}

/* Byte-addressed data read.  An uninitialized location returns zero. */
extern "C" uint8_t sparse_mem_read_data(uint32_t address)
{
    const SparseByteMap::const_iterator it = sparse_mem_data.find(address);
    return it == sparse_mem_data.end() ? 0 : it->second;
}

/* Byte-addressed tag read.  An uninitialized location returns zero. */
extern "C" uint8_t sparse_mem_read_tag(uint32_t address)
{
    const SparseByteMap::const_iterator it = sparse_mem_tag.find(address);
    return it == sparse_mem_tag.end() ? 0 : it->second;
}

extern "C" void sparse_mem_write_data(uint32_t address, uint8_t data)
{
    sparse_mem_data[address] = data;
}

extern "C" void sparse_mem_write_tag(uint32_t address, uint8_t tag)
{
    sparse_mem_tag[address] = tag;
}

/* Dump data and tag entries in ascending byte-address order. */
extern "C" int sparse_mem_dump(const char *filename)
{
    if (filename == nullptr) {
        return report_error("sparse_mem_dump", SparseMemOpenError,
                            "output filename is null");
    }

    std::ofstream output(filename);
    if (!output.is_open()) {
        return report_error("sparse_mem_dump", SparseMemOpenError,
                            std::string("cannot open '") + filename + "'");
    }

    const std::map<uint32_t, uint8_t> ordered_data(
        sparse_mem_data.begin(), sparse_mem_data.end());
    const std::map<uint32_t, uint8_t> ordered_tag(
        sparse_mem_tag.begin(), sparse_mem_tag.end());

    output << "SPARSE MEMORY DUMP\n\n";
    output << "DATA BYTE MAP\n";
    output << "Entries: " << ordered_data.size() << '\n';
    for (const auto &entry : ordered_data) {
        output << "addr=0x" << std::hex << entry.first
               << " data=0x" << std::setw(2) << std::setfill('0')
               << static_cast<unsigned int>(entry.second)
               << std::setfill(' ') << std::dec << '\n';
    }

    output << "\nTAG BYTE MAP\n";
    output << "Entries: " << ordered_tag.size() << '\n';
    for (const auto &entry : ordered_tag) {
        output << "addr=0x" << std::hex << entry.first
               << " tag=0x" << std::setw(2) << std::setfill('0')
               << static_cast<unsigned int>(entry.second)
               << std::setfill(' ') << std::dec << '\n';
    }

    if (!output.good()) {
        return report_error("sparse_mem_dump", SparseMemIoError,
                            "error while writing output file");
    }

    return SparseMemOk;
}
