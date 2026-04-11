// ============================================================================
// sparse_rom16_x4.cpp
// Read-only sparse memory
//  - 16-bit storage
//  - 64-bit reads = 4 x 16-bit words
//  - Initialized from text file
// ============================================================================

#include <cstdint>
#include <cstdio>
#include <unordered_map>

// -----------------------------------------------------------------------------
// Sparse storage: halfword_address -> 16-bit value
// halfword_address = byte_address >> 1
// -----------------------------------------------------------------------------
static std::unordered_map<uint64_t, uint16_t> mem;

// -----------------------------------------------------------------------------
// Parse lines like:
//   mem[X,0x80000080] -> 0x01DB
// -----------------------------------------------------------------------------
static bool parse_line(const char *line, uint64_t &addr, uint16_t &data)
{
    unsigned long long a;
    unsigned int d;

    if (std::sscanf(line, "mem[X,0x%llx] -> 0x%x", &a, &d) != 2)
        return false;

    addr = static_cast<uint64_t>(a);
    data = static_cast<uint16_t>(d & 0xFFFF);
    return true;
}

// -----------------------------------------------------------------------------
// Initialize ROM from file
// -----------------------------------------------------------------------------
extern "C"
int instr_mem_init(const char *filename)
{
    FILE *fp = std::fopen(filename, "r");
    if (!fp) {
        std::perror("instr_mem_int");
        return -1;
    }

    mem.clear();

    char line[256];
    uint64_t addr;
    uint16_t data;

    while (std::fgets(line, sizeof(line), fp)) {
        if (!parse_line(line, addr, data))
            continue;

        // 16-bit alignment check
        if (addr & 0x1) {
            std::fprintf(stderr,
                "instr_mem_int: unaligned address 0x%lx\n", addr);
            continue;
        }

        mem[addr >> 1] = data;
    }

    std::fclose(fp);
    return 0;
}

// -----------------------------------------------------------------------------
// Read 64-bit value = 4 x 16-bit words
// Layout (little-endian):
//   addr+0  -> bits [15:0]
//   addr+2  -> bits [31:16]
//   addr+4  -> bits [47:32]
//   addr+6  -> bits [63:48]
// -----------------------------------------------------------------------------
extern "C"
uint64_t instr_mem_read64(uint64_t addr)
{
    // Must be 8-byte aligned
    if (addr & 0x7) {
        std::fprintf(stderr,
            "instr_mem_read64: unaligned address 0x%lx\n", addr);
        return 0;
    }

    uint64_t result = 0;
    uint64_t base = addr >> 1; // halfword address

    for (int i = 0; i < 4; i++) {
        auto it = mem.find(base + i);
        uint16_t val = (it != mem.end()) ? it->second : 0;
        result |= (uint64_t)val << (i * 16);
    }

    return result;
}

// -----------------------------------------------------------------------------
// Debug dump
// -----------------------------------------------------------------------------
extern "C"
void mem_dump(void)
{
    std::printf("---- Sparse ROM Dump ----\n");
    for (const auto &kv : mem) {
        std::printf("0x%08lx : 0x%04x\n",
            kv.first << 1, kv.second);
    }
    std::printf("-------------------------\n");
}

