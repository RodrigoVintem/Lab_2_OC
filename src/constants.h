#pragma once

#include <stdint.h>

// Number of bits used for virtual addresses.
// The virtual address space is the range of addresses that a process can use.
// The total amount of available virtual memory is determined by the number of
// bits of the virtual address. For example, a 32-bit virtual address space can
// address 2^32 bytes of memory, or 4 GiB.
#define VIRTUAL_ADDRESS_BITS 32

// This is the size of a page, expressed as the exponent of a power of two of
// the total page size in bytes. A page is a fixed-length contiguous block of
// *virtual* memory, which is the address space that a process can use. Common
// page sizes are 4096 bytes (4 KiB), 8192 bytes (8 KiB), etc. The page size is
// used to divide the virtual address space into smaller chunks, which can be
// mapped to physical memory (DRAM) or disk storage. A page size of 4096 bytes
// is 2^12 bytes, so PAGE_SIZE_BITS=12. PAGE_SIZE_BITS should always be less
// than VIRTUAL_ADDRESS_BITS, DRAM_ADDRESS_BITS, and DISK_ADDRESS_BITS.
#define PAGE_SIZE_BITS 12

// Number of bits used for physical addresses in the system's main memory
// (DRAM). The physical address space is the range of addresses that the
// hardware can access directly. This is typically smaller than the virtual
// address space. For example, a 15-bit physical address space can address 2^15
// bytes of memory, or 32 KiB. The physical address space is often determined by
// the amount of DRAM in the system and the architecture of the hardware.
#define DRAM_ADDRESS_BITS 28

// Number of bits used for physical addresses in the disk storage.
// The disk storage address space is the range of addresses that the system can
// access on disk. This is typically larger than the physical address space of
// the main memory (DRAM). For example, a 20-bit disk storage address space can
// address 2^20 bytes of memory, or 1 MiB. The disk storage address space is
// often determined by the size of the disk and the architecture of the
// hardware.
#define DISK_ADDRESS_BITS 48

#define TLB_L1_SIZE 32
#define TLB_L2_SIZE 512

#define TLB_L1_LATENCY_NS 1
#define TLB_L2_LATENCY_NS 2
#define DRAM_LATENCY_NS 100
#define DISK_LATENCY_NS 1000000

// ========================================================================
// Constants defined from the constants above.
// ========================================================================

#define PAGE_SIZE_BYTES (uint64_t)(1llu << PAGE_SIZE_BITS)
#define VIRTUAL_SIZE_BYTES (uint64_t)(1llu << VIRTUAL_ADDRESS_BITS)
#define DRAM_SIZE_BYTES (uint64_t)(1llu << DRAM_ADDRESS_BITS)
#define DISK_SIZE_BYTES (uint64_t)(1llu << DISK_ADDRESS_BITS)

#define DRAM_PAGE_CAPACITY \
  (uint64_t)(1llu << (DRAM_ADDRESS_BITS - PAGE_SIZE_BITS))
#define DISK_PAGE_CAPACITY \
  (uint64_t)(1llu << (DISK_ADDRESS_BITS - PAGE_SIZE_BITS))
#define TOTAL_PAGES (uint64_t)(1llu << (VIRTUAL_ADDRESS_BITS - PAGE_SIZE_BITS))

#define VIRTUAL_ADDRESS_MASK (VIRTUAL_SIZE_BYTES - 1)
#define DRAM_ADDRESS_MASK (DRAM_SIZE_BYTES - 1)
#define DISK_ADDRESS_MASK (DISK_SIZE_BYTES - 1)
#define PAGE_INDEX_MASK (TOTAL_PAGES - 1)
#define PAGE_OFFSET_MASK (PAGE_SIZE_BYTES - 1)
