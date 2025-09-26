#pragma once

#include <stdint.h>

// Virtual address.
// Pertains to the virtual address space of the process.
typedef uint64_t va_t;

// Physical address in main memory (DRAM).
// Pertains to the physical address space of the system's main memory (DRAM).
typedef uint64_t pa_dram_t;

// Physical address in disk storage.
// Pertains to the physical address space of the disk storage.
typedef uint64_t pa_disk_t;

typedef enum { OP_READ, OP_WRITE } op_t;

void read(va_t address);
void write(va_t address);
void dram_access(pa_dram_t address, op_t op);
void disk_access(pa_disk_t address, op_t op);