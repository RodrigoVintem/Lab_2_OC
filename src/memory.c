#include "memory.h"

#include "clock.h"
#include "constants.h"
#include "log.h"
#include "page_table.h"
#include "tlb.h"

void log_dram_access(pa_dram_t address, op_t op) {
  address &= DRAM_ADDRESS_MASK;
  switch (op) {
    case OP_READ:
      log_clk("R DRAM[%" PRIx64 "]", address);
      break;
    case OP_WRITE:
      log_clk("W DRAM[%" PRIx64 "]", address);
      break;
  }
}

void log_disk_access(pa_disk_t address, op_t op) {
  address &= DISK_ADDRESS_MASK;
  switch (op) {
    case OP_READ:
      log_clk("R Disk[%" PRIx64 "]", address);
      break;
    case OP_WRITE:
      log_clk("W Disk[%" PRIx64 "]", address);
      break;
  }
}

void read(va_t address) {
  address &= VIRTUAL_ADDRESS_MASK;
  pa_dram_t physical_address = tlb_translate(address, OP_READ);
  log_dram_access(physical_address, OP_READ);
}

void write(va_t address) {
  address &= VIRTUAL_ADDRESS_MASK;
  pa_dram_t physical_address = tlb_translate(address, OP_WRITE);
  log_dram_access(physical_address, OP_WRITE);
}

void dram_access(pa_dram_t address, op_t op) {
  log_dram_access(address, op);
  increment_time(DRAM_LATENCY_NS);
}

void disk_access(pa_disk_t address, op_t op) {
  log_disk_access(address, op);
  increment_time(DISK_LATENCY_NS);
}
