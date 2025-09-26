#include <stdio.h>
#include <stdlib.h>

#include "clock.h"
#include "constants.h"
#include "log.h"
#include "memory.h"
#include "page_table.h"
#include "tlb.h"

int main(int argc, char* argv[]) {
  log_dbg("=========== System Properties ===========");
  log_dbg("Virtual address:       %d bits", VIRTUAL_ADDRESS_BITS);
  log_dbg("Page index:            %d bits", PAGE_SIZE_BITS);
  log_dbg("DRAM address:          %d bits", DRAM_ADDRESS_BITS);
  log_dbg("Disk address:          %d bits", DISK_ADDRESS_BITS);
  log_dbg("Virtual address space: %" PRIu64 " B", VIRTUAL_SIZE_BYTES);
  log_dbg("DRAM address space:    %" PRIu64 " B", DRAM_SIZE_BYTES);
  log_dbg("Disk address space:    %" PRIu64 " B", DISK_SIZE_BYTES);
  log_dbg("Page size:             %" PRIu64 " B", PAGE_SIZE_BYTES);
  log_dbg("Total pages:           %" PRIu64, TOTAL_PAGES);
  log_dbg("=========================================");

  if (argc < 2) {
    panic("Usage: %s <instructions_file>", argv[0]);
  }

  srand(0xcafebabe);
  reset_time();
  page_table_init();
  tlb_init();

  FILE* file = fopen(argv[1], "r");
  if (!file) {
    panic("Failed to open instructions file %s", argv[1]);
  }

  uint64_t total_instructions = 0;

  char line[256];
  while (fgets(line, sizeof(line), file)) {
    char instruction;
    uint64_t address;
    if (sscanf(line, "%c %" PRIx64, &instruction, &address) != 2) {
      panic("Invalid instruction format: %s", line);
    }

    log_dbg("* %c %" PRIx64, instruction, address);

    switch (instruction) {
      case 'R':
        read(address);
        break;
      case 'W':
        write(address);
        break;
      default:
        panic("Unknown instruction: %c", instruction);
    }

    total_instructions++;
  }

  fclose(file);

  time_ns_t elapsed_time = get_time();
  uint64_t page_faults = get_total_page_faults();
  uint64_t page_evictions = get_total_page_evictions();

  uint64_t l1_hits = get_total_tlb_l1_hits();
  uint64_t l1_misses = get_total_tlb_l1_misses();
  uint64_t l1_invalidations = get_total_tlb_l1_invalidations();
  uint64_t l2_hits = get_total_tlb_l2_hits();
  uint64_t l2_misses = get_total_tlb_l2_misses();
  uint64_t l2_invalidations = get_total_tlb_l2_invalidations();

  float l1_hit_rate =
      (l1_hits + l1_misses) > 0 ? 100.0 * l1_hits / (l1_hits + l1_misses) : 0.0;

  float l2_hit_rate =
      (l2_hits + l2_misses) > 0 ? 100.0 * l2_hits / (l2_hits + l2_misses) : 0.0;

  log("Elapsed: %" PRIu64 " ns", elapsed_time);
  log("Total instructions executed: %" PRIu64, total_instructions);
  log("Total page faults: %" PRIu64, page_faults);
  log("Total page evictions: %" PRIu64, page_evictions);
  log("Total TLB L1 hits: %" PRIu64 " (%.2f%%)", l1_hits, l1_hit_rate);
  log("Total TLB L2 hits: %" PRIu64 " (%.2f%%)", l2_hits, l2_hit_rate);
  log("Total TLB L1 invalidations: %" PRIu64, l1_invalidations);
  log("Total TLB L2 invalidations: %" PRIu64, l2_invalidations);

  return 0;
}