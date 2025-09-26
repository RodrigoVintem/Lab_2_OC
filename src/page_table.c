#include "page_table.h"

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "clock.h"
#include "constants.h"
#include "log.h"
#include "tlb.h"

#define PAGE_TABLE_DRAM_ADDRESS (0)

pa_dram_t RANDOM_PAGE_ADDRESS_BASE = 0xcafebabe;
pa_dram_t RANDOM_PAGE_ADDRESS_IT = 0;

uint64_t page_faults = 0;
uint64_t page_evictions = 0;

typedef struct {
  // This only stored the page index, not the full address.
  // The full address is constructed by shifting this value left by
  // PAGE_SIZE_BITS. This is done to save space in the page table (not on the
  // simulator, not on actual hardware).
  pa_dram_t dram_page_number;

  // Is this entry in memory, or in disk?
  bool valid;

  // Has this entry been modified since it was loaded into memory?
  bool dirty;
} page_table_entry_t;

page_table_entry_t page_table[TOTAL_PAGES];

typedef struct {
  bool is_swapped;
  pa_disk_t disk_page_number;
} pte_metadata_t;

pte_metadata_t pte_metadata[TOTAL_PAGES];

bool allocated_dram_pages[DRAM_PAGE_CAPACITY];

page_table_entry_t* get_free_page_table_entry() {
  for (va_t virtual_page_number = 0; virtual_page_number < TOTAL_PAGES;
       virtual_page_number++) {
    if (!page_table[virtual_page_number].valid) {
      return &page_table[virtual_page_number];
    }
  }
  return NULL;
}

bool allocate_dram_page(pa_dram_t* dram_page_address) {
  // Very inefficient (but simple) way of finding a free DRAM page.
  for (pa_dram_t dram_page_number = 0; dram_page_number < DRAM_PAGE_CAPACITY;
       dram_page_number++) {
    if (dram_page_number == PAGE_TABLE_DRAM_ADDRESS) {
      continue;
    }

    if (!allocated_dram_pages[dram_page_number]) {
      allocated_dram_pages[dram_page_number] = true;
      *dram_page_address = dram_page_number << PAGE_SIZE_BITS;
      return true;
    }
  }
  return false;
}

pa_disk_t allocate_disk_page() {
  // Let's assume there is always a free disk page available, and ignore all the
  // complexity behind the actual process of finding an available disk page (for
  // simulation purposes). We simulate this by generating a random disk page
  // address.
  pa_disk_t disk_page_address = RANDOM_PAGE_ADDRESS_BASE;
  disk_page_address <<= 32;
  disk_page_address |= RANDOM_PAGE_ADDRESS_IT;
  disk_page_address &= DISK_ADDRESS_MASK;

  RANDOM_PAGE_ADDRESS_IT += PAGE_SIZE_BYTES;

  return disk_page_address;
}

pa_dram_t randomly_evict_page_from_dram() {
  page_evictions++;

  va_t evicted_virtual_page_number = PAGE_TABLE_DRAM_ADDRESS;
  while (!page_table[evicted_virtual_page_number].valid) {
    evicted_virtual_page_number++;
  }

  if (page_table[evicted_virtual_page_number].dirty) {
    log_dbg("***** Evicting dirty page %" PRIx64 " to disk *****",
            evicted_virtual_page_number);

    pa_disk_t disk_page_address = allocate_disk_page();
    pte_metadata[evicted_virtual_page_number].is_swapped = true;
    pte_metadata[evicted_virtual_page_number].disk_page_number =
        disk_page_address >> PAGE_SIZE_BITS;

    disk_access(disk_page_address, OP_WRITE);

    tlb_invalidate(evicted_virtual_page_number);
  } else {
    log_dbg("***** Evicting page %" PRIx64 " *****",
            evicted_virtual_page_number);
  }

  page_table[evicted_virtual_page_number].valid = false;
  page_table[evicted_virtual_page_number].dirty = false;

  allocated_dram_pages[evicted_virtual_page_number] = false;

  dram_access(PAGE_TABLE_DRAM_ADDRESS, OP_READ);

  return evicted_virtual_page_number << PAGE_SIZE_BITS;
}

void page_fault_handler(va_t virtual_page_number) {
  log_dbg("***** Page fault! *****");
  page_faults++;

  pa_dram_t page_dram_address;
  if (!allocate_dram_page(&page_dram_address)) {
    page_dram_address = randomly_evict_page_from_dram();
  }

  page_table_entry_t* entry = &page_table[virtual_page_number];
  entry->dram_page_number = page_dram_address >> PAGE_SIZE_BITS;
  entry->valid = true;
  entry->dirty = false;
  dram_access(PAGE_TABLE_DRAM_ADDRESS, OP_WRITE);

  if (pte_metadata[virtual_page_number].is_swapped) {
    log_dbg("***** Page %" PRIx64 " is swapped, loading from disk *****",
            virtual_page_number);
    pa_disk_t disk_address = pte_metadata[virtual_page_number].disk_page_number
                             << PAGE_SIZE_BITS;
    disk_access(disk_address, OP_READ);
    dram_access(page_dram_address, OP_WRITE);
    pte_metadata[virtual_page_number].is_swapped = false;
  }
}

void page_table_init() {
  memset(page_table, 0, sizeof(page_table));
  memset(pte_metadata, 0, sizeof(pte_metadata));
  memset(allocated_dram_pages, 0, sizeof(allocated_dram_pages));
  page_faults = 0;
  page_evictions = 0;
}

pa_dram_t page_table_translate(va_t virtual_address, op_t op) {
  virtual_address &= VIRTUAL_ADDRESS_MASK;

  va_t virtual_page_number =
      (virtual_address >> PAGE_SIZE_BITS) & PAGE_INDEX_MASK;
  va_t virtual_page_offset = virtual_address & PAGE_OFFSET_MASK;
  assert(virtual_page_number < TOTAL_PAGES && "Page index out of bounds");
  assert(virtual_page_offset < PAGE_SIZE_BYTES && "Page offset out of bounds");

  page_table_entry_t* entry = &page_table[virtual_page_number];
  if (!entry->valid) {
    page_fault_handler(virtual_page_number);
  } else {
    dram_access(PAGE_TABLE_DRAM_ADDRESS, OP_READ);
  }

  if (op == OP_WRITE) {
    entry->dirty = true;
  }

  pa_dram_t translated_address =
      (entry->dram_page_number << PAGE_SIZE_BITS) | virtual_page_offset;
  log_dbg("PTE found (VA=%" PRIx64 " VPN=%" PRIx64 " PA=%" PRIx64 ")",
          virtual_address, virtual_page_number, translated_address);

  return translated_address;
}

void write_back_tlb_entry(va_t virtual_address) {
  dram_access(virtual_address, OP_WRITE);
}

uint64_t get_total_page_faults() { return page_faults; }
uint64_t get_total_page_evictions() { return page_evictions; }