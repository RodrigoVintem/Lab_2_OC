#pragma once

#include <stdint.h>

#include "memory.h"

void tlb_init();

// TLB translation function.
// Can also update the content of the TLB.
pa_dram_t tlb_translate(va_t virtual_address, op_t op);

// Invalidate entries on the TLB.
// This can happen if a page is swapped out of memory and into the disk.
void tlb_invalidate(va_t virtual_page_number);

uint64_t get_total_tlb_l1_hits();
uint64_t get_total_tlb_l1_misses();
uint64_t get_total_tlb_l1_invalidations();

uint64_t get_total_tlb_l2_hits();
uint64_t get_total_tlb_l2_misses();
uint64_t get_total_tlb_l2_invalidations();
