#pragma once

#include "memory.h"

void page_table_init();
pa_dram_t page_table_translate(va_t virtual_address, op_t op);
void write_back_tlb_entry(va_t virtual_address);

uint64_t get_total_page_faults();
uint64_t get_total_page_evictions();
