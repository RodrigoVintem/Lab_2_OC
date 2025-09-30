#include "tlb.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "clock.h"
#include "constants.h"
#include "log.h"
#include "memory.h"
#include "page_table.h"

typedef struct {
  bool valid;
  bool dirty;
  uint64_t last_access;
  va_t virtual_page_number;
  pa_dram_t physical_page_number;
} tlb_entry_t;

tlb_entry_t tlb_l1[TLB_L1_SIZE];
tlb_entry_t tlb_l2[TLB_L2_SIZE];

uint64_t tlb_l1_hits = 0;
uint64_t tlb_l1_misses = 0;
uint64_t tlb_l1_invalidations = 0;

uint64_t tlb_l2_hits = 0;
uint64_t tlb_l2_misses = 0;
uint64_t tlb_l2_invalidations = 0;

uint64_t get_total_tlb_l1_hits() { return tlb_l1_hits; }
uint64_t get_total_tlb_l1_misses() { return tlb_l1_misses; }
uint64_t get_total_tlb_l1_invalidations() { return tlb_l1_invalidations; }

uint64_t get_total_tlb_l2_hits() { return tlb_l2_hits; }
uint64_t get_total_tlb_l2_misses() { return tlb_l2_misses; }
uint64_t get_total_tlb_l2_invalidations() { return tlb_l2_invalidations; }

//extracts the virtual page number (VPN) from a virtual address
static inline va_t va_to_vpn(va_t va) {
  return (va_t)((uint64_t)va >> PAGE_SIZE_BITS);
}

//extracts the page offset (low PAGE_SIZE_BITS bits)
static inline uint32_t va_offset(va_t va) {
  return (uint32_t)(va & PAGE_OFFSET_MASK);
}

//extracts the physical page number (PPN) from a physical address
static inline uint64_t pa_to_ppn(pa_dram_t pa) {
  return ((uint64_t)pa) >> PAGE_SIZE_BITS;
}

//rebuilds the full physical address from a PPN plus an offset.
static inline pa_dram_t compose_pa(uint64_t ppn, uint32_t off) {
  return (pa_dram_t)((ppn << PAGE_SIZE_BITS) | (uint64_t)off);
}

static uint64_t lru_tick = 0;
static uint64_t lru_tick2 = 0;

/* Forward declaration for internal helper used before its definition */
static void l2_insert(va_t vpn, uint64_t ppn, bool dirty);


void tlb_init() {
  memset(tlb_l1, 0, sizeof(tlb_l1));
  memset(tlb_l2, 0, sizeof(tlb_l2));
  tlb_l1_hits = 0;
  tlb_l1_misses = 0;
  tlb_l1_invalidations = 0;
  tlb_l2_hits = 0;
  tlb_l2_misses = 0;
  tlb_l2_invalidations = 0;
  lru_tick = 0;
  lru_tick2 = 0;
}

// Varre todas as entradas de L1: se válida e VPN igual, devolve o índice; senão -1 (miss)
static int l1_find(va_t vpn) {
  for (int i = 0; i < (int)TLB_L1_SIZE; ++i) {
    if (tlb_l1[i].valid && tlb_l1[i].virtual_page_number == vpn) {
      return i;
    }
  }
  return -1;
}

// Varre todas as entradas de L2: se válida e VPN igual, devolve o índice; senão -1 (miss)
static int l2_find(va_t vpn) {
  for(int i = 0; i < (int)TLB_L2_SIZE; ++i) {
    if (tlb_l2[i].valid && tlb_l2[i].virtual_page_number == vpn) {
      return i;
    }
  }
  return -1;
}




// L1 victim selection: escolher um slot inválido ou o menos usado recentemente
static int l1_choose_victim(void) {
  for (int i = 0; i < (int)TLB_L1_SIZE; ++i) {
    if (!tlb_l1[i].valid) return i;
  }
  int victim = 0;
  uint64_t best = tlb_l1[0].last_access;
  for (int i = 1; i < (int)TLB_L1_SIZE; ++i) {
    if (tlb_l1[i].last_access < best) {
      best = tlb_l1[i].last_access;
      victim = i;
    }
  }
  return victim;
}

//L2 victim selection: escolher um slot inválido ou o menos usado recentemente
static int l2_choose_victim(void) {
  for (int i = 0; i < (int)TLB_L2_SIZE; ++i) {
    if (!tlb_l2[i].valid) return i;
  }
  int victim = 0;
  uint64_t best = tlb_l2[0].last_access;
  for (int i = 1; i < (int)TLB_L2_SIZE; ++i) {
    if (tlb_l2[i].last_access < best) {
      best = tlb_l2[i].last_access;
      victim = i;
    }
  }
  return victim;
}

//Se dirty, faz write‑back usando um VA “sem offset” (offset=0 é irrelevante para write‑back de página).
//Depois invalida a entrada.

static void l1_evict_entry(int idx) {
  if (idx < 0) return;
  if (tlb_l1[idx].valid && tlb_l1[idx].dirty) {
    /* L1 write-back goes to L2, not directly to memory */
    va_t vpn = tlb_l1[idx].virtual_page_number;
    uint64_t ppn = (uint64_t)tlb_l1[idx].physical_page_number;
    
    /* Insert into L2 with dirty flag set */
    l2_insert(vpn, ppn, true);
  }
  tlb_l1[idx].valid = false;
  tlb_l1[idx].dirty = false;
  tlb_l1[idx].last_access = 0;
}

//Lógica do l1_evict_entry
static void l2_evict_entry(int idx) {
  if (idx < 0) return;
  if (tlb_l2[idx].valid && tlb_l2[idx].dirty) {
    /* write-back must use the PHYSICAL frame address (PPN -> PA) */
    uint64_t ppn = (uint64_t)tlb_l2[idx].physical_page_number;
    pa_dram_t pa_for_writeback = compose_pa(ppn, 0);
    write_back_tlb_entry(pa_for_writeback);
  }
  tlb_l2[idx].valid = false;
  tlb_l2[idx].dirty = false;
  tlb_l2[idx].last_access = 0;
}

// Inserir na L1. Atualiza no sítio se já existir na mesma página
// Caso contrário escolhe uma vítima (write-back) e escreve a nova entrada
static void l1_insert(va_t vpn, uint64_t ppn, bool dirty) {
  int idx = l1_find(vpn);
  if (idx >= 0) {
    //Já existe
    /* Update in place */
    tlb_l1[idx].physical_page_number = (pa_dram_t)ppn; /* store only frame number */
    tlb_l1[idx].dirty = (tlb_l1[idx].dirty || dirty);
    tlb_l1[idx].last_access = ++lru_tick;
    tlb_l1[idx].valid = true;
    return;
  }
  //Nova entrada
  int victim = l1_choose_victim();
  l1_evict_entry(victim);
  tlb_l1[victim].valid = true;
  tlb_l1[victim].dirty = dirty;
  tlb_l1[victim].last_access = ++lru_tick;
  tlb_l1[victim].virtual_page_number = vpn;
  tlb_l1[victim].physical_page_number = (pa_dram_t)ppn; /* store only frame number */
}

// Inserir na L2. Lógica da L1
static void l2_insert(va_t vpn, uint64_t ppn, bool dirty) {
  int idx = l2_find(vpn);
  if (idx >= 0) {
    tlb_l2[idx].physical_page_number = (pa_dram_t)ppn; 
    tlb_l2[idx].dirty = (tlb_l2[idx].dirty || dirty);
    tlb_l2[idx].last_access = ++lru_tick2;
    tlb_l2[idx].valid = true;
    return;
  }
  int victim = l2_choose_victim();
  l2_evict_entry(victim);
  tlb_l2[victim].valid = true;
  tlb_l2[victim].dirty = dirty;
  tlb_l2[victim].last_access = ++lru_tick2;
  tlb_l2[victim].virtual_page_number = vpn;
  tlb_l2[victim].physical_page_number = (pa_dram_t)ppn; 
}

/* Invalidate a given VPN in both levels (write-back if dirty) */
void tlb_invalidate(va_t virtual_page_number) {
  /* Account for TLB maintenance overhead (matches expected timing model):
     invalidate requires checking both levels once. */
  increment_time((time_ns_t)(TLB_L1_LATENCY_NS + TLB_L2_LATENCY_NS));
  /* L1 */
  for (int i = 0; i < (int)TLB_L1_SIZE; ++i) {
    if (tlb_l1[i].valid && tlb_l1[i].virtual_page_number == virtual_page_number) {
      if (tlb_l1[i].dirty) {
        // L1 write-back to L2
        va_t vpn = tlb_l1[i].virtual_page_number;
        uint64_t ppn = (uint64_t)tlb_l1[i].physical_page_number;
        l2_insert(vpn, ppn, true);
      }
      tlb_l1[i].valid = false;
      tlb_l1[i].dirty = false;
      tlb_l1[i].last_access = 0;
      ++tlb_l1_invalidations;
      break; /* only one match expected */
    }
  }

  /* L2 */
  for (int i = 0; i < (int)TLB_L2_SIZE; ++i) {
    if (tlb_l2[i].valid && tlb_l2[i].virtual_page_number == virtual_page_number) {
      if (tlb_l2[i].dirty) {
        /* write-back must use the PHYSICAL frame address (PPN -> PA) */
        uint64_t ppn = (uint64_t)tlb_l2[i].physical_page_number;
        pa_dram_t pa_for_writeback = compose_pa(ppn, 0);
        write_back_tlb_entry(pa_for_writeback);
      }
      tlb_l2[i].valid = false;
      tlb_l2[i].dirty = false;
      tlb_l2[i].last_access = 0;
      ++tlb_l2_invalidations;
      break;
    }
  }
}

pa_dram_t tlb_translate(va_t virtual_address, op_t op) {
  increment_time((time_ns_t)TLB_L1_LATENCY_NS);

  // Divide VA em VPN e offset
  const va_t vpn = va_to_vpn(virtual_address);
  const uint32_t off = va_offset(virtual_address);

  //Procura L1
  int idx1 = l1_find(vpn);
  if (idx1 >= 0) {
    //Dá hit
    ++tlb_l1_hits;
    tlb_l1[idx1].last_access = ++lru_tick; // Atualiza lru
    if (op == OP_WRITE) {
      tlb_l1[idx1].dirty = true;
    }
    // Guarda PPN (frame) na physical_page_number
    uint64_t ppn = (uint64_t)tlb_l1[idx1].physical_page_number;
    return compose_pa(ppn, off);
  }

  // L1 MISS: Ir à page table (it will model DRAM/DISK latencies and print logs)
  ++tlb_l1_misses;
  increment_time((time_ns_t)TLB_L2_LATENCY_NS);

  //Procurar na L2
  int idx2 = l2_find(vpn);
  if (idx2 >= 0) {
    //há Hit
    ++tlb_l2_hits;
    tlb_l2[idx2].last_access = ++lru_tick2;
    if (op == OP_WRITE) {
      tlb_l2[idx2].dirty = true;
    }
    uint64_t ppn = (uint64_t)tlb_l2[idx2].physical_page_number;
    //Coloca também no L1
    l1_insert(vpn, ppn, (op == OP_WRITE));
    return compose_pa(ppn, off);
  }

  //L2 miss
  ++tlb_l2_misses;
  pa_dram_t pa = page_table_translate(virtual_address, op);
  uint64_t ppn = pa_to_ppn(pa);

  //Insere na L1 e L2 (write-back on victim if dirty)
  l1_insert(vpn, ppn, (op == OP_WRITE));
  l2_insert(vpn, ppn, (op == OP_WRITE));

  return pa; /* already includes ppn+offset; returning pa is fine */
}
