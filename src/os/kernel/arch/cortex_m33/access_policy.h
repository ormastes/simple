#ifndef SIMPLEOS_CORTEX_M_ACCESS_POLICY_H
#define SIMPLEOS_CORTEX_M_ACCESS_POLICY_H

#include <stdint.h>

/* Pure-Simple policy ABI.  C owns address acquisition and volatile access;
 * these two functions own alignment and readable/writable classification. */
uint32_t cortex_m_policy_read_receipt(uint32_t addr,
                                      uint32_t flash_base,
                                      uint32_t flash_size,
                                      uint32_t ram_base,
                                      uint32_t ram_size);
uint32_t cortex_m_policy_write_receipt(uint32_t addr,
                                       uint32_t ram_base,
                                       uint32_t ram_size);

#endif
