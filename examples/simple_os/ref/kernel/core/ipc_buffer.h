/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/ipc_buffer.h -- Per-thread IPC buffer (4KB)
 *
 * Mirrors: spl/kernel/core/ipc_buffer.spl
 *
 * Layout (offsets in u32 words):
 *   0       : tag
 *   1       : length
 *   2       : label
 *   3       : caps_length
 *   4..123  : msg_regs[0..119]
 *   124..131: caps[0..7]
 */

#ifndef SIMPLE_OS_IPC_BUFFER_H
#define SIMPLE_OS_IPC_BUFFER_H

#include "common/types.h"
#include "common/config.h"

/* ---- Constants --------------------------------------------------------- */

/* IPC_BUFFER_SIZE, IPC_MAX_MRS, IPC_MAX_CAPS defined in config.h */

/* ---- IPC Buffer -------------------------------------------------------- */

typedef struct {
    uint32_t tag;                       /* Message descriptor / type tag */
    uint32_t length;                    /* Number of valid message registers */
    uint32_t label;                     /* Opcode / method identifier */
    uint32_t caps_length;               /* Number of cap slots in transfer */
    uint32_t msg_regs[IPC_MAX_MRS];     /* Message register payload */
    uint32_t cap_slots[IPC_MAX_CAPS];   /* Capability slot indices */
    uint32_t owner_thread_id;           /* Thread that owns this buffer */
    uint32_t virt_addr;                 /* Virtual address where mapped */
} ipc_buffer_t;

/* ---- API --------------------------------------------------------------- */

/* Initialize an IPC buffer to zero. */
void ipc_buffer_init(ipc_buffer_t *buf);

/* Initialize for a specific thread and virtual address. */
void ipc_buffer_init_for(ipc_buffer_t *buf, uint32_t thread_id,
                         uint32_t vaddr);

/* Message register access */
void     ipc_buffer_set_mr(ipc_buffer_t *buf, uint32_t index, uint32_t value);
uint32_t ipc_buffer_get_mr(const ipc_buffer_t *buf, uint32_t index);

/* Capability slot access */
void     ipc_buffer_set_cap(ipc_buffer_t *buf, uint32_t index,
                            uint32_t cap_slot);
uint32_t ipc_buffer_get_cap(const ipc_buffer_t *buf, uint32_t index);

/* Tag / label / length */
void     ipc_buffer_set_tag(ipc_buffer_t *buf, uint32_t tag);
uint32_t ipc_buffer_get_tag(const ipc_buffer_t *buf);
void     ipc_buffer_set_label(ipc_buffer_t *buf, uint32_t label);
uint32_t ipc_buffer_get_label(const ipc_buffer_t *buf);
void     ipc_buffer_set_length(ipc_buffer_t *buf, uint32_t len);
uint32_t ipc_buffer_get_length(const ipc_buffer_t *buf);
void     ipc_buffer_set_caps_length(ipc_buffer_t *buf, uint32_t len);
uint32_t ipc_buffer_get_caps_length(const ipc_buffer_t *buf);

/* Transfer full message from src to dst (zero-copy rendezvous). */
void ipc_buffer_transfer(const ipc_buffer_t *src, ipc_buffer_t *dst);

/* Copy message registers (up to max_regs). */
void ipc_buffer_copy_mrs(const ipc_buffer_t *src, ipc_buffer_t *dst,
                         uint32_t max_regs);

/* Clear all fields to zero. */
void ipc_buffer_clear(ipc_buffer_t *buf);

/* Message info word helpers (seL4 convention: label<<12 | length). */
uint32_t ipc_msg_info_new(uint32_t label, uint32_t length);
uint32_t ipc_msg_info_get_label(uint32_t msg_info);
uint32_t ipc_msg_info_get_length(uint32_t msg_info);

/* Load / build message info from buffer. */
void     ipc_buffer_load_msg_info(ipc_buffer_t *buf, uint32_t msg_info);
uint32_t ipc_buffer_build_msg_info(const ipc_buffer_t *buf);

#endif /* SIMPLE_OS_IPC_BUFFER_H */
