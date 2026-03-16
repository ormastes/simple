/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/ipc_buffer.c -- Per-thread IPC buffer implementation
 *
 * Mirrors: spl/kernel/core/ipc_buffer.spl
 */

#include "kernel/core/ipc_buffer.h"

/* ------------------------------------------------------------------------ */

void ipc_buffer_init(ipc_buffer_t *buf)
{
    buf->tag             = 0;
    buf->length          = 0;
    buf->label           = 0;
    buf->caps_length     = 0;
    buf->owner_thread_id = 0;
    buf->virt_addr       = 0;

    for (uint32_t i = 0; i < IPC_MAX_MRS; i++) {
        buf->msg_regs[i] = 0;
    }
    for (uint32_t i = 0; i < IPC_MAX_CAPS; i++) {
        buf->cap_slots[i] = 0;
    }
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_init_for(ipc_buffer_t *buf, uint32_t thread_id,
                         uint32_t vaddr)
{
    ipc_buffer_init(buf);
    buf->owner_thread_id = thread_id;
    buf->virt_addr       = vaddr;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_set_mr(ipc_buffer_t *buf, uint32_t index, uint32_t value)
{
    if (index >= IPC_MAX_MRS) {
        return;
    }
    buf->msg_regs[index] = value;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_get_mr(const ipc_buffer_t *buf, uint32_t index)
{
    if (index >= IPC_MAX_MRS) {
        return 0;
    }
    return buf->msg_regs[index];
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_set_cap(ipc_buffer_t *buf, uint32_t index,
                        uint32_t cap_slot)
{
    if (index >= IPC_MAX_CAPS) {
        return;
    }
    buf->cap_slots[index] = cap_slot;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_get_cap(const ipc_buffer_t *buf, uint32_t index)
{
    if (index >= IPC_MAX_CAPS) {
        return 0;
    }
    return buf->cap_slots[index];
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_set_tag(ipc_buffer_t *buf, uint32_t tag)
{
    buf->tag = tag;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_get_tag(const ipc_buffer_t *buf)
{
    return buf->tag;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_set_label(ipc_buffer_t *buf, uint32_t label)
{
    buf->label = label;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_get_label(const ipc_buffer_t *buf)
{
    return buf->label;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_set_length(ipc_buffer_t *buf, uint32_t len)
{
    buf->length = (len > IPC_MAX_MRS) ? IPC_MAX_MRS : len;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_get_length(const ipc_buffer_t *buf)
{
    return buf->length;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_set_caps_length(ipc_buffer_t *buf, uint32_t len)
{
    buf->caps_length = (len > IPC_MAX_CAPS) ? IPC_MAX_CAPS : len;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_get_caps_length(const ipc_buffer_t *buf)
{
    return buf->caps_length;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_transfer(const ipc_buffer_t *src, ipc_buffer_t *dst)
{
    dst->tag         = src->tag;
    dst->label       = src->label;
    dst->length      = src->length;
    dst->caps_length = src->caps_length;

    /* Copy message registers */
    for (uint32_t i = 0; i < src->length && i < IPC_MAX_MRS; i++) {
        dst->msg_regs[i] = src->msg_regs[i];
    }

    /* Copy capability transfer slots */
    for (uint32_t i = 0; i < src->caps_length && i < IPC_MAX_CAPS; i++) {
        dst->cap_slots[i] = src->cap_slots[i];
    }
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_copy_mrs(const ipc_buffer_t *src, ipc_buffer_t *dst,
                         uint32_t max_regs)
{
    uint32_t count = src->length;
    if (count > max_regs) {
        count = max_regs;
    }
    for (uint32_t i = 0; i < count; i++) {
        dst->msg_regs[i] = src->msg_regs[i];
    }
    dst->length = count;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_clear(ipc_buffer_t *buf)
{
    buf->tag         = 0;
    buf->length      = 0;
    buf->label       = 0;
    buf->caps_length = 0;

    for (uint32_t i = 0; i < IPC_MAX_MRS; i++) {
        buf->msg_regs[i] = 0;
    }
    for (uint32_t i = 0; i < IPC_MAX_CAPS; i++) {
        buf->cap_slots[i] = 0;
    }
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_msg_info_new(uint32_t label, uint32_t length)
{
    uint32_t capped = length;
    if (capped > IPC_MAX_MRS) {
        capped = IPC_MAX_MRS;
    }
    return ((label & 0xFFFFF) << 12) | (capped & 0xFFF);
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_msg_info_get_label(uint32_t msg_info)
{
    return (msg_info >> 12) & 0xFFFFF;
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_msg_info_get_length(uint32_t msg_info)
{
    return msg_info & 0xFFF;
}

/* ------------------------------------------------------------------------ */

void ipc_buffer_load_msg_info(ipc_buffer_t *buf, uint32_t msg_info)
{
    buf->label  = ipc_msg_info_get_label(msg_info);
    buf->length = ipc_msg_info_get_length(msg_info);
}

/* ------------------------------------------------------------------------ */

uint32_t ipc_buffer_build_msg_info(const ipc_buffer_t *buf)
{
    return ipc_msg_info_new(buf->label, buf->length);
}
