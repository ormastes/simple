/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/tcb.c -- Thread Control Block implementation
 *
 * Mirrors: spl/kernel/core/tcb.spl
 */

#include "kernel/core/tcb.h"

/* ---- Internal helpers -------------------------------------------------- */

static void memzero_name(char *buf, uint32_t len)
{
    for (uint32_t i = 0; i < len; i++) {
        buf[i] = '\0';
    }
}

/* ---- API --------------------------------------------------------------- */

void tcb_init(tcb_t *tcb, uint32_t id, uint32_t priority)
{
    uint32_t prio = priority;
    if (prio > MAX_PRIORITY) {
        prio = MAX_PRIORITY;
    }

    tcb->id       = id;
    memzero_name(tcb->name, THREAD_NAME_MAX);
    tcb->state    = THREAD_STATE_INACTIVE;
    tcb->priority = prio;
    tcb->time_slice = 0;

    tcb->saved_eip    = 0;
    tcb->saved_esp    = 0;
    tcb->saved_eflags = 0;
    tcb->saved_eax    = 0;
    tcb->saved_ebx    = 0;
    tcb->saved_ecx    = 0;
    tcb->saved_edx    = 0;
    tcb->saved_esi    = 0;
    tcb->saved_edi    = 0;
    tcb->saved_cs     = 0;
    tcb->saved_ds     = 0;
    tcb->saved_ss     = 0;

    tcb->page_dir_phys     = 0;
    tcb->cspace_root       = 0;
    tcb->ipc_buffer_addr   = 0;
    tcb->fault_endpoint    = 0;
    tcb->bound_notification = 0;
    tcb->ipc_endpoint      = 0;
    tcb->ipc_badge         = 0;
    tcb->sched_context     = 0;

    tcb->queue_next = TCB_NONE;
    tcb->queue_prev = TCB_NONE;
}

/* ------------------------------------------------------------------------ */

void tcb_configure(tcb_t *tcb, uint32_t eip, uint32_t esp,
                   uint32_t page_dir, uint32_t cspace_root,
                   uint32_t ipc_buffer_addr)
{
    tcb->saved_eip       = eip;
    tcb->saved_esp       = esp;
    tcb->page_dir_phys   = page_dir;
    tcb->cspace_root     = cspace_root;
    tcb->ipc_buffer_addr = ipc_buffer_addr;
}

/* ------------------------------------------------------------------------ */

void tcb_set_state(tcb_t *tcb, thread_state_t state)
{
    tcb->state = state;
}

/* ------------------------------------------------------------------------ */

void tcb_set_priority(tcb_t *tcb, uint32_t priority)
{
    uint32_t prio = priority;
    if (prio > MAX_PRIORITY) {
        prio = MAX_PRIORITY;
    }
    tcb->priority = prio;
}

/* ------------------------------------------------------------------------ */

void tcb_suspend(tcb_t *tcb)
{
    tcb->state = THREAD_STATE_SUSPENDED;
}

/* ------------------------------------------------------------------------ */

void tcb_resume(tcb_t *tcb)
{
    if (tcb->state == THREAD_STATE_SUSPENDED ||
        tcb->state == THREAD_STATE_INACTIVE) {
        tcb->state = THREAD_STATE_READY;
    }
}

/* ------------------------------------------------------------------------ */

void tcb_save_context(tcb_t *tcb, uint32_t eip, uint32_t esp,
                      uint32_t eflags, uint32_t eax, uint32_t ebx,
                      uint32_t ecx, uint32_t edx, uint32_t esi,
                      uint32_t edi)
{
    tcb->saved_eip    = eip;
    tcb->saved_esp    = esp;
    tcb->saved_eflags = eflags;
    tcb->saved_eax    = eax;
    tcb->saved_ebx    = ebx;
    tcb->saved_ecx    = ecx;
    tcb->saved_edx    = edx;
    tcb->saved_esi    = esi;
    tcb->saved_edi    = edi;
}

/* ------------------------------------------------------------------------ */

void tcb_restore_context(const tcb_t *tcb, uint32_t *eip, uint32_t *esp,
                         uint32_t *eflags, uint32_t *eax, uint32_t *ebx,
                         uint32_t *ecx, uint32_t *edx, uint32_t *esi,
                         uint32_t *edi)
{
    *eip    = tcb->saved_eip;
    *esp    = tcb->saved_esp;
    *eflags = tcb->saved_eflags;
    *eax    = tcb->saved_eax;
    *ebx    = tcb->saved_ebx;
    *ecx    = tcb->saved_ecx;
    *edx    = tcb->saved_edx;
    *esi    = tcb->saved_esi;
    *edi    = tcb->saved_edi;
}

/* ------------------------------------------------------------------------ */

void tcb_set_register(tcb_t *tcb, uint32_t reg_index, uint32_t value)
{
    switch (reg_index) {
    case 0:  tcb->saved_eax    = value; break;
    case 1:  tcb->saved_ebx    = value; break;
    case 2:  tcb->saved_ecx    = value; break;
    case 3:  tcb->saved_edx    = value; break;
    case 4:  tcb->saved_esi    = value; break;
    case 5:  tcb->saved_edi    = value; break;
    case 6:  tcb->saved_eip    = value; break;
    case 7:  tcb->saved_esp    = value; break;
    case 8:  tcb->saved_eflags = value; break;
    default: break;
    }
}

/* ------------------------------------------------------------------------ */

uint32_t tcb_get_register(const tcb_t *tcb, uint32_t reg_index)
{
    switch (reg_index) {
    case 0:  return tcb->saved_eax;
    case 1:  return tcb->saved_ebx;
    case 2:  return tcb->saved_ecx;
    case 3:  return tcb->saved_edx;
    case 4:  return tcb->saved_esi;
    case 5:  return tcb->saved_edi;
    case 6:  return tcb->saved_eip;
    case 7:  return tcb->saved_esp;
    case 8:  return tcb->saved_eflags;
    default: return 0;
    }
}

/* ------------------------------------------------------------------------ */

void tcb_block_on_send(tcb_t *tcb, uint32_t endpoint, uint32_t badge)
{
    tcb->state        = THREAD_STATE_BLOCKED_SEND;
    tcb->ipc_endpoint = endpoint;
    tcb->ipc_badge    = badge;
}

/* ------------------------------------------------------------------------ */

void tcb_block_on_recv(tcb_t *tcb, uint32_t endpoint)
{
    tcb->state        = THREAD_STATE_BLOCKED_RECV;
    tcb->ipc_endpoint = endpoint;
}

/* ------------------------------------------------------------------------ */

void tcb_block_on_notify(tcb_t *tcb)
{
    tcb->state = THREAD_STATE_BLOCKED_NOTIFY;
}

/* ------------------------------------------------------------------------ */

void tcb_unblock(tcb_t *tcb)
{
    tcb->state        = THREAD_STATE_READY;
    tcb->ipc_endpoint = 0;
    tcb->ipc_badge    = 0;
}

/* ------------------------------------------------------------------------ */

void tcb_unlink(tcb_t *tcb)
{
    tcb->queue_next = TCB_NONE;
    tcb->queue_prev = TCB_NONE;
}

/* ------------------------------------------------------------------------ */

bool tcb_is_runnable(const tcb_t *tcb)
{
    return tcb->state == THREAD_STATE_READY ||
           tcb->state == THREAD_STATE_RUNNING;
}

/* ------------------------------------------------------------------------ */

bool tcb_is_blocked(const tcb_t *tcb)
{
    return tcb->state == THREAD_STATE_BLOCKED_SEND  ||
           tcb->state == THREAD_STATE_BLOCKED_RECV  ||
           tcb->state == THREAD_STATE_BLOCKED_NOTIFY;
}
