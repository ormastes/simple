/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/tcb.h -- Thread Control Block
 *
 * Mirrors: spl/kernel/core/tcb.spl
 */

#ifndef SIMPLE_OS_TCB_H
#define SIMPLE_OS_TCB_H

#include "common/types.h"
#include "common/config.h"

/* ---- Constants --------------------------------------------------------- */

#define TCB_NONE           0xFFFFFFFF   /* Sentinel: no thread */
#define THREAD_NAME_MAX    32

/* ---- Thread states ----------------------------------------------------- */

typedef enum {
    THREAD_STATE_INACTIVE       = 0,
    THREAD_STATE_RUNNING        = 1,
    THREAD_STATE_READY          = 2,
    THREAD_STATE_BLOCKED_SEND   = 3,
    THREAD_STATE_BLOCKED_RECV   = 4,
    THREAD_STATE_BLOCKED_NOTIFY = 5,
    THREAD_STATE_SUSPENDED      = 6,
} thread_state_t;

/* ---- Thread Control Block ---------------------------------------------- */

typedef struct {
    uint32_t       id;
    char           name[THREAD_NAME_MAX];
    thread_state_t state;
    uint32_t       priority;           /* 0-255, higher = higher priority */
    uint32_t       time_slice;         /* Remaining ticks in current quantum */

    /* Saved register state (x86) */
    uint32_t saved_eip;
    uint32_t saved_esp;
    uint32_t saved_eflags;
    uint32_t saved_eax;
    uint32_t saved_ebx;
    uint32_t saved_ecx;
    uint32_t saved_edx;
    uint32_t saved_esi;
    uint32_t saved_edi;
    uint32_t saved_cs;
    uint32_t saved_ds;
    uint32_t saved_ss;

    /* Address space */
    uint32_t page_dir_phys;            /* Physical address of page directory */

    /* Capability space */
    uint32_t cspace_root;              /* Root CNode capability index */

    /* IPC configuration */
    uint32_t ipc_buffer_addr;          /* Virtual address of IPC buffer */
    uint32_t fault_endpoint;           /* Cap index for fault delivery */
    uint32_t bound_notification;       /* Bound notification cap (0 = none) */

    /* IPC state (populated when blocked) */
    uint32_t ipc_endpoint;
    uint32_t ipc_badge;

    /* Scheduling */
    uint32_t sched_context;            /* Index of associated SchedContext */

    /* Intrusive queue linkage (scheduler & IPC wait queues) */
    uint32_t queue_next;               /* Next TCB id, or TCB_NONE */
    uint32_t queue_prev;               /* Previous TCB id, or TCB_NONE */
} tcb_t;

/* ---- API --------------------------------------------------------------- */

/* Create a new TCB in the Inactive state. */
void tcb_init(tcb_t *tcb, uint32_t id, uint32_t priority);

/* Configure registers, address space, and CSpace in one call. */
void tcb_configure(tcb_t *tcb, uint32_t eip, uint32_t esp,
                   uint32_t page_dir, uint32_t cspace_root,
                   uint32_t ipc_buffer_addr);

/* State transitions */
void tcb_set_state(tcb_t *tcb, thread_state_t state);
void tcb_set_priority(tcb_t *tcb, uint32_t priority);
void tcb_suspend(tcb_t *tcb);
void tcb_resume(tcb_t *tcb);

/* Register access */
void tcb_save_context(tcb_t *tcb, uint32_t eip, uint32_t esp,
                      uint32_t eflags, uint32_t eax, uint32_t ebx,
                      uint32_t ecx, uint32_t edx, uint32_t esi,
                      uint32_t edi);
void tcb_restore_context(const tcb_t *tcb, uint32_t *eip, uint32_t *esp,
                         uint32_t *eflags, uint32_t *eax, uint32_t *ebx,
                         uint32_t *ecx, uint32_t *edx, uint32_t *esi,
                         uint32_t *edi);
void tcb_set_register(tcb_t *tcb, uint32_t reg_index, uint32_t value);
uint32_t tcb_get_register(const tcb_t *tcb, uint32_t reg_index);

/* IPC helpers */
void tcb_block_on_send(tcb_t *tcb, uint32_t endpoint, uint32_t badge);
void tcb_block_on_recv(tcb_t *tcb, uint32_t endpoint);
void tcb_block_on_notify(tcb_t *tcb);
void tcb_unblock(tcb_t *tcb);

/* Queue linkage */
void tcb_unlink(tcb_t *tcb);

/* Query helpers */
bool tcb_is_runnable(const tcb_t *tcb);
bool tcb_is_blocked(const tcb_t *tcb);

#endif /* SIMPLE_OS_TCB_H */
