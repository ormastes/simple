/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * common/config.h — Kernel configuration constants
 *
 * Compiled with: clang -O2 -ffreestanding -nostdlib
 */

#ifndef SIMPLE_OS_CONFIG_H
#define SIMPLE_OS_CONFIG_H

/* ── Thread / scheduling ──────────────────────────────────────────── */
#define MAX_THREADS       256
#define MAX_CAPS          4096
#define MAX_PRIORITY      255
#define NUM_PRIORITIES    256

/* ── Memory ───────────────────────────────────────────────────────── */
#define PAGE_SIZE         4096
#define PAGE_SHIFT        12

/* ── IPC objects ──────────────────────────────────────────────────── */
#define MAX_ENDPOINTS     64
#define MAX_NOTIFICATIONS 64

/* ── Bitmap allocator ─────────────────────────────────────────────── */
#define BITMAP_MAX_WORDS     1024
#define BITMAP_BITS_PER_WORD 32
#define BITMAP_MAX_BITS      (BITMAP_MAX_WORDS * BITMAP_BITS_PER_WORD)

/* ── Linked-list sentinel ─────────────────────────────────────────── */
#define LIST_NONE         0xFFFFFFFF

/* ── Ring buffer ──────────────────────────────────────────────────── */
#define RING_MAX_CAPACITY 256

/* ── Frame allocator ──────────────────────────────────────────────── */
#define MAX_FRAMES        32768

/* ── IPC buffer ───────────────────────────────────────────────────── */
#define IPC_BUFFER_SIZE   4096
#define IPC_MAX_MRS       120
#define IPC_MAX_CAPS      8

/* ── Kernel stack ─────────────────────────────────────────────────── */
#define KERNEL_STACK_SIZE 16384

/* ── Timer ────────────────────────────────────────────────────────── */
#define TICK_FREQ_HZ      100

#endif /* SIMPLE_OS_CONFIG_H */
