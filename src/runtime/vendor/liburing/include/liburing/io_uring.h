/* SPDX-License-Identifier: (GPL-2.0 WITH Linux-syscall-note) OR MIT */
/*
 * io_uring kernel interface definitions
 * Vendored minimal subset for Simple's async I/O driver.
 *
 * Original: https://github.com/axboe/liburing
 */

#ifndef LIBURING_IO_URING_H
#define LIBURING_IO_URING_H

#include <linux/types.h>
#include <linux/time_types.h>

/*
 * IO submission data structure (Submission Queue Entry)
 */
struct io_uring_sqe {
    __u8    opcode;         /* type of operation for this sqe */
    __u8    flags;          /* IOSQE_ flags */
    __u16   ioprio;         /* ioprio for the request */
    __s32   fd;             /* file descriptor to do IO on */
    union {
        __u64   off;        /* offset into file */
        __u64   addr2;
        struct {
            __u32   cmd_op;
            __u32   __pad1;
        };
    };
    union {
        __u64   addr;       /* pointer to buffer or iovecs */
        __u64   splice_off_in;
    };
    __u32   len;            /* buffer size or number of iovecs */
    union {
        __kernel_rwf_t  rw_flags;
        __u32   fsync_flags;
        __u16   poll_events;
        __u32   poll32_events;
        __u32   sync_range_flags;
        __u32   msg_flags;
        __u32   timeout_flags;
        __u32   accept_flags;
        __u32   cancel_flags;
        __u32   open_flags;
        __u32   statx_flags;
        __u32   fadvise_advice;
        __u32   splice_flags;
        __u32   rename_flags;
        __u32   unlink_flags;
        __u32   hardlink_flags;
        __u32   xattr_flags;
        __u32   msg_ring_flags;
        __u32   uring_cmd_flags;
    };
    __u64   user_data;      /* data to be passed back at completion time */
    /* pack this to avoid bogus arm OABI complaints */
    union {
        /* index into fixed buffers, if used */
        __u16   buf_index;
        /* for grouped buffer selection */
        __u16   buf_group;
    } __attribute__((packed));
    /* personality to use, if used */
    __u16   personality;
    union {
        __s32   splice_fd_in;
        __u32   file_index;
        struct {
            __u16   addr_len;
            __u16   __pad3[1];
        };
    };
    union {
        struct {
            __u64   addr3;
            __u64   __pad2[1];
        };
        __u8    cmd[0];
    };
};

/*
 * sqe->opcode constants
 */
enum io_uring_op {
    IORING_OP_NOP              = 0,
    IORING_OP_READV            = 1,
    IORING_OP_WRITEV           = 2,
    IORING_OP_FSYNC            = 3,
    IORING_OP_READ_FIXED       = 4,
    IORING_OP_WRITE_FIXED      = 5,
    IORING_OP_POLL_ADD         = 6,
    IORING_OP_POLL_REMOVE      = 7,
    IORING_OP_SYNC_FILE_RANGE  = 8,
    IORING_OP_SENDMSG          = 9,
    IORING_OP_RECVMSG          = 10,
    IORING_OP_TIMEOUT          = 11,
    IORING_OP_TIMEOUT_REMOVE   = 12,
    IORING_OP_ACCEPT           = 13,
    IORING_OP_ASYNC_CANCEL     = 14,
    IORING_OP_LINK_TIMEOUT     = 15,
    IORING_OP_CONNECT          = 16,
    IORING_OP_FALLOCATE        = 17,
    IORING_OP_OPENAT           = 18,
    IORING_OP_CLOSE            = 19,
    IORING_OP_FILES_UPDATE     = 20,
    IORING_OP_STATX            = 21,
    IORING_OP_READ             = 22,
    IORING_OP_WRITE            = 23,
    IORING_OP_FADVISE          = 24,
    IORING_OP_MADVISE          = 25,
    IORING_OP_SEND             = 26,
    IORING_OP_RECV             = 27,
    IORING_OP_OPENAT2          = 28,
    IORING_OP_EPOLL_CTL        = 29,
    IORING_OP_SPLICE           = 30,
    IORING_OP_PROVIDE_BUFFERS  = 31,
    IORING_OP_REMOVE_BUFFERS   = 32,
    IORING_OP_TEE              = 33,
    IORING_OP_SHUTDOWN         = 34,
    IORING_OP_RENAMEAT         = 35,
    IORING_OP_UNLINKAT         = 36,
    IORING_OP_MKDIRAT          = 37,
    IORING_OP_SYMLINKAT        = 38,
    IORING_OP_LINKAT           = 39,
    IORING_OP_MSG_RING         = 40,
    IORING_OP_FSETXATTR        = 41,
    IORING_OP_SETXATTR         = 42,
    IORING_OP_FGETXATTR        = 43,
    IORING_OP_GETXATTR         = 44,
    IORING_OP_SOCKET           = 45,
    IORING_OP_URING_CMD        = 46,
    IORING_OP_SEND_ZC          = 47,
    IORING_OP_SENDMSG_ZC       = 48,
    IORING_OP_LAST
};

/*
 * sqe->flags
 */
#define IOSQE_FIXED_FILE        (1U << 0)
#define IOSQE_IO_DRAIN          (1U << 1)
#define IOSQE_IO_LINK           (1U << 2)
#define IOSQE_IO_HARDLINK       (1U << 3)
#define IOSQE_ASYNC             (1U << 4)
#define IOSQE_BUFFER_SELECT     (1U << 5)
#define IOSQE_CQE_SKIP_SUCCESS  (1U << 6)

/*
 * IO completion data structure (Completion Queue Entry)
 */
struct io_uring_cqe {
    __u64   user_data;      /* sqe->data submission passed back */
    __s32   res;            /* result code for this event */
    __u32   flags;
};

/*
 * cqe->flags
 */
#define IORING_CQE_F_BUFFER     (1U << 0)
#define IORING_CQE_F_MORE       (1U << 1)
#define IORING_CQE_F_SOCK_NONEMPTY (1U << 2)
#define IORING_CQE_F_NOTIF      (1U << 3)

/*
 * io_uring_setup() flags
 */
#define IORING_SETUP_IOPOLL     (1U << 0)
#define IORING_SETUP_SQPOLL     (1U << 1)
#define IORING_SETUP_SQ_AFF     (1U << 2)
#define IORING_SETUP_CQSIZE     (1U << 3)
#define IORING_SETUP_CLAMP      (1U << 4)
#define IORING_SETUP_ATTACH_WQ  (1U << 5)
#define IORING_SETUP_R_DISABLED (1U << 6)
#define IORING_SETUP_SUBMIT_ALL (1U << 7)
#define IORING_SETUP_COOP_TASKRUN (1U << 8)
#define IORING_SETUP_TASKRUN_FLAG (1U << 9)
#define IORING_SETUP_SQE128     (1U << 10)
#define IORING_SETUP_CQE32      (1U << 11)
#define IORING_SETUP_SINGLE_ISSUER (1U << 12)
#define IORING_SETUP_DEFER_TASKRUN (1U << 13)

/*
 * Ring offset structures (must be defined before io_uring_params)
 */
struct io_sqring_offsets {
    __u32 head;
    __u32 tail;
    __u32 ring_mask;
    __u32 ring_entries;
    __u32 flags;
    __u32 dropped;
    __u32 array;
    __u32 resv1;
    __u64 user_addr;
};

struct io_cqring_offsets {
    __u32 head;
    __u32 tail;
    __u32 ring_mask;
    __u32 ring_entries;
    __u32 overflow;
    __u32 cqes;
    __u32 flags;
    __u32 resv1;
    __u64 user_addr;
};

/*
 * io_uring_params
 */
struct io_uring_params {
    __u32 sq_entries;
    __u32 cq_entries;
    __u32 flags;
    __u32 sq_thread_cpu;
    __u32 sq_thread_idle;
    __u32 features;
    __u32 wq_fd;
    __u32 resv[3];
    struct io_sqring_offsets sq_off;
    struct io_cqring_offsets cq_off;
};

/*
 * io_uring_enter() flags
 */
#define IORING_ENTER_GETEVENTS  (1U << 0)
#define IORING_ENTER_SQ_WAKEUP  (1U << 1)
#define IORING_ENTER_SQ_WAIT    (1U << 2)
#define IORING_ENTER_EXT_ARG    (1U << 3)

/*
 * Timeout flags
 */
#define IORING_TIMEOUT_ABS      (1U << 0)

/*
 * Cancel flags
 */
#define IORING_ASYNC_CANCEL_ALL (1U << 0)
#define IORING_ASYNC_CANCEL_FD  (1U << 1)
#define IORING_ASYNC_CANCEL_ANY (1U << 2)

#endif /* LIBURING_IO_URING_H */
