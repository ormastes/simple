/* Private implementation, instantiated by exactly one runtime provider.
 * Tokens are generations, NEVER descriptors. Same flock/LockFileEx namespace
 * as rt_file_lock; no journal, path cache, or fallback lock is introduced. */
#ifndef SIMPLE_RUNTIME_FILE_LOCK_OWNED_V2_H
#define SIMPLE_RUNTIME_FILE_LOCK_OWNED_V2_H
#include <stdint.h>
#include <limits.h>
#include <string.h>
#include <stdatomic.h>
#if defined(_WIN32)
#include <windows.h>
typedef HANDLE SplOwnedLockNativeV2;
#else
#include <errno.h>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>
#if defined(__linux__)
#include <sys/vfs.h>
#include <sys/ioctl.h>
#include <linux/nsfs.h>
#include <linux/magic.h>
#include <linux/sched.h>
#endif
typedef int SplOwnedLockNativeV2;
#endif

/* Hooks are compile-time native-test adapter seams, never runtime switches.
 * Test wrappers call the actual OS operation except the one selected fault. */
#ifndef SPL_OWNED_LOCK_UNLOCK_V2
#if defined(_WIN32)
#define SPL_OWNED_LOCK_UNLOCK_V2(h, o) UnlockFileEx((h), 0, MAXDWORD, MAXDWORD, (o))
#else
#define SPL_OWNED_LOCK_UNLOCK_V2(h, o) (flock((h), LOCK_UN) == 0)
#endif
#endif
#ifndef SPL_OWNED_LOCK_CLOSE_V2
#if defined(_WIN32)
#define SPL_OWNED_LOCK_CLOSE_V2(h) (CloseHandle(h) != 0)
#else
#define SPL_OWNED_LOCK_CLOSE_V2(h) (close(h) == 0)
#endif
#endif

typedef struct {
    int64_t token;
    uint64_t pid;
    atomic_int state; /* 1 held, 2 close pending, 3 unknown, 4 acquiring, 5 cleanup-held */
    SplOwnedLockNativeV2 native;
} SplOwnedLockSlotV2;
#define SPL_OWNED_LOCK_SLOTS_V2 256
static SplOwnedLockSlotV2 spl_owned_locks_v2[SPL_OWNED_LOCK_SLOTS_V2];
static int64_t spl_owned_lock_generation_v2;
static atomic_flag spl_owned_lock_gate_v2 = ATOMIC_FLAG_INIT;
#if defined(__linux__)
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "owned lock origin requires lock-free phase atomics");
/* 0 virgin, 1 initializing, 2 immutable published identity, 3 quarantined.
 * Only an unsuccessful virgin probe can return to 0; established origin and
 * its inherited gate are never reset. No reader waits for initialization. */
static atomic_uint spl_owned_lock_origin_phase_v2;
static uint64_t spl_owned_lock_origin_pid_v2;
static dev_t spl_owned_lock_origin_device_v2;
static ino_t spl_owned_lock_origin_inode_v2;
#ifndef SPL_OWNED_LOCK_NAMESPACE_STAT_V2
#define SPL_OWNED_LOCK_NAMESPACE_STAT_V2(observed) stat("/proc/self/ns/pid", (observed))
#endif
/* Same concrete initial proof as the native storage/local-Unix owners. The
 * temporary fd exists ONLY before an owner is established. Linux close is
 * checked once, never retried, including EINTR. No runtime allocation. */
static int spl_owned_lock_initial_namespace_v2(struct stat *observed) {
    int fd = open("/proc/self/ns/pid", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    struct statfs filesystem;
    int valid = fstat(fd, observed) == 0 && fstatfs(fd, &filesystem) == 0 &&
        (unsigned long)filesystem.f_type == (unsigned long)NSFS_MAGIC &&
        ioctl(fd, NS_GET_NSTYPE) == CLONE_NEWPID;
    int closed = close(fd);
    return valid && closed == 0;
}
static int spl_owned_lock_origin_check_impl_v2(void) {
    unsigned phase = atomic_load_explicit(&spl_owned_lock_origin_phase_v2, memory_order_acquire);
    if (phase == 3 || phase == 1) return 0;
    uint64_t pid = (uint64_t)getpid();
    if (phase == 0) {
        unsigned expected = 0;
        if (!atomic_compare_exchange_strong_explicit(&spl_owned_lock_origin_phase_v2,
                &expected, 1, memory_order_acq_rel, memory_order_acquire)) return 0;
        struct stat identity;
        if (!spl_owned_lock_initial_namespace_v2(&identity)) {
            atomic_store_explicit(&spl_owned_lock_origin_phase_v2, 0, memory_order_release);
            return 0;
        }
        spl_owned_lock_origin_pid_v2 = pid;
        spl_owned_lock_origin_device_v2 = identity.st_dev;
        spl_owned_lock_origin_inode_v2 = identity.st_ino;
        atomic_store_explicit(&spl_owned_lock_origin_phase_v2, 2, memory_order_release);
        return 1;
    }
    struct stat identity;
    if (pid != spl_owned_lock_origin_pid_v2 || SPL_OWNED_LOCK_NAMESPACE_STAT_V2(&identity) != 0 ||
        identity.st_dev != spl_owned_lock_origin_device_v2 || identity.st_ino != spl_owned_lock_origin_inode_v2) {
        atomic_store_explicit(&spl_owned_lock_origin_phase_v2, 3, memory_order_release);
        return 0;
    }
    return atomic_load_explicit(&spl_owned_lock_origin_phase_v2, memory_order_acquire) == 2;
}
static int spl_owned_lock_origin_check_v2(void) {
    int saved_errno = errno;
    int valid = spl_owned_lock_origin_check_impl_v2();
    errno = saved_errno;
    return valid;
}
#else
static atomic_uint_fast64_t spl_owned_lock_origin_v2;
static int spl_owned_lock_origin_check_v2(void) {
    uint_fast64_t pid;
#if defined(_WIN32)
    pid = (uint_fast64_t)GetCurrentProcessId();
#else
    pid = (uint_fast64_t)getpid();
#endif
    uint_fast64_t origin = atomic_load_explicit(&spl_owned_lock_origin_v2, memory_order_acquire);
    if (!origin) {
        uint_fast64_t expected = 0;
        atomic_compare_exchange_strong_explicit(&spl_owned_lock_origin_v2, &expected, pid,
            memory_order_acq_rel, memory_order_acquire);
        origin = atomic_load_explicit(&spl_owned_lock_origin_v2, memory_order_acquire);
    }
    return origin == pid;
}
#endif
static uint64_t spl_owned_lock_pid_v2(void) {
#if defined(_WIN32)
    return (uint64_t)GetCurrentProcessId();
#else
    return (uint64_t)getpid();
#endif
}
/* Refuse foreign/uncertain origin BEFORE a possibly inherited held gate.
 * Recheck periodically under contention and immediately after acquisition.
 * If the post-check fails, leave the quarantined gate untouched. */
static int spl_owned_lock_enter_v2(void) {
    if (!spl_owned_lock_origin_check_v2()) return 0;
    unsigned spins = 0;
    while (atomic_flag_test_and_set_explicit(&spl_owned_lock_gate_v2, memory_order_acquire)) {
        if ((++spins & 63U) == 0 && !spl_owned_lock_origin_check_v2()) return 0;
    }
    if (!spl_owned_lock_origin_check_v2()) return 0;
    return 1;
}
static void spl_owned_lock_leave_v2(void) {
    atomic_flag_clear_explicit(&spl_owned_lock_gate_v2, memory_order_release);
}
static SplOwnedLockSlotV2 *spl_owned_lock_find_v2(int64_t token) {
    if (token <= 0) return NULL;
    uint64_t pid = spl_owned_lock_pid_v2();
    for (int i = 0; i < SPL_OWNED_LOCK_SLOTS_V2; ++i)
        if (spl_owned_locks_v2[i].token == token && spl_owned_locks_v2[i].pid == pid)
            return &spl_owned_locks_v2[i];
    return NULL;
}

/* Called under gate. An unlocked handle is still an owned resource.
 * Linux close consumes the fd even on EINTR: invalidate BEFORE syscall.
 * Other POSIX close errors are quarantined, never retried by descriptor.
 * Windows CloseHandle failure retains the exact handle for a later retry. */
static int64_t spl_owned_lock_close_v2(SplOwnedLockSlotV2 *slot) {
    SplOwnedLockNativeV2 native = slot->native;
#if defined(_WIN32)
    if (!SPL_OWNED_LOCK_CLOSE_V2(native)) { slot->state = 2; return 2; }
    slot->token = 0;
    slot->state = 0;
    return 1;
#elif defined(__linux__)
    slot->token = 0;
    slot->state = 0;
    return SPL_OWNED_LOCK_CLOSE_V2(native) ? 1 : 4;
#else
    slot->state = 3;
    if (!SPL_OWNED_LOCK_CLOSE_V2(native)) return 3;
    slot->token = 0;
    slot->state = 0;
    return 1;
#endif
}

/* acquire returns 0 (no retained resource), or a token whose authoritative
 * state MUST be inspected. No successful open is ever hidden by close error.
 * Polling occurs outside the gate; only this acquiring thread can touch slot.
 * The bounded table has no allocation after acquiring an OS descriptor. */
int64_t rt_file_lock_owned_acquire_v2(const uint8_t *path_ptr, uint64_t path_len,
                                     int64_t timeout_secs) {
    if (!path_ptr || !path_len || path_len >= 4096 ||
        memchr(path_ptr, 0, (size_t)path_len) || timeout_secs < 0 || timeout_secs > 60) return 0;
    char path[4096];
    memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = 0;
    if (!spl_owned_lock_enter_v2()) return 0;
    SplOwnedLockSlotV2 *slot = NULL;
    for (int i = 0; i < SPL_OWNED_LOCK_SLOTS_V2; ++i)
        if (spl_owned_locks_v2[i].token == 0) { slot = &spl_owned_locks_v2[i]; break; }
    /* UNKNOWN never permits another owned writer in this process, even at a
     * different path. There is no inference that its OS resource disappeared. */
    int unknown = 0;
    for (int i = 0; i < SPL_OWNED_LOCK_SLOTS_V2; ++i)
        if (spl_owned_locks_v2[i].pid == spl_owned_lock_pid_v2() && spl_owned_locks_v2[i].state == 3)
            unknown = 1;
    if (!slot || unknown || spl_owned_lock_generation_v2 == INT64_MAX) {
        spl_owned_lock_leave_v2(); return 0;
    }
    int64_t token = ++spl_owned_lock_generation_v2;
    slot->token = token;
    slot->pid = spl_owned_lock_pid_v2();
    slot->state = 4;
    spl_owned_lock_leave_v2();
#if defined(_WIN32)
    wchar_t wide[4096];
    int converted = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS,
        path, (int)path_len, wide, 4095);
    HANDLE native = INVALID_HANDLE_VALUE;
    if (converted > 0) {
        wide[converted] = 0;
        native = CreateFileW(wide, GENERIC_READ | GENERIC_WRITE,
            FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_ALWAYS,
            FILE_ATTRIBUTE_NORMAL | FILE_FLAG_OPEN_REPARSE_POINT, NULL);
    }
    int opened = native != INVALID_HANDLE_VALUE;
    int eligible = 0;
    if (opened) {
        BY_HANDLE_FILE_INFORMATION info;
        eligible = GetFileInformationByHandle(native, &info) &&
            !(info.dwFileAttributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT));
    }
    ULONGLONG start = GetTickCount64();
#else
    int native = open(path, O_RDWR | O_CREAT | O_CLOEXEC | O_NOFOLLOW, 0644);
    int opened = native >= 0;
    struct stat metadata;
    int eligible = opened && fstat(native, &metadata) == 0 && S_ISREG(metadata.st_mode);
#endif
    int locked = 0;
    int64_t waited_ms = 0;
    while (eligible) {
#if defined(_WIN32)
        OVERLAPPED overlapped;
        memset(&overlapped, 0, sizeof(overlapped));
        if (LockFileEx(native, LOCKFILE_EXCLUSIVE_LOCK | LOCKFILE_FAIL_IMMEDIATELY,
                0, MAXDWORD, MAXDWORD, &overlapped)) { locked = 1; break; }
        DWORD error = GetLastError();
        if (error != ERROR_LOCK_VIOLATION) break;
        if (GetTickCount64() - start >= (ULONGLONG)timeout_secs * 1000U) break;
        Sleep(50);
#else
        if (flock(native, LOCK_EX | LOCK_NB) == 0) { locked = 1; break; }
        if (errno != EWOULDBLOCK && errno != EAGAIN && errno != EINTR) break;
        if (waited_ms >= timeout_secs * 1000) break;
        struct timespec pause = {0, 50000000L};
        nanosleep(&pause, NULL);
        waited_ms += 50;
#endif
    }
    if (!spl_owned_lock_enter_v2()) {
        if (!opened) return 0; /* no native resource; quarantined reservation */
        /* The acquiring thread alone owns a state4 slot. No reader of state4
         * touches native or clears token. Publish local ownership as UNKNOWN
         * without any gate/native close after origin loss. */
        slot->native = native;
        atomic_store_explicit(&slot->state, 3, memory_order_release);
        return token;
    }
    if (!opened) { slot->token = 0; slot->state = 0; token = 0; }
    else {
        slot->native = native;
        int admission_blocked = 0;
        for (int i = 0; i < SPL_OWNED_LOCK_SLOTS_V2; ++i)
            if (spl_owned_locks_v2[i].pid == spl_owned_lock_pid_v2() && spl_owned_locks_v2[i].state == 3)
                admission_blocked = 1;
        /* A concurrent close may quarantine a different slot during polling.
         * Keep this exact lock only as cleanup, never admit a new writer. */
        slot->state = locked ? (admission_blocked ? 5 : 1) : 2;
        if (!locked) {
            int64_t closed = spl_owned_lock_close_v2(slot);
            if (closed == 1 || closed == 4) token = 0;
        }
    }
    spl_owned_lock_leave_v2();
    return token;
}

int64_t rt_file_lock_owned_state_v2(int64_t token) {
    if (!spl_owned_lock_enter_v2()) return token > 0 ? 3 : 0;
    SplOwnedLockSlotV2 *slot = spl_owned_lock_find_v2(token);
    int64_t state = slot ? slot->state : 0;
    spl_owned_lock_leave_v2();
    return state;
}

/* 0 stale, 1 released, 2 retained/retryable, 3 unknown/not retryable,
 * 4 consumed with close error. Unknown tokens never issue another native call. */
int64_t rt_file_lock_owned_release_v2(int64_t token) {
    if (!spl_owned_lock_enter_v2()) return token > 0 ? 3 : 0;
    SplOwnedLockSlotV2 *slot = spl_owned_lock_find_v2(token);
    if (!slot) { spl_owned_lock_leave_v2(); return 0; }
    /* One acquire snapshot: state4 may concurrently publish UNKNOWN without
     * this gate. Multiple phase reads could otherwise fall through to close. */
    int phase = atomic_load_explicit(&slot->state, memory_order_acquire);
    if (phase == 3) { spl_owned_lock_leave_v2(); return 3; }
    if (phase == 4) { spl_owned_lock_leave_v2(); return 2; }
    if (phase == 1 || phase == 5) {
#if defined(_WIN32)
        OVERLAPPED overlapped;
        memset(&overlapped, 0, sizeof(overlapped));
        int unlocked = SPL_OWNED_LOCK_UNLOCK_V2(slot->native, &overlapped);
#else
        int unlocked = SPL_OWNED_LOCK_UNLOCK_V2(slot->native, NULL);
#endif
        if (!unlocked) { spl_owned_lock_leave_v2(); return 2; }
        slot->state = 2;
    }
    int64_t result = spl_owned_lock_close_v2(slot);
    spl_owned_lock_leave_v2();
    return result;
}
#endif
