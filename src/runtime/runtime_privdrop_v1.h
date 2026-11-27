#ifndef SIMPLE_PRIVDROP_V1_H
#define SIMPLE_PRIVDROP_V1_H
/* Privilege drop + privilege-dropping spawn (rt_privcred_*_v1, rt_privspawn_*_v1).
 *
 * ABI (identical in the C runtime and the Rust runtime
 * src/compiler_rust/runtime/src/value/sffi/privdrop_v1.rs):
 *   - handles are opaque non-zero i64 owner tokens (one owner, freed once);
 *   - text arguments are (ptr, len) byte spans, NUL bytes rejected;
 *   - every fallible call returns >= 0 on success or
 *       -(step * 65536 + errno)
 *     where step is one of the RT_PRIVDROP_STEP_* codes below.
 * Fixed drop order: setgroups -> setresgid -> setresuid -> verify (ids equal
 * target in real/effective/saved slots, group list equal, setresuid(0) and
 * setresgid(0) both refused). Name lookup only ever happens in the parent.
 * Hosts without POSIX credentials (Windows) return
 * -(RT_PRIVDROP_STEP_UNSUPPORTED * 65536). */
#include <stdint.h>

#define RT_PRIVDROP_STEP_INVALID     1
#define RT_PRIVDROP_STEP_LOOKUP      2
#define RT_PRIVDROP_STEP_SETSID      3
#define RT_PRIVDROP_STEP_CGROUP_OPEN 4
#define RT_PRIVDROP_STEP_CGROUP_WRITE 5
#define RT_PRIVDROP_STEP_SETGROUPS   6
#define RT_PRIVDROP_STEP_SETGID      7
#define RT_PRIVDROP_STEP_SETUID      8
#define RT_PRIVDROP_STEP_VERIFY      9
#define RT_PRIVDROP_STEP_EXEC        10
#define RT_PRIVDROP_STEP_FORK        11
#define RT_PRIVDROP_STEP_PIPE        12
#define RT_PRIVDROP_STEP_NOMEM       13
#define RT_PRIVDROP_STEP_UNSUPPORTED 14
#define RT_PRIVDROP_STEP_FDS         15
#define RT_PRIVDROP_STEP_WAIT        16

int64_t rt_privcred_new_v1(int64_t uid, int64_t gid);
int64_t rt_privcred_from_user_v1(const uint8_t* name, uint64_t name_len);
int64_t rt_privcred_add_group_v1(int64_t cred, int64_t gid);
int64_t rt_privcred_uid_v1(int64_t cred);
int64_t rt_privcred_gid_v1(int64_t cred);
int64_t rt_privcred_group_count_v1(int64_t cred);
int64_t rt_privcred_group_at_v1(int64_t cred, int64_t index);
int64_t rt_privcred_drop_self_v1(int64_t cred);
int64_t rt_privcred_free_v1(int64_t cred);

int64_t rt_privspawn_new_v1(const uint8_t* path, uint64_t path_len);
int64_t rt_privspawn_arg_v1(int64_t spawn, const uint8_t* arg, uint64_t arg_len);
int64_t rt_privspawn_env_v1(int64_t spawn, const uint8_t* entry, uint64_t entry_len);
int64_t rt_privspawn_cred_v1(int64_t spawn, int64_t cred);
int64_t rt_privspawn_join_procs_v1(int64_t spawn, int64_t dir_fd, const uint8_t* name, uint64_t name_len);
int64_t rt_privspawn_new_session_v1(int64_t spawn);
int64_t rt_privspawn_run_v1(int64_t spawn);
int64_t rt_privspawn_free_v1(int64_t spawn);
/* Reap a pid returned by rt_privspawn_run_v1: blocking waitpid, raw status. */
int64_t rt_privspawn_wait_v1(int64_t pid);

#ifdef SIMPLE_PRIVDROP_V1_IMPLEMENTATION
#include "runtime_privdrop_v1.c"
#endif
#endif
