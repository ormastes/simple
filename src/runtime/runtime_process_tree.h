/* Session-owned process trees: the one mechanism by which a timed-out test
 * kills everything it started, on every host.
 *
 * Ownership is taken AT SPAWN. rt_process_spawn_session() forks, calls
 * setsid() in the child and execs, so the child's pid is also its session id
 * and every descendant inherits that session (setpgid cannot leave a session;
 * only a descendant that itself calls setsid() can). Cleanup is then
 * rt_process_kill_tree(pid): signal every live process whose session id is
 * pid, then reap the leader. A `sh -c 'sleep 300 &'` grandchild that was
 * reparented to init and sits in its own process group is still in the
 * session, so it dies too. A pgid kill or a ppid walk cannot reach it.
 *
 * Host arms (one entry point each, no silent success):
 *   Linux    /proc scan + getsid(2)
 *   macOS    proc_listallpids(3) + getsid(2)       (verified 2026-10-30)
 *   FreeBSD  sysctl KERN_PROC_PROC -> kinfo_proc.ki_sid
 *   Windows  not this owner: the Job object (KILL_ON_JOB_CLOSE) in
 *            runtime_process_owned.c owns capture children. Every function
 *            here returns RT_PTREE_UNSUPPORTED there.
 *   other    RT_PTREE_UNSUPPORTED (SimpleOS and any host without one of the
 *            arms above). Callers must turn that into an explicit error.
 *
 * Known limit on every POSIX host, by design: a descendant that calls
 * setsid() itself (a daemon) leaves the session and is not found. Ok from
 * rt_process_kill_tree means "the session was enumerated and every member was
 * signalled", never "no descendant survives". Linux PR_SET_CHILD_SUBREAPER is
 * the follow-up for that case.
 *
 * This file is compiled into the Rust runtime crate (build.rs c_sources) AND
 * the core-C archives, so it depends on libc only: no runtime.h types.
 * Return codes are 0 / positive on success and -errno on failure; the
 * two symbolic values below never collide with an errno. */
#ifndef SIMPLE_RUNTIME_PROCESS_TREE_H
#define SIMPLE_RUNTIME_PROCESS_TREE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* "No implementation on this host." Distinct from every -errno. */
#define RT_PTREE_UNSUPPORTED (-100000)
/* "pid is alive but is not a session leader this API spawned." */
#define RT_PTREE_NOT_SESSION_LEADER (-100001)
/* rt_process_kill_tree: the leader was reaped (or is no longer this process's
 * child), but the second sweep's enumeration failed. The pid is no longer
 * owned (it may be recycled), so callers must stop tracking it; survivors of
 * the race the second sweep guards against may remain. */
#define RT_PTREE_SWEEP_FAILED_AFTER_REAP (-100002)

/* 0 when session ownership works on this host, RT_PTREE_UNSUPPORTED otherwise. */
int64_t rt_process_tree_support(void);

/* fork + setsid + execvp. args has arg_count entries (argv[1..]).
 *   > 0  child pid (== its session id)
 *   -errno  fork/pipe/exec failure (the child never ran user code)
 *   RT_PTREE_UNSUPPORTED  on hosts without the owner */
int64_t rt_process_spawn_session(const char* cmd, const char** args, int64_t arg_count);

/* waitpid on a session leader. Same contract as rt_process_wait:
 *   >= 0  exit code       -(128+signo)  signal death
 *   -1    error (not our child, invalid pid)
 *   -2    still running at the deadline (timeout_ms > 0)
 * timeout_ms <= 0 blocks until exit. */
int64_t rt_process_session_wait(int64_t pid, int64_t timeout_ms);

/* 1 while the leader is alive (a reapable zombie counts as exited), 0 otherwise.
 * Never reaps: the exit status stays for rt_process_session_wait. */
int64_t rt_process_session_is_running(int64_t pid);

/* Send signo to every live process whose session id is sid, except the caller.
 *   >= 0  number of processes signalled (0 is a valid answer: nothing left)
 *   -EINVAL  sid <= 1, or sid is the caller's own session
 *   -errno   enumeration failed
 *   RT_PTREE_UNSUPPORTED */
int64_t rt_process_kill_session(int64_t sid, int32_t signo);

/* SIGKILL the whole session of a leader spawned by rt_process_spawn_session,
 * reap the leader, and sweep once more for forks that raced the first pass.
 *   0  session enumerated, every member signalled, leader reaped or not ours
 *   RT_PTREE_NOT_SESSION_LEADER  pid is alive and getsid(pid) != pid
 *   RT_PTREE_SWEEP_FAILED_AFTER_REAP  leader gone, second sweep failed
 *   -EINVAL / -errno / RT_PTREE_UNSUPPORTED  as above */
int64_t rt_process_kill_tree(int64_t pid);

/* Child-side: die with signo when the parent exits.
 *   0   armed            -errno  supported but failed
 *   RT_PTREE_UNSUPPORTED  no parent-death signal on this host (macOS, Windows)
 * Callers must re-check getppid() afterwards: a parent that died before this
 * call never triggers it. Linux prctl(PR_SET_PDEATHSIG); FreeBSD
 * procctl(PROC_PDEATHSIG_CTL). */
int64_t rt_child_set_pdeathsig(int32_t signo);

/* Process birth identity for the pid-reuse guard, in the host's own unit:
 * Linux /proc stat field 22 (clock ticks since boot), macOS proc_pidinfo
 * start time in microseconds, FreeBSD kinfo_proc.ki_start in microseconds,
 * Windows FILETIME creation ticks. 0 means unavailable (no such process, no
 * permission, or no arm for this host); callers treat 0 as "cannot verify". */
int64_t rt_proc_start_time(int64_t pid);

#ifdef __cplusplus
}
#endif

#endif /* SIMPLE_RUNTIME_PROCESS_TREE_H */
