/* Deterministic regression for the native snapshot-to-signal exit race. */
#define _DARWIN_C_SOURCE
#include <sys/types.h>
#include <sys/sysctl.h>
#include <sys/proc.h>
#include <sys/wait.h>
#include <signal.h>
#include <errno.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

static int signal_calls, deny_signal, live_members = 1, reap_calls;
static int denied_kill(pid_t pid, int signal_number) {
    assert(pid == -12345 && signal_number == SIGKILL);
    signal_calls++;
    if (!deny_signal) return 0;
    errno = EPERM; return -1;
}
static int exited_waitid(idtype_t type, id_t pid, siginfo_t *info, int options) {
    assert(type == P_PID && pid == 12345);
    assert(options == (WEXITED | WNOHANG | WNOWAIT));
    info->si_pid = (pid_t)pid; return 0;
}
static int live_sysctl(int *mib, u_int count, void *output, size_t *size,
        void *input, size_t input_size) {
    assert(count == 4 && mib[2] == KERN_PROC_PGRP && mib[3] == 12345);
    assert(!input && !input_size);
    if (output && live_members) {
        assert(*size >= sizeof(struct kinfo_proc));
        struct kinfo_proc *process = output;
        memset(process, 0, sizeof(*process)); process->kp_proc.p_stat = SRUN;
    }
    *size = live_members ? sizeof(struct kinfo_proc) : 0; return 0;
}
static pid_t retired_wait4(pid_t pid, int *status, int options, struct rusage *usage) {
    assert(pid == 12345 && options == WNOHANG && !live_members);
    assert(usage); *status = 0; reap_calls++; return pid;
}
#define kill denied_kill
#define waitid exited_waitid
#define sysctl live_sysctl
#define wait4 retired_wait4
#include "../runtime_sosix_darwin_process_private.h"
#undef kill
#undef waitid
#undef sysctl
#undef wait4

int main(void) {
    SosixDarwinProcess owner; memset(&owner, 0, sizeof(owner));
    owner.generation = 42; owner.pid = 12345;
    owner.stdout_fd = owner.stderr_fd = -1;
    owner.cleanup_deadline = sosix_darwin_process_now() + 1000000000LL;
    assert(!sosix_darwin_process_poll(&owner, 42, 0));
    assert(signal_calls == 1 && owner.leader_exited && owner.kill_sent);
    deny_signal = 1;
    assert(!sosix_darwin_process_poll(&owner, 42, 0));
    assert(signal_calls == 2 && !reap_calls);
    assert(!owner.reaped && !owner.group_retired && !owner.frozen);
    assert(owner.generation == 42 && sosix_darwin_process_ack(&owner, 42) == EBUSY);
    puts("PASS Darwin signal race: repeated EPERM retains process authority");

    owner.cleanup_deadline = sosix_darwin_process_now() - 1;
    assert(sosix_darwin_process_poll(&owner, 42, 0) == ETIMEDOUT);
    assert(owner.cleanup_error == ETIMEDOUT && owner.generation == 42);
    assert(!owner.reaped && !owner.group_retired && !owner.frozen);
    assert(sosix_darwin_process_ack(&owner, 42) == EBUSY);
    puts("PASS Darwin signal race: persistent denial reaches cleanup deadline");

    owner.kill_sent = 0;
    assert(sosix_darwin_process_poll(&owner, 42, 0) == EPERM);
    assert(!owner.kill_sent && !owner.reaped && !owner.group_retired);
    puts("PASS Darwin signal race: initial permission denial remains an error");

    owner.kill_sent = 1; live_members = 0;
    assert(!sosix_darwin_process_poll(&owner, 42, 0));
    assert(reap_calls == 1 && owner.reaped && owner.group_retired && owner.frozen);
    assert(!sosix_darwin_process_poll(&owner, 42, 0) && reap_calls == 1);
    assert(!sosix_darwin_process_ack(&owner, 42) && !owner.generation);
    puts("PASS Darwin signal race: independent empty snapshot permits one reap and acknowledgement");
    return 0;
}
