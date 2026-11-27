#ifndef __APPLE__
#include <stdio.h>
int main(void) { puts("SKIP: Darwin coalition evidence requires macOS"); return 77; }
#else
#define _DARWIN_C_SOURCE
static void late_fork_hook(void);
#define SOSIX_DARWIN_COALITION_AFTER_CENSUS() late_fork_hook()
#include "../runtime_sosix_darwin_coalition_private.h"
#include <assert.h>
#include <stdio.h>
#include <sys/wait.h>
#include <spawn.h>
#include <sys/event.h>

static audit_token_t race_token;
static const char *race_report;
static unsigned worker_watchdog = 20;
static int deadline_hook_armed, deadline_hook_observed;

static void late_child(int signum) {
    (void)signum;
    pid_t child = fork();
    if (child < 0) _exit(91);
    if (!child) {
        alarm(worker_watchdog);
        const char ready[] = "late_child_ready\n";
        if (write(STDOUT_FILENO, ready, sizeof(ready) - 1) != sizeof(ready) - 1) _exit(92);
        for (;;) pause();
    }
}

static void pause_ms(unsigned ms) {
    struct timespec t = {ms / 1000, (ms % 1000) * 1000000L};
    while (nanosleep(&t, &t) && errno == EINTR) {}
}

static void late_fork_hook(void) {
    if (deadline_hook_armed) {
        deadline_hook_armed = 0; deadline_hook_observed = 1;
        pause_ms(300); return;
    }
    if (!race_report) return;
    const char *report = race_report; race_report = NULL;
    assert(!sosix_darwin_coalition_signal(&race_token, SIGUSR1));
    for (int attempt = 0; attempt < 500; attempt++) {
        FILE *in = fopen(report, "r"); assert(in);
        char bytes[4096] = {0}; size_t n = fread(bytes, 1, sizeof(bytes) - 1, in);
        assert(!ferror(in)); fclose(in); bytes[n] = 0;
        if (strstr(bytes, "late_child_ready\n")) return;
        pause_ms(1);
    }
    assert(!"late fork acknowledgement timed out");
}

static uint64_t current_coalition(void) {
    SosixDarwinCoalitionInfo info;
    assert(!sosix_darwin_coalition_info(getpid(), &info));
    return info.ids[0];
}

static void worker(int normal_exit) {
    alarm(worker_watchdog); setvbuf(stdout, NULL, _IONBF, 0);
    dprintf(STDOUT_FILENO, "root %d %llu\n", getpid(), current_coalition());
    /* An unreaped zombie already contributes to exited task accounting. */
    uint64_t started, exited, after_started, after_exited;
    assert(!sosix_darwin_coalition_counts(current_coalition(), &started, &exited));
    pid_t zombie = fork(); assert(zombie >= 0);
    if (!zombie) _exit(0);
    siginfo_t info; memset(&info, 0, sizeof(info));
    assert(!waitid(P_PID, zombie, &info, WEXITED | WNOWAIT));
    SosixDarwinProcessIdentity zombie_identity;
    assert(!sosix_darwin_coalition_identity(zombie, &zombie_identity, 1));
    assert(!sosix_darwin_coalition_counts(current_coalition(), &after_started, &after_exited));
    assert(after_started == started + 1 && after_exited == exited + 1);
    assert(waitpid(zombie, NULL, 0) == zombie);
    dprintf(STDOUT_FILENO, "zombie-exited 0 %llu\n", current_coalition());
    for (int i = 0; i < 3; i++) {
        pid_t child = fork(); assert(child >= 0);
        if (!child) {
            alarm(worker_watchdog); signal(SIGTERM, SIG_IGN);
            if (i == 0) signal(SIGUSR1, late_child);
            if (i == 0) assert(setpgid(0, 0) == 0);
            else assert(setsid() == getpid());
            if (i == 2) {
                pid_t grandchild = fork(); assert(grandchild >= 0);
                if (grandchild) _exit(0);
                /* POSIX fork clears pending alarms in the new child. */
                assert(alarm(worker_watchdog) == 0);
            }
            dprintf(STDOUT_FILENO, "child %d %llu\n", getpid(), current_coalition());
            /* New membership can appear after a supervisor's census. The
             * bounded churn keeps this a regression test, not a fork bomb. */
            if (i == 1) for (int j = 0; j < 16; j++) {
                pause_ms(2);
                pid_t churn = fork(); assert(churn >= 0);
                if (!churn) { alarm(worker_watchdog); for (;;) pause(); }
            }
            for (;;) pause();
        }
    }
    if (normal_exit) { pause_ms(300); _exit(0); }
    for (;;) pause();
}

static void run_launchctl(const char *service, int normal_exit) {
    char *args[] = {"/bin/launchctl", "bootout", (char *)service, NULL};
    char *environment[] = {"PATH=/usr/bin:/bin", NULL};
    pid_t pid; assert(!posix_spawn(&pid, args[0], NULL, NULL, args, environment));
    int status; assert(waitpid(pid, &status, 0) == pid);
    assert(WIFEXITED(status) && (WEXITSTATUS(status) == 0 ||
        (normal_exit && WEXITSTATUS(status) == 3)));
}

static void controller(const char *report, const char *service, int normal_exit, int watchdog_only) {
    alarm(20);
    pid_t root = 0, children[3] = {0}; uint64_t coalition = 0;
    unsigned nchildren = 0;
    for (int attempt = 0; attempt < 500; attempt++) {
        FILE *in = fopen(report, "r");
        if (in) {
            char kind[16]; int pid; unsigned long long cid;
            root = 0; coalition = 0; nchildren = 0;
            while (fscanf(in, "%15s %d %llu", kind, &pid, &cid) == 3) {
                if (!strcmp(kind, "root")) { root = pid; coalition = cid; }
                else if (!strcmp(kind, "child")) {
                    assert(cid == coalition && nchildren < 3);
                    children[nchildren++] = pid;
                }
            }
            fclose(in);
        }
        if (root && nchildren == 3) break;
        pause_ms(2);
    }
    assert(root > 1 && nchildren == 3 && coalition != current_coalition());
    audit_token_t root_token;
    assert(!sosix_darwin_coalition_member_token(root, coalition, &root_token));
    audit_token_t stale = root_token; stale.val[7]++;
    assert(sosix_darwin_coalition_signal(&stale, SIGKILL) == ESRCH);
    SosixDarwinProcessIdentity root_identity;
    assert(!sosix_darwin_coalition_identity(root, &root_identity, 0));
    assert(root_identity.pid_version == (int32_t)root_token.val[7]);
    audit_token_t wrong_member;
    assert(sosix_darwin_coalition_member_token(getpid(), coalition, &wrong_member) == EXDEV);
    int queue = kqueue(); assert(queue >= 0);
    SosixDarwinProcessIdentity identities[3];
    for (int i = 0; i < 3; i++) {
        assert(getpgid(children[i]) != root);
        assert(!sosix_darwin_coalition_identity(children[i], &identities[i], 0));
        struct kevent change;
        EV_SET(&change, children[i], EVFILT_PROC, EV_ADD | EV_CLEAR,
            NOTE_EXIT | NOTE_REAP | NOTE_EXITSTATUS, 0, NULL);
        assert(!kevent(queue, &change, 1, NULL, 0, NULL));
    }
    if (normal_exit) pause_ms(350);
    run_launchctl(service, normal_exit);
    /* Bootout alone only retires the leader's group. Escapes remain in the
     * original kernel coalition, even after reparenting to launchd. */
    for (int i = 0; i < 3; i++) {
        audit_token_t token;
        assert(!sosix_darwin_coalition_member_token(children[i], coalition, &token));
    }
    /* Choose the setpgid child: it has the SIGUSR1 fork handler. */
    for (int i = 0; i < 3; i++) if (getsid(children[i]) != children[i] &&
            getpgid(children[i]) == children[i])
        assert(!sosix_darwin_coalition_member_token(children[i], coalition, &race_token));
    SosixDarwinCoalitionRetirement receipt;
    assert(race_token.val[5] > 1);
    if (!watchdog_only) {
        assert(sosix_darwin_coalition_retire(coalition, 1, &receipt) == ETIMEDOUT);
        assert(!receipt.tasks_empty && !receipt.all_reaped && !receipt.signal_count);
        deadline_hook_armed = 1;
        assert(sosix_darwin_coalition_retire(coalition, 100000000, &receipt) == ETIMEDOUT);
        assert(deadline_hook_observed && !receipt.tasks_empty && !receipt.signal_count);
        race_report = report;
        assert(!sosix_darwin_coalition_retire(coalition, 3000000000LL, &receipt));
        assert(receipt.tasks_empty && !receipt.all_reaped && receipt.signal_count >= 4 && receipt.passes >= 2);
    }
    /* Prove reap separately for the known adversarial fixtures; do not
     * extrapolate this finite set to an unobserved production process tree. */
    int remaining = 3; unsigned reaped = 0;
    for (int attempt = 0; attempt < 30 && remaining; attempt++) {
        struct kevent events[8]; struct timespec wait = {0, 100000000};
        int count = kevent(queue, NULL, 0, events, 8, &wait); assert(count >= 0);
        if (watchdog_only) for (int j = 0; j < count; j++) if (events[j].fflags & NOTE_EXIT)
            assert(WIFSIGNALED(events[j].data) && WTERMSIG(events[j].data) == SIGALRM);
        for (int j = 0; j < count; j++) if (events[j].fflags & NOTE_REAP) {
            for (int i = 0; i < 3; i++) if (events[j].ident == (uintptr_t)children[i] && !(reaped & (1U << i))) {
                reaped |= 1U << i; remaining--;
            }
        }
    }
    assert(remaining == 0); close(queue);
    if (watchdog_only) {
        uint64_t started, exited;
        int e = 0;
        for (int attempt = 0; attempt < 100; attempt++) {
            e = sosix_darwin_coalition_counts(coalition, &started, &exited);
            if (e == ESRCH || (!e && started == exited)) break;
            assert(!e); pause_ms(10);
        }
        assert(e == ESRCH || (!e && started == exited));
        puts("watchdog_orphan_cleanup: confirmed");
        return;
    }
    for (int i = 0; i < 3; i++) {
        SosixDarwinProcessIdentity after;
        int e = sosix_darwin_coalition_identity(children[i], &after, 1);
        assert(e == ESRCH || (!e && after.unique_id != identities[i].unique_id));
    }
    assert(sosix_darwin_coalition_retire(current_coalition(), 1000000, &receipt) == EPERM);
    assert(sosix_darwin_coalition_retire(UINT64_MAX, 1000000, &receipt) == ESRCH);
    printf("coalition_%s: escaped_members_killed_and_fixture_reap_observed\n",
        normal_exit ? "leader_exit" : "leader_kill");
    puts("audit_token_stale_signal: rejected");
    puts("post_census_fork: retired_on_later_pass");
    puts("expired_deadline: rejected_before_signalling");
    puts("census_deadline: enforced_before_signalling");
    puts("self_coalition_retirement: rejected");
    puts("unknown_coalition_retirement: rejected");
    puts("generic_reap_capability: not_claimed");
    puts("zombie_accounting_is_not_reap: verified");
}

int main(int argc, char **argv) {
    if (argc == 3 && !strcmp(argv[1], "worker")) {
        if (!strcmp(argv[2], "watchdog")) worker_watchdog = 1;
        worker(!strcmp(argv[2], "exit"));
    }
    else if (argc == 5 && !strcmp(argv[1], "controller"))
        controller(argv[2], argv[3], !strcmp(argv[4], "exit"), !strcmp(argv[4], "watchdog"));
    else return 64;
    return 0;
}
#endif
