/* Native component test. Does not qualify the sealed-image V4 contract. */
#define _DARWIN_C_SOURCE
#include <sys/types.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <limits.h>
static int injected_turn;
static ssize_t injected_read(int fd, void *bytes, size_t count) {
    if (fd != INT_MAX) return read(fd, bytes, count);
    if (injected_turn++ == 0) { errno = EINTR; return -1; }
    if (injected_turn == 2) count = 1;
    memset(bytes, 'x', count); return (ssize_t)count;
}
#define SOSIX_DARWIN_PROCESS_READ injected_read
#include "../runtime_sosix_darwin_process_private.h"
#include <assert.h>
#include <stdio.h>

static SosixDarwinProcess *active_owner;
static void emergency_cleanup(int signal_number) {
    (void)signal_number;
    if (active_owner && active_owner->generation && !active_owner->reaped)
        (void)kill(-active_owner->pid, SIGKILL);
    _exit(1);
}

int main(int argc, char **argv) {
    if (argc > 1) {
        if (!strcmp(argv[1], "capture")) {
            char cwd[PATH_MAX]; assert(getcwd(cwd, sizeof(cwd)));
            printf("%s|%s|%s", argv[2], getenv("CAPTURE_ENV"), cwd);
            fprintf(stderr, "diagnostic"); return 17;
        }
        if (!strcmp(argv[1], "timeout")) {
            signal(SIGTERM, SIG_IGN);
            for (;;) pause();
        }
        if (!strcmp(argv[1], "descendant")) {
            pid_t child = fork(); assert(child >= 0);
            if (!child) { signal(SIGTERM, SIG_IGN); for (;;) pause(); }
            printf("%d", child); fflush(stdout); return 0;
        }
        if (!strcmp(argv[1], "overflow")) {
            for (int i = 0; i < 10000; i++) putchar('x');
            return 0;
        }
        return 127;
    }
    signal(SIGALRM, emergency_cleanup); signal(SIGABRT, emergency_cleanup);
    signal(SIGTERM, emergency_cleanup); alarm(15);
    int injected_fd = INT_MAX, injected_error = 0;
    unsigned char discard[1]; size_t retained = 0; uint64_t seen = 0;
    sosix_darwin_process_drain(&injected_fd, discard, 0, &retained, &seen, &injected_error);
    assert(injected_turn < 20 && seen == 65535 && retained == 0 && !injected_error);
    int source = open(argv[0], O_RDONLY | O_CLOEXEC); assert(source >= 0);
    SosixDarwinImage image; assert(!sosix_darwin_image_create(source, &image)); close(source);
    int cwd = open("/private/tmp", O_RDONLY | O_DIRECTORY | O_CLOEXEC); assert(cwd >= 0);
    char *env[] = {"CAPTURE_ENV=exact", NULL};
    const char *modes[] = {"capture", "timeout", "descendant", "overflow", "exit127", "timeout"};
    for (unsigned i = 0; i < sizeof(modes)/sizeof(modes[0]); i++) {
        char *args[] = {"owned-image", (char*)modes[i], "two words", NULL};
        SosixDarwinProcess owner;
        SosixDarwinProcessLimits limits = {1000000000LL, 20000000LL, 2000000000LL, 128, 128};
        if (i == 1) limits.wall_ns = 30000000LL;
        assert(!sosix_darwin_process_start(&owner, &image, image.generation, cwd, args, env, limits));
        active_owner = &owner;
        uint64_t generation = owner.generation;
        assert(sosix_darwin_process_ack(&owner, generation) == EBUSY);
        if (i == 5) assert(!sosix_darwin_process_cancel(&owner, generation));
        int turns = 0;
        while (!owner.frozen && turns++ < 400) {
            int error = sosix_darwin_process_poll(&owner, generation, 10000000LL);
            if (error) {
                size_t live = 0; int sample = sosix_darwin_process_group_live(owner.pid, &live);
                int signal_zero = kill(-owner.pid, 0), signal_error = errno;
                fprintf(stderr, "mode=%s pid=%d poll error=%d (%s), pgid=%d, sample=%d/live=%zu signal0=%d/errno=%d exited=%d reaped=%d term=%d kill=%d\n",
                    modes[i], owner.pid, error, strerror(error), getpgid(owner.pid), sample, live, signal_zero, signal_error,
                    owner.leader_exited, owner.reaped, owner.term_sent, owner.kill_sent);
            }
            assert(!error);
        }
        assert(owner.frozen && owner.reaped && owner.group_retired);
        if (i == 0) {
            assert(WIFEXITED(owner.wait_status) && WEXITSTATUS(owner.wait_status) == 17);
            assert(owner.stdout_kept == strlen("two words|exact|/private/tmp"));
            assert(!memcmp(owner.stdout_bytes, "two words|exact|/private/tmp", owner.stdout_kept));
            assert(owner.stderr_kept == strlen("diagnostic"));
            assert(!memcmp(owner.stderr_bytes, "diagnostic", owner.stderr_kept));
        } else if (i == 1) {
            assert(owner.timed_out && owner.term_sent && owner.kill_sent);
            assert(WIFSIGNALED(owner.wait_status) && WTERMSIG(owner.wait_status) == SIGKILL);
        } else if (i == 2) {
            assert(owner.kill_sent && WIFEXITED(owner.wait_status));
        } else if (i == 3) {
            assert(owner.stdout_seen == 10000 && owner.stdout_kept == 128);
        } else if (i == 4) assert(WIFEXITED(owner.wait_status) && WEXITSTATUS(owner.wait_status) == 127);
        else assert(owner.cancel_requested && !owner.timed_out && owner.term_sent);
        assert(sosix_darwin_process_ack(&owner, generation ^ 1) == ESTALE);
        assert(owner.generation == generation);
        assert(!sosix_darwin_process_ack(&owner, generation));
        assert(sosix_darwin_process_poll(&owner, generation, 0) == ESTALE);
        assert(sosix_darwin_process_ack(&owner, generation) == ESTALE);
        active_owner = NULL;
    }
    close(cwd); assert(!sosix_darwin_image_close(&image, image.generation));
    puts("Darwin owned process snapshot component: PASS (not sealed V4)");
    return 0;
}
