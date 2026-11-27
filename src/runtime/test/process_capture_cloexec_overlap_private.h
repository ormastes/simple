/* Deterministic writer-overlap ATTEMPT: A pauses with open writers in atfork
 * prepare. B must fail before fork within the bounded setup transaction, then
 * succeed after A's parent closes its writers. A is held until B is live;
 * A must then finish/EOF while B waits preexec, runs after exec, or remains a
 * long-lived raw child retaining its historical unrelated-FD semantics. */
#include <sys/socket.h>

struct CaptureOverlapV1 {
    const char* executable;
    int trigger[2];
    int release[2];
    int a_control[2];
    int unrelated_fd;
    int exec_holder;
    pthread_mutex_t lock;
    pthread_cond_t changed;
    int a_done;
    int a_setup_ready;
    int b_rejected_overlap;
    int a_failed;
    int b_failed;
    int b_alive_after_a;
};
static _Thread_local struct CaptureOverlapV1* overlap_prepare_v1;

static void overlap_atfork_prepare_v1(void) {
    struct CaptureOverlapV1* test = overlap_prepare_v1;
    if (!test) return;
    const char opened = 'P'; char released = 0;
    assert(write(test->trigger[1], &opened, 1) == 1);
    assert(read(test->release[0], &released, 1) == 1 && released == 'B');
}

static void* overlap_a_v1(void* opaque) {
    struct CaptureOverlapV1* test = (struct CaptureOverlapV1*)opaque;
    assert(socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, test->a_control) == 0);
    overlap_prepare_v1 = test;
    int64_t pid = simple_fork_child_setup_capture_v1(0, test->a_control[1]);
    overlap_prepare_v1 = NULL;
    if (pid == 0) {
        char go = 0; if (read(3, &go, 1) != 1 || go != 'A') rt_fork_child_exit(95);
        const char output[] = "short-owner-eof";
        (void)write(STDOUT_FILENO, output, sizeof(output) - 1);
        rt_fork_child_exit(19);
    }
    assert(pid > 0); close(test->a_control[1]);
    assert(pthread_mutex_lock(&test->lock) == 0);
    test->a_setup_ready = 1; assert(pthread_cond_broadcast(&test->changed) == 0);
    assert(pthread_mutex_unlock(&test->lock) == 0);
    int64_t result = rt_fork_parent_wait_bounded(pid, 1000, 128);
    if (result != 19 || strcmp(rt_fork_parent_stdout(), "short-owner-eof") ||
            simple_fork_parent_capture_flags_v1() != 0) test->a_failed = 1;
    close(test->a_control[0]); simple_fork_parent_capture_release_v1();
    assert(pthread_mutex_lock(&test->lock) == 0);
    test->a_done = 1; assert(pthread_cond_signal(&test->changed) == 0);
    assert(pthread_mutex_unlock(&test->lock) == 0);
    return NULL;
}

static void* overlap_b_v1(void* opaque) {
    struct CaptureOverlapV1* test = (struct CaptureOverlapV1*)opaque;
    char opened = 0; assert(read(test->trigger[0], &opened, 1) == 1 && opened == 'P');
    int64_t rejected = rt_fork_child_setup();
    if (rejected == 0) rt_fork_child_exit(94);
    test->b_rejected_overlap = rejected == -1;
    if (rejected > 0) (void)rt_fork_parent_wait_bounded(rejected, 1000, 128);
    const char released = 'B'; assert(write(test->release[1], &released, 1) == 1);
    assert(pthread_mutex_lock(&test->lock) == 0);
    struct timespec ready_limit; assert(clock_gettime(CLOCK_REALTIME, &ready_limit) == 0); ready_limit.tv_sec += 5;
    while (!test->a_setup_ready) assert(pthread_cond_timedwait(&test->changed, &test->lock, &ready_limit) == 0);
    assert(pthread_mutex_unlock(&test->lock) == 0);
    int control[2]; assert(socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, control) == 0);
    int64_t pid = test->exec_holder == 2 ? rt_fork_child_setup() :
        simple_fork_child_setup_capture_v1(now_ms() + 5000, control[1]);
    if (pid == 0) {
        int private_fd = test->exec_holder == 2 ? control[1] : 3;
        /* This witness runs AFTER the production captured-child whitelist. */
        if (test->exec_holder == 2) {
            if (fcntl(test->unrelated_fd, F_GETFD) < 0) rt_fork_child_exit(93);
            close(control[0]);
        } else if (fcntl(test->unrelated_fd, F_GETFD) != -1 || errno != EBADF ||
                (fcntl(3, F_GETFD) & FD_CLOEXEC) == 0) rt_fork_child_exit(97);
        if (test->exec_holder == 1) {
            char* const child_args[] = {(char*)test->executable, (char*)"--exec-holder", (char*)"", NULL};
            execv(test->executable, child_args); rt_fork_child_exit(98);
        }
        const char ready = 'R'; char released = 0;
        (void)write(private_fd, &ready, 1);
        if (read(private_fd, &released, 1) != 1 || released != 'G') rt_fork_child_exit(96);
        const char* output = test->exec_holder == 2 ? "raw-holder" : "preexec-holder";
        (void)write(STDOUT_FILENO, output, strlen(output)); rt_fork_child_exit(29);
    }
    assert(pid > 0); close(control[1]);
    char ready = 0;
    ssize_t witnessed = read(control[0], &ready, 1);
    if (test->exec_holder == 1 ? witnessed != 0 : (witnessed != 1 || ready != 'R')) test->b_failed = 1;
    const char start_a = 'A'; assert(write(test->a_control[0], &start_a, 1) == 1);
    assert(pthread_mutex_lock(&test->lock) == 0);
    struct timespec limit; assert(clock_gettime(CLOCK_REALTIME, &limit) == 0); limit.tv_sec += 5;
    while (!test->a_done) assert(pthread_cond_timedwait(&test->changed, &test->lock, &limit) == 0);
    assert(pthread_mutex_unlock(&test->lock) == 0);
    int status = 0;
    test->b_alive_after_a = waitpid((pid_t)pid, &status, WNOHANG) == 0;
    if (test->exec_holder != 1) { const char go = 'G'; assert(write(control[0], &go, 1) == 1); }
    close(control[0]);
    int64_t result = rt_fork_parent_wait_bounded(pid, 5000, 128);
    const char* expected = test->exec_holder == 1 ? "exec-holder" : test->exec_holder == 2 ? "raw-holder" : "preexec-holder";
    if (result != 29 || strcmp(rt_fork_parent_stdout(), expected) ||
            simple_fork_parent_capture_flags_v1() != 0) test->b_failed = 2;
    simple_fork_parent_capture_release_v1(); return NULL;
}

static void forced_descriptor_overlap_v1(const char* executable, int exec_holder) {
    struct CaptureOverlapV1 test = {.executable = executable, .exec_holder = exec_holder,
        .lock = PTHREAD_MUTEX_INITIALIZER, .changed = PTHREAD_COND_INITIALIZER};
    CHECK(simple_fork_capture_pipe_v1(test.trigger) == 0);
    CHECK(simple_fork_capture_pipe_v1(test.release) == 0);
    test.unrelated_fd = fcntl(test.trigger[0], F_DUPFD_CLOEXEC, 128); CHECK(test.unrelated_fd >= 128);
    pthread_t threads[2];
    CHECK(pthread_create(&threads[0], NULL, overlap_a_v1, &test) == 0);
    CHECK(pthread_create(&threads[1], NULL, overlap_b_v1, &test) == 0);
    CHECK(pthread_join(threads[0], NULL) == 0); CHECK(pthread_join(threads[1], NULL) == 0);
    CHECK(test.a_failed == 0); CHECK(test.b_failed == 0); CHECK(test.b_alive_after_a == 1);
    CHECK(test.b_rejected_overlap == 1);
    close(test.trigger[0]); close(test.trigger[1]); close(test.release[0]); close(test.release[1]); close(test.unrelated_fd);
    CHECK(pthread_cond_destroy(&test.changed) == 0); CHECK(pthread_mutex_destroy(&test.lock) == 0);
}
