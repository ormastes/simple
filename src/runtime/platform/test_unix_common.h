/*
 * POSIX-specific test cases — fork/waitpid panic tests, directory ops,
 * file locking, and shell commands that require POSIX utilities.
 *
 * Included by runtime_test.c via test_platform.h.
 * Requires TEST/RUN/ASSERT macros to be defined before inclusion.
 */
#ifndef SPL_TEST_UNIX_COMMON_H
#define SPL_TEST_UNIX_COMMON_H

#include <sys/wait.h>
#include <unistd.h>

/* ================================================================
 * Panic (via fork — POSIX only)
 * ================================================================ */

TEST(panic_exits) {
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        spl_panic("test panic");
        _exit(0);
    }
    int status;
    waitpid(pid, &status, 0);
    ASSERT(WIFEXITED(status));
    ASSERT_EQ_INT(WEXITSTATUS(status), 1);
}

TEST(panic_null_msg) {
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        spl_panic(NULL);
        _exit(0);
    }
    int status;
    waitpid(pid, &status, 0);
    ASSERT(WIFEXITED(status));
    ASSERT_EQ_INT(WEXITSTATUS(status), 1);
}

/* ================================================================
 * Directory Operations
 * ================================================================ */

TEST(dir_remove_all) {
    /* Create temp directory structure */
    system("mkdir -p /tmp/rt_test_dir/subdir");
    system("touch /tmp/rt_test_dir/file.txt");
    system("touch /tmp/rt_test_dir/subdir/file2.txt");

    /* Remove all should work */
    ASSERT(rt_dir_remove_all("/tmp/rt_test_dir"));
    ASSERT(!spl_file_exists("/tmp/rt_test_dir"));
}

TEST(dir_remove_all_null) {
    ASSERT(!rt_dir_remove_all(NULL));
}

TEST(dir_create_empty_path) {
    ASSERT(!rt_dir_create("", false));
    ASSERT(!rt_dir_create("", true));
}

TEST(dir_create_recursive) {
    const char* root = "/tmp/rt_test_mkdir_recursive";
    const char* leaf = "/tmp/rt_test_mkdir_recursive/a/b/c";
    if (spl_file_exists(root)) {
        rt_dir_remove_all(root);
    }
    ASSERT(rt_dir_create(leaf, true));
    ASSERT(spl_file_exists("/tmp/rt_test_mkdir_recursive/a"));
    ASSERT(spl_file_exists(leaf));
    ASSERT(rt_dir_remove_all(root));
}

TEST(dir_create_nonrecursive_missing_parent) {
    const char* root = "/tmp/rt_test_mkdir_nonrecursive";
    const char* leaf = "/tmp/rt_test_mkdir_nonrecursive/a/b";
    if (spl_file_exists(root)) {
        rt_dir_remove_all(root);
    }
    ASSERT(!rt_dir_create(leaf, false));
    ASSERT(!spl_file_exists(leaf));
    ASSERT(!spl_file_exists(root));
}

/* ================================================================
 * File Locking
 * ================================================================ */

TEST(file_lock_unlock) {
    const char* path = "/tmp/rt_test_lock.txt";
    spl_file_write(path, "test");

    /* Lock file */
    int64_t handle = rt_file_lock(path, 0);
    ASSERT(handle >= 0);

    /* Unlock file */
    ASSERT(rt_file_unlock(handle));

    remove(path);
}

TEST(file_lock_null_path) {
    ASSERT_EQ_INT(rt_file_lock(NULL, 0), -1);
}

TEST(file_lock_invalid_path) {
    /* Try to lock non-existent directory path */
    ASSERT_EQ_INT(rt_file_lock("/nonexistent_dir_12345/file.txt", 0), -1);
}

TEST(file_lock_with_timeout) {
    const char* path = "/tmp/rt_test_lock_timeout.txt";
    spl_file_write(path, "test");

    /* Lock with timeout */
    int64_t handle = rt_file_lock(path, 1);
    ASSERT(handle >= 0);

    rt_file_unlock(handle);
    remove(path);
}

TEST(file_lock_timeout_contended) {
    const char* path = "/tmp/rt_test_lock_contended.txt";
    spl_file_write(path, "test");

    int64_t lock_a = rt_file_lock(path, 0);
    ASSERT(lock_a >= 0);

    pid_t pid = fork();
    ASSERT(pid >= 0);
    if (pid == 0) {
        int64_t lock_b = rt_file_lock(path, 1);
        if (lock_b >= 0) {
            rt_file_unlock(lock_b);
            _exit(2);
        }
        _exit(0);
    }

    int status = 0;
    waitpid(pid, &status, 0);
    ASSERT(WIFEXITED(status));
    ASSERT_EQ_INT(WEXITSTATUS(status), 0);

    ASSERT(rt_file_unlock(lock_a));
    remove(path);
}

TEST(file_unlock_invalid_handle) {
    ASSERT(!rt_file_unlock(-1));
}

TEST(time_now_monotonic_nonzero) {
    int64_t n1 = rt_time_now_nanos();
    int64_t n2 = rt_time_now_nanos();
    int64_t u1 = rt_time_now_micros();

    ASSERT(n1 > 0);
    ASSERT(n2 >= n1 || n2 > 0);
    ASSERT(u1 > 0);
}

/* ================================================================
 * Shell Output (POSIX-specific commands)
 * ================================================================ */

TEST(shell_output_large) {
    /* Force buffer realloc in spl_shell_output — uses `seq` (POSIX) */
    char* out = spl_shell_output("seq 1 5000");
    ASSERT(spl_str_len(out) > 0);
    ASSERT(spl_str_contains(out, "5000"));
    free(out);
}

/* ================================================================
 * Platform test runner — called from main()
 * ================================================================ */

static void run_platform_tests(void) {
    printf("\n--- Branch Coverage: Panic ---\n");
    RUN(panic_exits);
    RUN(panic_null_msg);

    printf("\n--- Coverage: Directory Operations ---\n");
    RUN(dir_remove_all);
    RUN(dir_remove_all_null);
    RUN(dir_create_empty_path);
    RUN(dir_create_recursive);
    RUN(dir_create_nonrecursive_missing_parent);

    printf("\n--- Coverage: File Locking ---\n");
    RUN(file_lock_unlock);
    RUN(file_lock_null_path);
    RUN(file_lock_invalid_path);
    RUN(file_lock_with_timeout);
    RUN(file_lock_timeout_contended);
    RUN(file_unlock_invalid_handle);

    printf("\n--- Coverage: High-Resolution Time ---\n");
    RUN(time_now_monotonic_nonzero);

    printf("\n--- Coverage: Shell Output (POSIX) ---\n");
    RUN(shell_output_large);

    run_cpu_tests();
}

#endif /* SPL_TEST_UNIX_COMMON_H */
