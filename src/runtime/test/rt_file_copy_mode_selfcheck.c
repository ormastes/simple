#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

int rt_file_copy(const uint8_t *, uint64_t, const uint8_t *, uint64_t);
int64_t rt_file_publish_noreplace(const uint8_t *, uint64_t,
                                const uint8_t *, uint64_t);

static int copy(const char *source, const char *destination) {
    return rt_file_copy((const uint8_t *)source, strlen(source),
                        (const uint8_t *)destination, strlen(destination));
}

static void expect_mode(const char *path, mode_t expected) {
    struct stat st;
    assert(stat(path, &st) == 0);
    if ((st.st_mode & 0777) != expected) {
        fprintf(stderr, "copied mode %03o, expected %03o\n",
                (unsigned)(st.st_mode & 0777), (unsigned)expected);
        exit(1);
    }
}

int main(int argc, char **argv) {
    assert(argc == 2);
    assert(chdir(argv[1]) == 0);
    const char *source = "compiler-output";
    const char *stage = "staged-output";
    const char *published = "hello.exe";
    FILE *file = fopen(source, "wb");
    assert(file);
    assert(fputs("#!/bin/sh\nexit 37\n", file) >= 0);
    assert(fclose(file) == 0);
    assert(chmod(source, 0751) == 0);

    /* BuildRunner copies into a private staging directory before publishing.
     * A restrictive manager umask must not strip the compiler's execute bits. */
    mode_t previous = umask(0077);
    assert(copy(source, stage) == 1);
    umask(previous);
    expect_mode(stage, 0751);
    assert(rt_file_publish_noreplace((const uint8_t *)stage, strlen(stage),
             (const uint8_t *)published, strlen(published)) == 1);
    expect_mode(published, 0751);
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        execl("./hello.exe", "hello.exe", (char *)NULL);
        _exit(127);
    }
    int status = 0;
    assert(waitpid(child, &status, 0) == child);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 37);

    /* Replacing an executable with an object/data file must clear execute. */
    assert(chmod(source, 0640) == 0);
    assert(copy(source, published) == 1);
    expect_mode(published, 0640);
    assert(copy("missing", stage) == 0);
    assert(copy(source, "missing-parent/output") == 0);
    assert(unlink(source) == 0);
    assert(unlink(published) == 0);
    puts("rt_file_copy_mode_selfcheck: PASS (copy, publish, execute, data mode)");
    return 0;
}
