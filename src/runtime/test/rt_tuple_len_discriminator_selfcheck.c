/* Verify rt_tuple_len acts as a quiet runtime-tuple discriminator:
 *   1. Returns arity (2) on a real rt_tuple_new(2).
 *   2. Returns -1 on a raw malloc'd 2-word language-tuple struct pointer
 *      with ZERO stderr diagnostic spam.
 *   3. Returns -1 on a registered RtCoreString handle with ZERO stderr spam.
 *   4. Leaves rt_core_invalid_array_reported armed so a subsequent invalid
 *      rt_array_len call still emits its one-shot diagnostic.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern int64_t rt_tuple_new(int64_t len);
extern int64_t rt_tuple_len(int64_t tuple);
extern int64_t rt_string_new(const char* data, uint64_t len);
extern int64_t rt_array_len(void* array);

int main(void) {
    int pipefd[2];
    if (pipe(pipefd) != 0) return 2;
    int saved_stderr = dup(STDERR_FILENO);
    if (saved_stderr < 0) return 2;
    if (dup2(pipefd[1], STDERR_FILENO) < 0) return 2;

    int64_t real_tuple = rt_tuple_new(2);
    if (rt_tuple_len(real_tuple) != 2) {
        dup2(saved_stderr, STDERR_FILENO);
        fprintf(stderr, "FAIL: expected rt_tuple_len(rt_tuple_new(2)) == 2\n");
        return 1;
    }

    int64_t* lang_pair = (int64_t*)calloc(2, sizeof(int64_t));
    if (!lang_pair) return 2;
    lang_pair[0] = rt_string_new("K", 1);
    lang_pair[1] = rt_string_new("V", 1);
    if (rt_tuple_len((int64_t)(uintptr_t)lang_pair) != -1) {
        dup2(saved_stderr, STDERR_FILENO);
        fprintf(stderr, "FAIL: expected rt_tuple_len(lang_pair) == -1\n");
        return 1;
    }
    if (rt_tuple_len(lang_pair[0]) != -1) {
        dup2(saved_stderr, STDERR_FILENO);
        fprintf(stderr, "FAIL: expected rt_tuple_len(string_handle) == -1\n");
        return 1;
    }

    fflush(stderr);
    dup2(saved_stderr, STDERR_FILENO);
    close(saved_stderr);
    close(pipefd[1]);
    char buf[512];
    ssize_t n = read(pipefd[0], buf, sizeof(buf) - 1);
    close(pipefd[0]);
    if (n != 0) {
        if (n > 0) buf[n] = '\0';
        fprintf(stderr, "FAIL: unexpected stderr from rt_tuple_len: %s\n", n > 0 ? buf : "<err>");
        return 1;
    }

    /* Verify one-shot invalid-array diagnostic remains armed for real rt_array_len misuse. */
    if (pipe(pipefd) != 0) return 2;
    saved_stderr = dup(STDERR_FILENO);
    if (saved_stderr < 0) return 2;
    if (dup2(pipefd[1], STDERR_FILENO) < 0) return 2;
    (void)rt_array_len((void*)lang_pair);
    fflush(stderr);
    dup2(saved_stderr, STDERR_FILENO);
    close(saved_stderr);
    close(pipefd[1]);
    n = read(pipefd[0], buf, sizeof(buf) - 1);
    close(pipefd[0]);
    free(lang_pair);
    if (n <= 0 || (buf[n] = '\0', strstr(buf, "rejected invalid array handle") == NULL)) {
        fprintf(stderr, "FAIL: one-shot invalid array diagnostic was not preserved\n");
        return 1;
    }

    puts("PASS: rt_tuple_len quietly discriminates runtime tuples without disarming array guard");
    return 0;
}
