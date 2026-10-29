/* Bounded native workloads for the real Linux cgroup owner probe. */
#define _GNU_SOURCE
#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

int main(void) {
    char mode[32] = {0};
    FILE *input = fopen("mode", "r"); assert(input);
    assert(fgets(mode, sizeof(mode), input)); fclose(input);
    if (!strcmp(mode, "orphan\n")) {
        int ready[2]; assert(pipe(ready) == 0);
        pid_t child = fork(); assert(child >= 0);
        if (!child) {
            close(ready[0]);
            assert(setsid() == getpid());
            FILE *marker = fopen("descendant.tmp", "wx"); assert(marker);
            fprintf(marker, "%ld %ld\n", (long)getpid(), (long)getsid(0));
            assert(fclose(marker) == 0);
            assert(rename("descendant.tmp", "descendant") == 0);
            assert(write(ready[1], "1", 1) == 1); close(ready[1]);
            sleep(30); /* Safety bound if the owner fails to retire us. */
            _exit(91);
        }
        close(ready[1]);
        char byte; assert(read(ready[0], &byte, 1) == 1);
        close(ready[0]);
        return 0;
    }
    assert(!strcmp(mode, "memory\n"));
    FILE *marker = fopen("allocation-started", "wx"); assert(marker);
    assert(fclose(marker) == 0);
    size_t bytes = 128 * 1024 * 1024;
    volatile unsigned char *pages = mmap(NULL, bytes, PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(pages != MAP_FAILED);
    for (size_t i = 0; i < bytes; i += 4096) pages[i] = 1;
    /* Reaching this is a failed enforcement test, never an expected exit. */
    return 92;
}
