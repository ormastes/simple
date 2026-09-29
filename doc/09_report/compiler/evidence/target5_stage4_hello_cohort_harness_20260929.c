#define _GNU_SOURCE
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

struct sample { double ms; long rss_kib; };

static double elapsed_ms(struct timespec a, struct timespec b) {
    return (double)(b.tv_sec - a.tv_sec) * 1000.0 +
           (double)(b.tv_nsec - a.tv_nsec) / 1000000.0;
}

static struct sample run(const char *binary, int python) {
    struct timespec start, end;
    struct rusage usage;
    int status = 0;
    clock_gettime(CLOCK_MONOTONIC, &start);
    pid_t child = fork();
    if (child < 0) { perror("fork"); exit(2); }
    if (child == 0) {
        int null_fd = open("/dev/null", O_WRONLY);
        if (null_fd < 0) _exit(125);
        dup2(null_fd, STDOUT_FILENO);
        dup2(null_fd, STDERR_FILENO);
        close(null_fd);
        if (python) execl(binary, binary, "-c", "print('Hello World')", (char *)0);
        else execl(binary, binary, (char *)0);
        _exit(126);
    }
    if (wait4(child, &status, 0, &usage) != child) { perror("wait4"); exit(2); }
    clock_gettime(CLOCK_MONOTONIC, &end);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        fprintf(stderr, "child failed: %s status=%d\n", binary, status);
        exit(2);
    }
    return (struct sample){elapsed_ms(start, end), usage.ru_maxrss};
}

static int cmp_double(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}
static int cmp_long(const void *a, const void *b) {
    long x = *(const long *)a, y = *(const long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: cohort SIMPLE PYTHON OUTPUT\n");
        return 2;
    }
    FILE *out = fopen(argv[3], "w");
    if (!out) { perror("fopen"); return 2; }
    run(argv[1], 0);
    run(argv[2], 1);
    double times[2][30];
    long rss[2][30];
    for (int pair = 0; pair < 30; pair++) {
        for (int position = 0; position < 2; position++) {
            int lane = (pair + position) % 2;
            struct sample s = run(argv[lane + 1], lane == 1);
            times[lane][pair] = s.ms;
            rss[lane][pair] = s.rss_kib;
            fprintf(out, "sample|%s|%d|%.6f|%ld\n",
                    lane == 0 ? "simple" : "python", pair, s.ms, s.rss_kib);
        }
    }
    fclose(out);
    for (int lane = 0; lane < 2; lane++) {
        qsort(times[lane], 30, sizeof(double), cmp_double);
        qsort(rss[lane], 30, sizeof(long), cmp_long);
        printf("%s time_p95_ms=%.6f rss_p95_kib=%ld\n",
               lane == 0 ? "simple" : "python", times[lane][28], rss[lane][28]);
    }
    printf("normalized_sum=%.6f\n",
           times[0][28] / times[1][28] +
           (double)rss[0][28] / (double)rss[1][28]);
    return 0;
}
