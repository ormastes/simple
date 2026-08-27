#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct uart_plan {
    int status;
    uint64_t divisor;
    uint8_t dll;
    uint8_t dlh;
};

static struct uart_plan uart_plan(uint64_t clock_hz, uint64_t baud) {
    if (clock_hz == 0) return (struct uart_plan){1, 0, 0, 0};
    if (baud == 0) return (struct uart_plan){2, 0, 0, 0};
    const uint64_t clock_per_sample = clock_hz / 16;
    if (baud > clock_per_sample) return (struct uart_plan){3, 0, 0, 0};
    const uint64_t divisor = clock_per_sample / baud;
    if (divisor > 65535) return (struct uart_plan){4, 0, 0, 0};
    return (struct uart_plan){
        0, divisor, (uint8_t)(divisor & 0xff), (uint8_t)((divisor >> 8) & 0xff)
    };
}

static int run_vectors(const char *path) {
    FILE *input = fopen(path, "r");
    if (input == NULL) return 2;
    char line[256];
    int rows = 0;
    while (fgets(line, sizeof line, input) != NULL) {
        if (strncmp(line, "    ", 4) != 0) continue;
        char name[64];
        uint64_t clock_hz;
        uint64_t baud;
        int expected_status;
        uint64_t expected_divisor;
        unsigned expected_dll;
        unsigned expected_dlh;
        int expected_writes;
        if (sscanf(line, " %63[^,], %" SCNu64 ", %" SCNu64 ", %d, %" SCNu64
                         ", %u, %u, %d",
                   name, &clock_hz, &baud, &expected_status, &expected_divisor,
                   &expected_dll, &expected_dlh, &expected_writes) != 8) {
            fclose(input);
            return 3;
        }
        const struct uart_plan plan = uart_plan(clock_hz, baud);
        const int writes = plan.status == 0 ? 7 : 0;
        if (plan.status != expected_status || plan.divisor != expected_divisor ||
            plan.dll != expected_dll || plan.dlh != expected_dlh ||
            writes != expected_writes) {
            fclose(input);
            return 4;
        }
        printf("%s,%d,%" PRIu64 ",%u,%u\n",
               name, plan.status, plan.divisor, plan.dll, plan.dlh);
        rows++;
    }
    fclose(input);
    return rows == 8 ? 0 : 5;
}

static int run_bench(uint64_t iterations) {
    uint64_t checksum = 0;
    for (uint64_t i = 0; i < iterations; ++i) {
        const uint64_t baud = (i & 15) == 0 ? 0 : 2 + (i % 115199);
        const struct uart_plan plan = uart_plan(1843200, baud);
        checksum += plan.divisor + (uint64_t)plan.status;
    }
    printf("checksum=%" PRIu64 "\n", checksum);
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp(argv[1], "--bench") == 0) {
        return run_bench(strtoull(argv[2], NULL, 10));
    }
    if (argc != 2) return 64;
    return run_vectors(argv[1]);
}
