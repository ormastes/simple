/* Test-only C comparator for the frozen rthal-scalar-v1 process protocol.
 * Pure Simple owns execution and semantics; this child only validates the
 * scalar envelope and returns the already-observed receipt digests. */
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { EXPECTED_ARGC = 25 };

static int valid_i64(const char *value) {
    char *end = NULL;
    if (value == NULL || value[0] == '\0') return 0;
    size_t index = value[0] == '-' ? 1U : 0U;
    if (value[index] == '\0') return 0;
    for (; value[index] != '\0'; ++index) {
        if (value[index] < '0' || value[index] > '9') return 0;
    }
    errno = 0;
    (void)strtoll(value, &end, 10);
    return errno == 0 && end != value && *end == '\0';
}

int main(int argc, char **argv) {
    if (argc != EXPECTED_ARGC) return 64;
    if (strcmp(argv[1], "rthal-scalar-v1") != 0) return 65;
    if (strcmp(argv[2], "compare") != 0 && strcmp(argv[2], "replay") != 0) return 66;
    if (strcmp(argv[4], "0") != 0 && strcmp(argv[4], "1") != 0) return 67;
    for (int index = 3; index < EXPECTED_ARGC; ++index) {
        if (!valid_i64(argv[index])) return 68;
    }
    if (printf("RTHAL1 %s %s %s %s %s %s %s %s %s %s %s %s\n",
               argv[13], argv[14], argv[15], argv[16],
               argv[17], argv[18], argv[19], argv[20],
               argv[21], argv[22], argv[23], argv[24]) < 0) return 69;
    return 0;
}
