#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define DEFAULT_PORT UINT64_C(8080)
#define REQUIRED_MASK UINT64_C(0x7ff)

static uint64_t selected_port = DEFAULT_PORT;
static uint64_t coverage_mask;

static void coverage_hit(unsigned bit) {
    coverage_mask |= UINT64_C(1) << bit;
}

static uint64_t select_addr(const char *addr) {
    size_t i = strlen(addr);
    uint64_t multiplier = UINT64_C(1);
    uint64_t parsed = UINT64_C(0);
    int saw_digit = 0;

    selected_port = DEFAULT_PORT;
    if (i == 0U) {
        coverage_hit(0);
        return selected_port;
    }
    while (i > 0U) {
        unsigned char ch = (unsigned char)addr[i - 1U];
        if (ch >= (unsigned char)'0' && ch <= (unsigned char)'9') {
            coverage_hit(2);
            parsed += (uint64_t)(ch - (unsigned char)'0') * multiplier;
            multiplier *= UINT64_C(10);
            saw_digit = 1;
            i--;
            continue;
        }
        if (ch == (unsigned char)':' && saw_digit) {
            coverage_hit(3);
            if (parsed > UINT64_C(0) && parsed <= UINT64_C(65535)) {
                coverage_hit(4);
                selected_port = parsed;
            } else {
                coverage_hit(5);
            }
            return selected_port;
        }
        if (saw_digit) {
            coverage_hit(6);
            return selected_port;
        }
        coverage_hit(1);
        i--;
    }
    coverage_hit(saw_digit ? 7U : 8U);
    return selected_port;
}

static uint64_t select_explicit(int64_t port) {
    if (port > 0 && port <= 65535) {
        coverage_hit(9);
        selected_port = (uint64_t)port;
    } else {
        coverage_hit(10);
    }
    return selected_port;
}

static void emit_addr(const char *case_id, const char *addr) {
    printf("%s port=%llu\n", case_id,
           (unsigned long long)select_addr(addr));
}

static void emit_explicit(const char *case_id, int64_t port) {
    printf("%s port=%llu\n", case_id,
           (unsigned long long)select_explicit(port));
}

int main(void) {
    emit_addr("empty", "");
    emit_addr("no-digits", "localhost");
    emit_addr("valid", "0.0.0.0:2222");
    emit_addr("trailing-junk", "host:123tail");
    emit_addr("interrupted", "host:12x34");
    emit_addr("zero", "host:0");
    emit_addr("too-large", "host:65536");
    emit_addr("digits-only", "1234");
    emit_explicit("explicit-valid", 9090);
    emit_explicit("explicit-invalid-retains", 0);
    printf("coverage mask=%llu required=%llu\n",
           (unsigned long long)coverage_mask,
           (unsigned long long)REQUIRED_MASK);
    return 0;
}
