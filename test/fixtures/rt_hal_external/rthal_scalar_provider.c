/* Test-only C comparator for the frozen rthal-scalar-v1 process protocol.
 * Pure Simple owns execution and effects, but this child independently derives
 * its result so a wrong Pure oracle is falsifiable.  For lane i in 0..3:
 *
 *   base = op[i] XOR rotl(input[(i+1)%4], 7+11*i)
 *          XOR (GOLDEN + FNV_PRIME*i)
 *   replay: base ^= rotl(pure_trace[(i+2)%4], 13+7*i) XOR EFFECT_DOMAIN
 *   outcome[i] = mix64(base)
 *   error[i] = 0
 *   query trace[i] = mix64(base XOR TRACE_DOMAIN)
 *   replay trace[i] = pure_trace[i]
 *
 * mix64 is the SplitMix64 finalizer.  All arithmetic is wrapping u64.  Query
 * mode never reads the parent's expected outcome/error/trace fields; replay
 * reads only trace as its effect-replay input and still ignores expected
 * outcome/error.  Work and storage are fixed O(1), with no heap allocation. */
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { EXPECTED_ARGC = 25 };

static const uint64_t GOLDEN = UINT64_C(0x9e3779b97f4a7c15);
static const uint64_t FNV_PRIME = UINT64_C(0x00000100000001b3);
static const uint64_t EFFECT_DOMAIN = UINT64_C(0xd1b54a32d192ed03);
static const uint64_t TRACE_DOMAIN = UINT64_C(0x94d049bb133111eb);

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

static uint64_t parse_word(const char *value) {
    return (uint64_t)strtoll(value, NULL, 10);
}

static uint64_t rotl64(uint64_t value, unsigned shift) {
    shift &= 63U;
    return (value << shift) | (value >> ((64U - shift) & 63U));
}

static uint64_t mix64(uint64_t value) {
    value ^= value >> 30U;
    value *= UINT64_C(0xbf58476d1ce4e5b9);
    value ^= value >> 27U;
    value *= UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31U);
}

static int print_word(uint64_t word) {
    if ((word & (UINT64_C(1) << 63U)) == 0)
        return printf(" %" PRIu64, word) >= 0;
    return printf(" -%" PRIu64, (~word) + UINT64_C(1)) >= 0;
}

int main(int argc, char **argv) {
    if (argc != EXPECTED_ARGC) return 64;
    if (strcmp(argv[1], "rthal-scalar-v1") != 0) return 65;
    if (strcmp(argv[2], "compare") != 0 && strcmp(argv[2], "replay") != 0) return 66;
    if (strcmp(argv[4], "0") != 0 && strcmp(argv[4], "1") != 0) return 67;
    for (int index = 3; index < EXPECTED_ARGC; ++index) {
        if (!valid_i64(argv[index])) return 68;
    }
    const int effect = argv[4][0] == '1';
    if ((!effect && strcmp(argv[2], "compare") != 0) ||
        (effect && strcmp(argv[2], "replay") != 0)) return 67;
    uint64_t operation[4], input[4], replay_trace[4];
    uint64_t outcome[4], trace[4];
    for (unsigned i = 0; i < 4U; ++i) {
        operation[i] = parse_word(argv[5 + i]);
        input[i] = parse_word(argv[9 + i]);
        replay_trace[i] = effect ? parse_word(argv[21 + i]) : 0;
    }
    for (unsigned i = 0; i < 4U; ++i) {
        uint64_t base = operation[i] ^ rotl64(input[(i + 1U) & 3U], 7U + 11U * i)
            ^ (GOLDEN + FNV_PRIME * i);
        if (effect)
            base ^= rotl64(replay_trace[(i + 2U) & 3U], 13U + 7U * i)
                ^ EFFECT_DOMAIN;
        outcome[i] = mix64(base);
        trace[i] = effect ? replay_trace[i] : mix64(base ^ TRACE_DOMAIN);
    }
    if (printf("RTHAL1") < 0) return 69;
    for (unsigned i = 0; i < 4U; ++i) if (!print_word(outcome[i])) return 69;
    for (unsigned i = 0; i < 4U; ++i) if (!print_word(0)) return 69;
    for (unsigned i = 0; i < 4U; ++i) if (!print_word(trace[i])) return 69;
    if (printf("\n") < 0) return 69;
    return 0;
}
