/* Independent native oracle for the Pure Simple environment wire contract. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

enum { HEADER = 32, RECORD = 96, FRAME = 128, MAX_FRAME = 1048576,
       MAX_RECORDS = 4096 };
static const uint64_t MAGIC = UINT64_C(827738437);

typedef struct {
    uint64_t count;
    uint64_t next;
    uint64_t invocation;
    int error;
} cursor_v1;

static uint64_t load64(const unsigned char *p) {
    uint64_t v = 0;
    for (unsigned i = 0; i < 8; ++i) v |= (uint64_t)p[i] << (i * 8);
    return v;
}

static void store64(unsigned char *p, uint64_t v) {
    for (unsigned i = 0; i < 8; ++i) p[i] = (unsigned char)(v >> (i * 8));
}

static cursor_v1 open_frame(const unsigned char *p, size_t n, uint64_t cap) {
    cursor_v1 c = {0, 0, 0, 0};
    if (n < HEADER || n > MAX_FRAME || cap == 0 || cap > MAX_RECORDS) {
        c.error = 1; return c;
    }
    c.count = load64(p + 24);
    if (load64(p) != MAGIC || load64(p + 8) != 1 || c.count > cap ||
        load64(p + 16) != n || n != HEADER + c.count * RECORD) c.error = 1;
    return c;
}

static int next_record(cursor_v1 *c, const unsigned char *p, size_t n) {
    size_t o = HEADER + (size_t)c->next * RECORD;
    if (c->error || c->next >= c->count || o + RECORD > n) return 0;
    uint64_t version = load64(p + o), invocation = load64(p + o + 8);
    uint64_t sequence = load64(p + o + 16), opcode = load64(p + o + 24);
    if (version != 1 || opcode > 23 || sequence != c->next || invocation == 0 ||
        (c->next && invocation != c->invocation)) { c->error = 1; return 0; }
    c->invocation = invocation;
    ++c->next;
    return 1;
}

static void valid_frame(unsigned char p[FRAME]) {
    memset(p, 0, FRAME);
    store64(p, MAGIC); store64(p + 8, 1); store64(p + 16, FRAME);
    store64(p + 24, 1); store64(p + 32, 1); store64(p + 40, 17);
    store64(p + 48, 0); store64(p + 56, 1); store64(p + 64, 21);
    store64(p + 88, 2); store64(p + 96, 8); store64(p + 104, 4);
    store64(p + 112, 4); store64(p + 120, 16);
}

int main(void) {
    unsigned char frame[FRAME]; valid_frame(frame);
    cursor_v1 c = open_frame(frame, sizeof frame, 1);
    assert(!c.error && next_record(&c, frame, sizeof frame));
    assert(c.next == 1 && !next_record(&c, frame, sizeof frame));

    unsigned char bad[FRAME]; memcpy(bad, frame, FRAME);
    store64(bad + 8, 2); assert(open_frame(bad, FRAME, 1).error);
    memcpy(bad, frame, FRAME); store64(bad + 56, 24);
    c = open_frame(bad, FRAME, 1); assert(!next_record(&c, bad, FRAME));
    memcpy(bad, frame, FRAME); store64(bad + 48, 1);
    c = open_frame(bad, FRAME, 1); assert(!next_record(&c, bad, FRAME));
    assert(open_frame(frame, FRAME - 1, 1).error);
    assert(open_frame(frame, FRAME, 0).error);

    const uint64_t iterations = UINT64_C(10000000);
    struct timespec a, b; clock_gettime(CLOCK_MONOTONIC, &a);
    uint64_t accepted = 0;
    for (uint64_t i = 0; i < iterations; ++i) {
        c = open_frame(frame, sizeof frame, 1);
        accepted += (uint64_t)next_record(&c, frame, sizeof frame);
    }
    clock_gettime(CLOCK_MONOTONIC, &b);
    struct rusage usage; getrusage(RUSAGE_SELF, &usage);
    double seconds = (double)(b.tv_sec - a.tv_sec) +
        (double)(b.tv_nsec - a.tv_nsec) / 1000000000.0;
    assert(accepted == iterations);
    printf("environment_wire_v1 iterations=%llu ns_per_record=%.2f maxrss_kib=%ld\n",
        (unsigned long long)iterations, seconds * 1e9 / (double)iterations,
        usage.ru_maxrss);
    return 0;
}
