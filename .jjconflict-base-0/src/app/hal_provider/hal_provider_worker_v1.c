/* Production C rt(hal) provider worker, ABI v1.
 *
 * Build this source with HAL_PROVIDER_KIND=1.  The worker is deliberately a
 * fixed-storage state machine: stdin/stdout are the only inherited channels,
 * every frame is newline terminated, and no heap API is used before or after
 * the session handshake.
 */
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>

#ifndef HAL_PROVIDER_KIND
#define HAL_PROVIDER_KIND 1
#endif

enum { HAL_FRAME_CAP_V1 = 512, HAL_REQUEST_FIELDS_V1 = 8,
       HAL_REQUEST_FIELDS_V2 = 11, HAL_REQUEST_BYTES_FIELDS_V2 = 19 };

typedef struct {
    uint64_t contract, operation, invocation, fixture;
    uint64_t input_offset, input_length, input_capacity, trace_capacity;
} HalRequestV1;

typedef struct {
    uint64_t contract, operation, invocation, fixture, captured_scalar;
    uint64_t result_capacity, trace_hi, trace_lo, trace_cursor;
    uint64_t trace_length, trace_capacity;
} HalRequestV2;

typedef struct {
    uint64_t contract, operation, invocation, fixture;
    uint64_t status, error_domain, error_code, error_detail;
    uint64_t payload_length, payload_capacity;
    int64_t word[4];
    uint64_t trace_hi, trace_lo, trace_cursor, trace_length, trace_capacity;
} HalBytesRequestV2;

typedef struct {
    unsigned char data[HAL_FRAME_CAP_V1];
    size_t start, end;
} HalInputV1;

static int write_all(const unsigned char *p, size_t n) {
    size_t at = 0;
    while (at < n) {
        ssize_t k = write(STDOUT_FILENO, p + at, n - at);
        if (k > 0) at += (size_t)k;
        else if (k < 0 && errno == EINTR) continue;
        else return 0;
    }
    return 1;
}

static int read_line(HalInputV1 *input,
                     unsigned char p[HAL_FRAME_CAP_V1], size_t *n_out) {
    for (;;) {
        unsigned char *newline = memchr(input->data + input->start, '\n',
                                         input->end - input->start);
        if (newline) {
            size_t n = (size_t)(newline - (input->data + input->start)) + 1;
            memcpy(p, input->data + input->start, n);
            input->start += n;
            if (input->start == input->end) input->start = input->end = 0;
            p[n] = 0; *n_out = n; return 1;
        }
        if (input->start != 0) {
            memmove(input->data, input->data + input->start,
                    input->end - input->start);
            input->end -= input->start; input->start = 0;
        }
        if (input->end + 1 >= HAL_FRAME_CAP_V1) return 0;
        {
            ssize_t k = read(STDIN_FILENO, input->data + input->end,
                             HAL_FRAME_CAP_V1 - input->end - 1);
            if (k < 0 && errno == EINTR) continue;
            if (k <= 0) return k == 0 ? -1 : 0;
            input->end += (size_t)k;
        }
    }
}

static int prefix(const unsigned char *p, size_t n, const char *s, size_t z) {
    return n >= z && memcmp(p, s, z) == 0;
}

static int u64_field(const unsigned char *p, size_t n, size_t *at,
                     uint64_t *out, int terminal) {
    uint64_t value = 0;
    int digits = 0;
    while (*at < n && p[*at] >= '0' && p[*at] <= '9') {
        unsigned d = (unsigned)(p[*at] - '0');
        if (value > (UINT64_MAX - d) / 10) return 0;
        value = value * 10 + d;
        (*at)++; digits++;
    }
    if (!digits || *at >= n || p[*at] != (terminal ? '\n' : '|')) return 0;
    (*at)++;
    *out = value;
    return 1;
}

static int i64_field(const unsigned char *p, size_t n, size_t *at,
                     int64_t *out, int terminal) {
    uint64_t magnitude = 0;
    int negative = 0, digits = 0;
    if (*at < n && p[*at] == '-') { negative = 1; (*at)++; }
    while (*at < n && p[*at] >= '0' && p[*at] <= '9') {
        unsigned d = (unsigned)(p[*at] - '0');
        uint64_t limit = negative ? UINT64_C(9223372036854775808)
                                  : UINT64_C(9223372036854775807);
        if (magnitude > (limit - d) / 10) return 0;
        magnitude = magnitude * 10 + d; (*at)++; digits++;
    }
    if (!digits || *at >= n || p[*at] != (terminal ? '\n' : '|')) return 0;
    (*at)++;
    if (negative)
        *out = magnitude == UINT64_C(9223372036854775808)
            ? INT64_MIN : -(int64_t)magnitude;
    else *out = (int64_t)magnitude;
    return 1;
}

static int parse_request(const unsigned char *p, size_t n, HalRequestV1 *r) {
    uint64_t *field = &r->contract;
    size_t at = 8;
    int i;
    if (!prefix(p, n, "HALREQ1|", 8)) return 0;
    for (i = 0; i < HAL_REQUEST_FIELDS_V1; ++i)
        if (!u64_field(p, n, &at, &field[i], i == 7)) return 0;
    for (i = 0; i < HAL_REQUEST_FIELDS_V1; ++i)
        if (field[i] > INT64_MAX) return 0;
    return at == n && r->contract == 1 && r->operation > 0 &&
        r->invocation > 0 && r->fixture > 0 && r->trace_capacity > 0 &&
        r->input_length <= r->input_capacity &&
        r->input_offset <= r->input_capacity - r->input_length &&
        r->input_capacity <= UINT64_C(1048576) &&
        r->trace_capacity <= UINT64_C(65536);
}

static int parse_request_v2(const unsigned char *p, size_t n, HalRequestV2 *r) {
    uint64_t *field = &r->contract;
    size_t at = 8;
    int i;
    if (!prefix(p, n, "HALREQ2|", 8)) return 0;
    for (i = 0; i < HAL_REQUEST_FIELDS_V2; ++i)
        if (!u64_field(p, n, &at, &field[i], i == 10)) return 0;
    for (i = 0; i < HAL_REQUEST_FIELDS_V2; ++i)
        if (field[i] > INT64_MAX) return 0;
    return at == n && r->contract == 2 && r->operation > 0 &&
        r->invocation > 0 && r->fixture > 0 &&
        r->result_capacity >= 8 && r->result_capacity <= 32 &&
        (r->trace_hi != 0 || r->trace_lo != 0) &&
        r->trace_cursor <= r->trace_length &&
        r->trace_length <= r->trace_capacity && r->trace_capacity > 0 &&
        r->trace_capacity <= UINT64_C(65536);
}

static int admitted_bytes_operation(uint64_t operation) {
    /* Parent-captured normalized results only. Process and socket lifecycle
     * IDs are typed EnvOpcodeV1 values plus the provider-operation base;
     * admitting them does not perform the represented host side effect. */
    return operation == UINT64_C(102) || operation == UINT64_C(1001) ||
           operation == UINT64_C(1004) ||
           (operation >= UINT64_C(1006) && operation <= UINT64_C(1008)) ||
           (operation >= UINT64_C(1012) && operation <= UINT64_C(1015));
}

static int canonical_word(uint64_t word, uint64_t used) {
    if (used == 0) return word == 0;
    if (used >= 8) return 1;
    return (word >> (unsigned)(used * 8)) == 0;
}

static int parse_bytes_request_v2(const unsigned char *p, size_t n,
                                  HalBytesRequestV2 *r) {
    size_t at = 9;
    int i;
    uint64_t remaining;
    if (!prefix(p, n, "HALREQ2B|", 9)) return 0;
    if (!u64_field(p, n, &at, &r->contract, 0) ||
        !u64_field(p, n, &at, &r->operation, 0) ||
        !u64_field(p, n, &at, &r->invocation, 0) ||
        !u64_field(p, n, &at, &r->fixture, 0) ||
        !u64_field(p, n, &at, &r->status, 0) ||
        !u64_field(p, n, &at, &r->error_domain, 0) ||
        !u64_field(p, n, &at, &r->error_code, 0) ||
        !u64_field(p, n, &at, &r->error_detail, 0) ||
        !u64_field(p, n, &at, &r->payload_length, 0) ||
        !u64_field(p, n, &at, &r->payload_capacity, 0)) return 0;
    for (i = 0; i < 4; ++i)
        if (!i64_field(p, n, &at, &r->word[i], 0)) return 0;
    if (!u64_field(p, n, &at, &r->trace_hi, 0) ||
        !u64_field(p, n, &at, &r->trace_lo, 0) ||
        !u64_field(p, n, &at, &r->trace_cursor, 0) ||
        !u64_field(p, n, &at, &r->trace_length, 0) ||
        !u64_field(p, n, &at, &r->trace_capacity, 1)) return 0;
    if (at != n || r->contract != 2 || !admitted_bytes_operation(r->operation) ||
        r->invocation == 0 || r->fixture == 0 || r->status > 7 ||
        r->payload_capacity == 0 || r->payload_capacity > 32 ||
        r->payload_length > r->payload_capacity ||
        (r->trace_hi == 0 && r->trace_lo == 0) ||
        r->trace_cursor > r->trace_length ||
        r->trace_length > r->trace_capacity || r->trace_capacity == 0 ||
        r->trace_capacity > UINT64_C(65536)) return 0;
    if ((r->status == 0 && (r->error_domain != 0 || r->error_code != 0 ||
                            r->error_detail != 0)) ||
        (r->status != 0 && (r->error_domain == 0 || r->error_domain > 4 ||
                            r->error_code == 0))) return 0;
    for (i = 0; i < 4; ++i) {
        remaining = r->payload_length > (uint64_t)i * 8
            ? r->payload_length - (uint64_t)i * 8 : 0;
        if (!canonical_word((uint64_t)r->word[i], remaining > 8 ? 8 : remaining)) return 0;
    }
    return 1;
}

static int parse_reset(const unsigned char *p, size_t n, uint64_t out[3]) {
    size_t at = 10;
    int i;
    if (!prefix(p, n, "HALRESET1|", 10)) return 0;
    for (i = 0; i < 3; ++i)
        if (!u64_field(p, n, &at, &out[i], i == 2)) return 0;
    return at == n && out[0] > 0 && out[1] > 0 && out[2] > 0 &&
        out[0] <= INT64_MAX && out[1] <= INT64_MAX && out[2] <= INT64_MAX;
}

static uint64_t hash_request(const HalRequestV1 *r, uint64_t seed) {
    const uint64_t *v = &r->contract;
    uint64_t h = seed % UINT64_C(2147483647);
    int i, b;
    for (i = 0; i < HAL_REQUEST_FIELDS_V1; ++i)
        for (b = 0; b < 8; ++b) {
            h = (h * UINT64_C(257) +
                 ((v[i] >> (unsigned)(b * 8)) & UINT64_C(255))) %
                UINT64_C(2147483647);
        }
    return h;
}

static int append_text(unsigned char *p, size_t cap, size_t *at,
                       const char *s) {
    size_t n = strlen(s);
    if (*at > cap - n) return 0;
    memcpy(p + *at, s, n); *at += n; return 1;
}

static int append_i64(unsigned char *p, size_t cap, size_t *at, int64_t v) {
    unsigned char rev[24];
    uint64_t magnitude;
    size_t n = 0;
    if (v < 0) {
        if (*at >= cap) return 0;
        p[(*at)++] = '-';
        magnitude = (uint64_t)(-(v + 1)) + 1;
    } else magnitude = (uint64_t)v;
    do { rev[n++] = (unsigned char)('0' + magnitude % 10); magnitude /= 10; }
    while (magnitude != 0);
    if (*at > cap - n) return 0;
    while (n > 0) p[(*at)++] = rev[--n];
    return 1;
}

static int result(const HalRequestV1 *r) {
    unsigned char out[HAL_FRAME_CAP_V1];
    size_t at = 0;
    int64_t digest = (int64_t)hash_request(r, UINT64_C(1469598103934665603));
    int64_t trace = (int64_t)hash_request(r, UINT64_C(7809847782465536322));
    int64_t fields[16] = {
        HAL_PROVIDER_KIND, (int64_t)r->invocation, 0, 0,
        digest, (int64_t)((uint64_t)digest ^ UINT64_C(0x6a09e667f3bcc909)),
        trace, (int64_t)((uint64_t)trace ^ UINT64_C(0xbb67ae8584caa73b)),
        (int64_t)r->input_length, (int64_t)r->input_capacity,
        1, (int64_t)r->trace_capacity, 0, -1, 0,
        HAL_REQUEST_FIELDS_V1 * 8
    };
    int i;
    if (!append_text(out, sizeof(out), &at, "HALRES1|")) return 0;
    for (i = 0; i < 16; ++i) {
        if (!append_i64(out, sizeof(out), &at, fields[i]) || at >= sizeof(out))
            return 0;
        out[at++] = i == 15 ? '\n' : '|';
    }
    return write_all(out, at);
}

static int result_v2(const HalRequestV2 *r) {
    unsigned char out[HAL_FRAME_CAP_V1];
    size_t at = 0;
    int64_t fields[19] = {
        HAL_PROVIDER_KIND, (int64_t)r->invocation, 0, 0, 0, 0,
        1, (int64_t)r->captured_scalar, 8, (int64_t)r->result_capacity,
        (int64_t)r->trace_hi, (int64_t)r->trace_lo,
        (int64_t)r->trace_cursor, (int64_t)r->trace_length,
        (int64_t)r->trace_capacity, 0, -1, 0,
        HAL_REQUEST_FIELDS_V2 * 8
    };
    int i;
    if (!append_text(out, sizeof(out), &at, "HALRES2|")) return 0;
    for (i = 0; i < 19; ++i) {
        if (!append_i64(out, sizeof(out), &at, fields[i]) || at >= sizeof(out))
            return 0;
        out[at++] = i == 18 ? '\n' : '|';
    }
    return write_all(out, at);
}

static int bytes_result_v2(const HalBytesRequestV2 *r) {
    unsigned char out[HAL_FRAME_CAP_V1];
    size_t at = 0;
    int64_t fields[23] = {
        HAL_PROVIDER_KIND, (int64_t)r->invocation, (int64_t)r->status,
        (int64_t)r->error_domain, (int64_t)r->error_code,
        (int64_t)r->error_detail, 2, 0,
        (int64_t)r->payload_length, (int64_t)r->payload_capacity,
        r->word[0], r->word[1], r->word[2], r->word[3],
        (int64_t)r->trace_hi, (int64_t)r->trace_lo,
        (int64_t)r->trace_cursor, (int64_t)r->trace_length,
        (int64_t)r->trace_capacity, 0, -1, 0,
        HAL_REQUEST_BYTES_FIELDS_V2 * 8
    };
    int i;
    if (!append_text(out, sizeof(out), &at, "HALRES2B|")) return 0;
    for (i = 0; i < 23; ++i) {
        if (!append_i64(out, sizeof(out), &at, fields[i]) || at >= sizeof(out))
            return 0;
        out[at++] = i == 22 ? '\n' : '|';
    }
    return write_all(out, at);
}

static int dispatch_request(const unsigned char *line, size_t n,
                            uint64_t expected_invocation) {
    HalRequestV1 v1;
    HalRequestV2 v2;
    HalBytesRequestV2 bytes_v2;
    if (parse_request(line, n, &v1))
        return (expected_invocation == 0 || v1.invocation == expected_invocation)
            && result(&v1);
    if (parse_request_v2(line, n, &v2))
        return (expected_invocation == 0 || v2.invocation == expected_invocation)
            && result_v2(&v2);
    if (parse_bytes_request_v2(line, n, &bytes_v2))
        return (expected_invocation == 0 ||
                bytes_v2.invocation == expected_invocation)
            && bytes_result_v2(&bytes_v2);
    return 0;
}

static int reset_ok(const uint64_t reset[3]) {
    unsigned char out[96];
    size_t at = 0;
    int i;
    if (!append_text(out, sizeof(out), &at, "HALRESETOK1|")) return 0;
    for (i = 0; i < 3; ++i) {
        if (!append_i64(out, sizeof(out), &at, (int64_t)reset[i]) ||
            at >= sizeof(out)) return 0;
        out[at++] = i == 2 ? '\n' : '|';
    }
    return write_all(out, at);
}

int main(int argc, char **argv) {
    unsigned char line[HAL_FRAME_CAP_V1];
    HalInputV1 input = {{0}, 0, 0};
    size_t n = 0;
    uint64_t reset[3], generation = 0, next_sequence = 1;
    if (argc == 1) {
        return read_line(&input, line, &n) == 1 && dispatch_request(line, n, 0) ? 0 : 64;
    }
    if (argc != 2 || strcmp(argv[1], "session") != 0 ||
        !write_all((const unsigned char *)"HALWORKER1\n", 11)) return 64;
    for (;;) {
        int read_status = read_line(&input, line, &n);
        if (read_status == -1) return 0;
        if (read_status != 1 || !parse_reset(line, n, reset) ||
            (generation != 0 && reset[0] != generation) ||
            reset[1] != next_sequence || !reset_ok(reset)) return 65;
        generation = reset[0];
        if (read_line(&input, line, &n) != 1 ||
            !dispatch_request(line, n, reset[2])) return 66;
        next_sequence++;
        if (next_sequence == 0) return 67;
    }
}
