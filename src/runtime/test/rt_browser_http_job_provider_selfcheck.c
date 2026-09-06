/* Optional live smoke for the staged Rust browser HTTP provider.
 *
 * The provider ABI represents text and byte arrays as a transparent u64
 * RuntimeValue.  Keep this harness at that ABI boundary rather than relying
 * on the Simple interpreter's HTTP-job stubs.
 */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

typedef uint64_t RuntimeValue;

extern RuntimeValue rt_string_new(const uint8_t *bytes, uint64_t len);
extern RuntimeValue rt_bytes_from_raw(int64_t ptr, int64_t len);
extern int64_t rt_browser_http_job_start_public_limited(
    RuntimeValue scheme, RuntimeValue host, int64_t port,
    RuntimeValue request, int64_t timeout_ms, int64_t max_response_bytes);
extern int64_t rt_browser_http_job_poll(int64_t handle);
extern RuntimeValue rt_browser_http_job_take_response(int64_t handle);
extern RuntimeValue rt_browser_http_job_take_error(int64_t handle);
extern bool rt_browser_http_job_free(int64_t handle);
extern int64_t rt_array_len(RuntimeValue array);
extern int64_t rt_bytes_u8_at(RuntimeValue array, int64_t index);
extern int64_t rt_string_len(RuntimeValue string);
extern const uint8_t *rt_string_data(RuntimeValue string);

static int64_t monotonic_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static RuntimeValue text_value(const char *value) {
    return rt_string_new((const uint8_t *)value, (uint64_t)strlen(value));
}

static uint8_t ascii_lower(uint8_t value) {
    return value >= 'A' && value <= 'Z' ? (uint8_t)(value + ('a' - 'A')) : value;
}

static int text_contains_ascii_case(RuntimeValue value, const char *needle) {
    const uint8_t *data = rt_string_data(value);
    int64_t length = rt_string_len(value);
    size_t needle_length = strlen(needle);
    int64_t index;
    size_t offset;
    if (!data || length < (int64_t)needle_length) return 0;
    for (index = 0; index <= length - (int64_t)needle_length; ++index) {
        for (offset = 0; offset < needle_length; ++offset) {
            if (ascii_lower(data[index + (int64_t)offset]) !=
                ascii_lower((uint8_t)needle[offset])) break;
        }
        if (offset == needle_length) return 1;
    }
    return 0;
}

static int run_case(const char *host, int expect_certificate_error) {
    char request[512];
    RuntimeValue scheme = text_value("https");
    RuntimeValue host_value = text_value(host);
    int written = snprintf(request, sizeof(request),
        "GET / HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n\r\n", host);
    int64_t handle;
    int64_t started;
    int64_t deadline;
    int64_t now;
    int64_t state = 0;
    RuntimeValue response;
    RuntimeValue error;
    int64_t response_length;
    int result = 2;
    if (written < 0 || (size_t)written >= sizeof(request)) return 2;
    started = monotonic_ms();
    if (started < 0) {
        fputs("monotonic clock unavailable\n", stderr);
        return 2;
    }
    handle = rt_browser_http_job_start_public_limited(
        scheme, host_value, 443,
        rt_bytes_from_raw((int64_t)(intptr_t)request, written), 5000, 65536);
    if (handle <= 0) {
        fprintf(stderr, "HTTPS endpoint unavailable: %s\n", host);
        return 77;
    }
    deadline = started + 10000;
    while ((state = rt_browser_http_job_poll(handle)) == 0) {
        now = monotonic_ms();
        if (now < 0) {
            fputs("monotonic clock unavailable while polling\n", stderr);
            goto done;
        }
        if (now >= deadline) {
            fprintf(stderr, "HTTPS endpoint timed out: %s\n", host);
            result = 77;
            goto done;
        }
        usleep(10000);
    }
    if (state != 1) {
        fputs("browser HTTP job disappeared while polling\n", stderr);
        goto done;
    }
    response = rt_browser_http_job_take_response(handle);
    error = rt_browser_http_job_take_error(handle);
    response_length = rt_array_len(response);
    if (!expect_certificate_error) {
        if (response_length >= 5 &&
            rt_bytes_u8_at(response, 0) == 'H' &&
            rt_bytes_u8_at(response, 1) == 'T' &&
            rt_bytes_u8_at(response, 2) == 'T' &&
            rt_bytes_u8_at(response, 3) == 'P' &&
            rt_bytes_u8_at(response, 4) == '/' &&
            rt_string_len(error) == 0) {
            result = 0;
        } else {
            fprintf(stderr,
                "trusted HTTPS endpoint unavailable or untrusted: %s\n", host);
            result = 77;
        }
    } else if (response_length > 0) {
        fprintf(stderr, "invalid certificate was accepted: %s\n", host);
        result = 1;
    } else if (text_contains_ascii_case(error, "certificate") ||
               text_contains_ascii_case(error, "cert")) {
        result = 0;
    } else {
        fprintf(stderr, "invalid-certificate endpoint unavailable: %s\n", host);
        result = 77;
    }
done:
    if (!rt_browser_http_job_free(handle)) {
        fputs("failed to free browser HTTP job\n", stderr);
        return 2;
    }
    return result;
}

int main(int argc, char **argv) {
    int result;
    if (argc != 3) {
        fputs("usage: rt_browser_http_job_provider_selfcheck TRUSTED_HOST INVALID_CERT_HOST\n", stderr);
        return 64;
    }
    result = run_case(argv[1], 0);
    if (result != 0) return result;
    return run_case(argv[2], 1);
}
