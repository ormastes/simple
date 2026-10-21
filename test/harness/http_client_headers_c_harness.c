/* Native boundary contract, independent of a Simple compiler or live service. */
#include "../../src/runtime/runtime_native.c"

/* Extra Windows link dependencies outside the exercised HTTP boundary.
 * Like rt_clear_harness_stubs.c, abort if accidentally reached. */
int64_t spl_f64_to_bits(double value) { (void)value; abort(); }
#if defined(_WIN32)
int64_t rt_open_fd(const char* path, int64_t flags, int64_t mode) {
    (void)path; (void)flags; (void)mode; abort();
}
#endif
int64_t* rt_process_run_owned_observed_bounded_value(const char* cmd, uint64_t len,
        SplArray* args, int64_t timeout, int64_t bound) {
    (void)cmd; (void)len; (void)args; (void)timeout; (void)bound; abort();
}

static int checked, failed;
static void check(int condition, const char* label) {
    checked++;
    if (!condition) { failed++; fprintf(stderr, "FAIL: %s\n", label); }
}
static int64_t text(const char* value) {
    return rt_string_new((const uint8_t*)value, strlen(value));
}
int main(void) {
    int64_t client = rt_http_client_create();
    uint64_t generation;
    int slot = rt_http_client_slot(client, &generation);
    int64_t key = text("Content-Type"), value = text("text/plain");
    check(client > 0, "client allocation");
    check(rt_http_client_set_header(client, key, value), "store default header");
    rt_string_free(key); rt_string_free(value);
    check(rt_http_clients[slot].header_count == 1 &&
          strcmp(rt_http_clients[slot].headers[0].line, "Content-Type: text/plain") == 0,
          "default owns input bytes after caller frees text");
    check(rt_http_client_set_header(client, text("content-type"), text("application/json")),
          "case insensitive replacement");
    check(rt_http_clients[slot].header_count == 1 &&
          strcmp(rt_http_clients[slot].headers[0].line, "content-type: application/json") == 0,
          "replacement does not duplicate header");
    check(!rt_http_client_set_header(client, text("X-Invalid:"), text("x")), "invalid key");
    check(!rt_http_client_set_header(client, text("X-Valid"), text("a\r\nInjected: yes")), "CRLF injection");
    check(!rt_http_client_set_header(client, text(""), text("x")), "empty key");
    int64_t nul = rt_string_new((const uint8_t*)"a\0b", 3);
    check(!rt_http_client_set_header(client, text("X-Nul"), nul), "embedded nul value");
    check(rt_http_clients[slot].header_count == 1, "rejections preserve defaults");
    SplArray* invalid = rt_array_new(1);
    rt_array_push(invalid, text("bad header"));
    int64_t result = rt_http_client_request(client, text("GET"), text("http://127.0.0.1/"),
                    (int64_t)(uintptr_t)invalid, text(""));
    check(rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)result, 0)) == -1,
          "request rejects invalid header before transport");
    rt_http_client_destroy(client);
    check(rt_http_clients[slot].headers == NULL && rt_http_clients[slot].header_bytes == 0,
          "destroy clears owned defaults");
    check(!rt_http_client_set_header(client, text("X-Stale"), text("x")), "destroyed setter rejected");
    int64_t replacement = rt_http_client_create();
    check(replacement != client && rt_http_clients[slot].header_count == 0,
          "new generation has no inherited defaults");
    check(!rt_http_client_set_header(client, text("X-Stale"), text("x")), "stale generation rejected");
    char name[40];
    for (int i = 0; i < RT_HTTP_CLIENT_HEADER_LIMIT; i++) {
        snprintf(name, sizeof(name), "X-%d", i);
        if (!rt_http_client_set_header(replacement, text(name), text("v"))) failed++;
    }
    check(rt_http_clients[slot].header_count == RT_HTTP_CLIENT_HEADER_LIMIT, "bounded capacity filled");
    check(!rt_http_client_set_header(replacement, text("X-Overflow"), text("v")), "capacity rejects overflow");
    check(rt_http_client_set_header(replacement, text("x-0"), text("updated")), "replacement allowed at capacity");
    SplArray* override = rt_array_new(1);
    rt_array_push(override, text("X-0: per-request"));
    result = rt_http_client_request(replacement, text("GET"), text("invalid://local"),
                    (int64_t)(uintptr_t)override, text(""));
    RtCoreString* error = rt_core_as_string(rt_array_get((SplArray*)(uintptr_t)result, 2));
    check(error && strcmp(error->data, "HTTP client header limit or allocation failure") != 0,
          "per-request header overrides default at full capacity");
    SplArray* extra = rt_array_new(1);
    rt_array_push(extra, text("Other: v"));
    result = rt_http_client_request(replacement, text("GET"), text("invalid://local"),
                    (int64_t)(uintptr_t)extra, text(""));
    error = rt_core_as_string(rt_array_get((SplArray*)(uintptr_t)result, 2));
    check(error && strcmp(error->data, "HTTP client header limit or allocation failure") == 0,
          "combined headers enforce limit before transport");
    rt_http_client_destroy(replacement);
    char* huge = (char*)malloc(RT_HTTP_CLIENT_HEADER_BYTES + 1);
    memset(huge, 'v', RT_HTTP_CLIENT_HEADER_BYTES);
    huge[RT_HTTP_CLIENT_HEADER_BYTES] = 0;
    replacement = rt_http_client_create();
    check(!rt_http_client_set_header(replacement, text("X"), text(huge)), "byte budget rejects oversized value");
    free(huge);
    rt_http_client_destroy(replacement);
    printf("HTTP configured headers: %d checks, %d failures\n", checked, failed);
    return failed ? 1 : 0;
}
