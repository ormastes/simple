#include "runtime.h"

#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

SplArray* rt_bytes_from_raw(int64_t ptr, int64_t len);
SplArray* rt_strsplit(const char* string, const char* delimiter);

static int start_server(unsigned short* port, const char* body, int delay_ms) {
    int server = socket(AF_INET, SOCK_STREAM, 0);
    assert(server >= 0);
    struct sockaddr_in address = {0};
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    address.sin_port = 0;
    assert(bind(server, (struct sockaddr*)&address, sizeof(address)) == 0);
    socklen_t address_len = sizeof(address);
    assert(getsockname(server, (struct sockaddr*)&address, &address_len) == 0);
    assert(listen(server, 1) == 0);
    *port = ntohs(address.sin_port);
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        int client = accept(server, NULL, NULL);
        if (client >= 0) {
            char request[2048];
            (void)read(client, request, sizeof(request));
            if (delay_ms > 0) usleep((useconds_t)delay_ms * 1000);
            char response[256];
            int response_len = snprintf(response, sizeof(response),
                "HTTP/1.1 200 OK\r\nContent-Length: %zu\r\nConnection: close\r\n\r\n%s",
                strlen(body), body);
            (void)write(client, response, (size_t)response_len);
            close(client);
        }
        close(server);
        _exit(0);
    }
    close(server);
    return child;
}

static int64_t text(const char* value) {
    return rt_string_new((const uint8_t*)value, strlen(value));
}

static int walk_contains(SplArray* paths, const char* expected) {
    for (int64_t i = 0; i < spl_array_len(paths); i++) {
        const char* actual = spl_as_str(spl_array_get(paths, i));
        if (actual && strcmp(actual, expected) == 0) return 1;
    }
    return 0;
}

int main(void) {
    const uint8_t raw_bytes[] = {0, 127, 255};
    SplArray* canonical_bytes = rt_bytes_from_raw((int64_t)(uintptr_t)raw_bytes, 3);
    assert(rt_array_len(canonical_bytes) == 3);
    assert(rt_array_get(canonical_bytes, 0) == 0);
    assert(rt_array_get(canonical_bytes, 1) == 127);
    assert(rt_array_get(canonical_bytes, 2) == 255);
    assert(rt_array_len(rt_bytes_from_raw(0, 3)) == 0);

    SplArray* split = rt_strsplit("a,,b", ",");
    assert(rt_array_len(split) == 3);
    assert(strcmp((const char*)rt_string_data(rt_array_get(split, 0)), "a") == 0);
    assert(strcmp((const char*)rt_string_data(rt_array_get(split, 1)), "") == 0);
    assert(strcmp((const char*)rt_string_data(rt_array_get(split, 2)), "b") == 0);
    split = rt_strsplit("plain", ",");
    assert(rt_array_len(split) == 1);
    assert(strcmp((const char*)rt_string_data(rt_array_get(split, 0)), "plain") == 0);
    split = rt_strsplit("plain", "");
    assert(rt_array_len(split) == 1);
    assert(strcmp((const char*)rt_string_data(rt_array_get(split, 0)), "plain") == 0);

    char walk_root[] = "/tmp/simple-dir-walk-XXXXXX";
    assert(mkdtemp(walk_root) != NULL);
    char walk_nested[256], walk_suffix_dir[256], walk_regular[256];
    char walk_child[256], walk_file_link[256], walk_cycle[256];
    snprintf(walk_nested, sizeof(walk_nested), "%s/nested", walk_root);
    snprintf(walk_suffix_dir, sizeof(walk_suffix_dir), "%s/x.spl", walk_root);
    snprintf(walk_regular, sizeof(walk_regular), "%s/regular.spl", walk_root);
    snprintf(walk_child, sizeof(walk_child), "%s/child.spl", walk_nested);
    snprintf(walk_file_link, sizeof(walk_file_link), "%s/file-link.spl", walk_root);
    snprintf(walk_cycle, sizeof(walk_cycle), "%s/back", walk_nested);
    assert(mkdir(walk_nested, 0700) == 0);
    assert(mkdir(walk_suffix_dir, 0700) == 0);
    FILE* walk_file = fopen(walk_regular, "w");
    assert(walk_file != NULL && fclose(walk_file) == 0);
    walk_file = fopen(walk_child, "w");
    assert(walk_file != NULL && fclose(walk_file) == 0);
    assert(symlink(walk_regular, walk_file_link) == 0);
    assert(symlink(walk_root, walk_cycle) == 0);
    SplArray* walked = rt_dir_walk(walk_root);
    assert(spl_array_len(walked) == 4);
    assert(walk_contains(walked, walk_regular));
    assert(walk_contains(walked, walk_child));
    assert(walk_contains(walked, walk_file_link));
    assert(walk_contains(walked, walk_cycle));
    assert(!walk_contains(walked, walk_nested));
    assert(!walk_contains(walked, walk_suffix_dir));
    assert(rt_dir_remove_all(walk_root));
    assert(access(walk_root, F_OK) != 0);

    int64_t builder = rt_string_builder_new();
    assert(builder != 0);
    assert(rt_string_builder_push(builder, text("hello")) == 1);
    assert(rt_string_builder_push(builder, text("")) == 1);
    assert(rt_string_builder_push(builder, text(" world")) == 1);
    assert(rt_string_builder_len(builder) == 11);
    int64_t built = rt_string_builder_finish(builder);
    assert(rt_string_len(built) == 11);
    assert(memcmp(rt_string_data(built), "hello world", 11) == 0);
    int64_t trim_end = rt_string_trim_end(text("  value \t\r\n"));
    assert(rt_string_len(trim_end) == 7);
    assert(memcmp(rt_string_data(trim_end), "  value", 7) == 0);
    assert(rt_string_builder_len(0) == -1);
    assert(rt_string_builder_push(0, built) == 0);
    rt_string_builder_free(0);
    builder = rt_string_builder_new();
    assert(builder != 0);
    rt_string_builder_free(builder);

    SplArray* allocated = rt_bytes_alloc(4);
    assert(allocated != NULL);
    assert(unsafe_addr_of((int64_t)(uintptr_t)allocated) == (uint64_t)(uintptr_t)allocated);
    assert(rt_array_len(allocated) == 4);
    for (int64_t i = 0; i < 4; i++) assert(rt_bytes_u8_at(allocated, i) == 0);
    SplArray* left = rt_array_new(1);
    SplArray* right = rt_array_new(1);
    assert(rt_array_push(left, 11));
    assert(rt_array_push(right, 22));
    SplArray* joined = rt_array_concat(left, right);
    assert(rt_array_len(joined) == 2);
    assert(rt_array_get(joined, 0) == 11);
    assert(rt_array_get(joined, 1) == 22);
    SplArray* generic_bytes = rt_array_new(1);
    for (int64_t i = 0; i < 12; i++) {
        assert(rt_typed_bytes_u8_push(generic_bytes, i + 20));
    }
    assert(rt_bytes_u8_at(generic_bytes, 8) == 28);
    assert(rt_typed_bytes_u8_unchecked(generic_bytes, 8) == 28);
    assert(rt_bytes_u8_set(generic_bytes, 8, 8));
    assert(rt_bytes_u8_at(generic_bytes, 8) == 8);
    assert(rt_typed_bytes_u32_le_set(generic_bytes, 8, 0x11223344));
    assert(rt_bytes_u32_le_at(generic_bytes, 8) == 0x11223344);
    assert(rt_typed_bytes_u64_le_set(generic_bytes, 4, 0x0102030405060708LL));
    assert(rt_bytes_u64_le_at(generic_bytes, 4) == 0x0102030405060708LL);
    assert(rt_typed_bytes_u64_le_unchecked(generic_bytes, 4) == 0x0102030405060708LL);
    assert(rt_bytes_u8_at(allocated, 0) == 0);
    SplArray* packed_bytes_equal = rt_byte_array_new(1);
    SplArray* generic_bytes_equal = rt_array_new(1);
    for (int64_t i = 0; i < 5; i++) {
        assert(rt_typed_bytes_u8_push(packed_bytes_equal, i * 2 + 2));
        assert(rt_typed_bytes_u8_push(generic_bytes_equal, i * 2 + 2));
    }
    assert(rt_native_eq((int64_t)(uintptr_t)packed_bytes_equal,
                        (int64_t)(uintptr_t)generic_bytes_equal));
    rt_bdd_clear_state();
    rt_bdd_expect_eq_rv((int64_t)(uintptr_t)packed_bytes_equal,
                        (int64_t)(uintptr_t)generic_bytes_equal);
    assert(rt_bdd_has_failure() == 0);
    rt_bdd_clear_state();
    assert(!rt_native_eq(0x1001, 0x2001));
    assert(rt_typed_bytes_u8_push(generic_bytes_equal, 12));
    assert(!rt_native_eq((int64_t)(uintptr_t)packed_bytes_equal,
                         (int64_t)(uintptr_t)generic_bytes_equal));
    SplArray* cycle_left = rt_array_new(1);
    SplArray* cycle_right = rt_array_new(1);
    assert(rt_array_push(cycle_left, (int64_t)(uintptr_t)cycle_left));
    assert(rt_array_push(cycle_right, (int64_t)(uintptr_t)cycle_right));
    assert(rt_native_eq((int64_t)(uintptr_t)cycle_left,
                        (int64_t)(uintptr_t)cycle_right));
    SplArray* wide_left = rt_array_new(300);
    SplArray* wide_right = rt_array_new(300);
    for (int64_t i = 0; i < 300; i++) {
        SplArray* child_left = rt_array_new(1);
        SplArray* child_right = rt_array_new(1);
        assert(rt_array_push(child_left, rt_value_int(i)));
        assert(rt_array_push(child_right, rt_value_int(i)));
        assert(rt_array_push(wide_left, (int64_t)(uintptr_t)child_left));
        assert(rt_array_push(wide_right, (int64_t)(uintptr_t)child_right));
    }
    assert(rt_native_eq((int64_t)(uintptr_t)wide_left,
                        (int64_t)(uintptr_t)wide_right));
    SplArray* float_left = rt_array_new(1);
    SplArray* float_right = rt_array_new(1);
    assert(rt_array_push(float_left, rt_value_float(0)));
    assert(rt_array_push(float_right, rt_value_float(INT64_MIN)));
    assert(rt_native_eq((int64_t)(uintptr_t)float_left,
                        (int64_t)(uintptr_t)float_right));
    int64_t enum_left = rt_enum_new(7, 3, rt_value_int(42));
    int64_t enum_right = rt_enum_new(9, 3, rt_value_int(42));
    assert(rt_native_eq(enum_left, enum_right));
    SplArray* generic_words = rt_array_new(1);
    for (int64_t i = 0; i < 12; i++) {
        assert(rt_typed_words_u64_push(generic_words, 0x200000 + i * 8));
    }
    assert(rt_typed_words_u64_at(generic_words, 0) == 0x200000);
    assert(rt_typed_words_u64_at(generic_words, 8) == 0x200040);
    assert(rt_typed_words_u64_at(generic_words, 11) == 0x200058);
    assert(rt_array_get(generic_words, 11) == rt_value_int(0x200058));
    assert(rt_typed_words_u32_at(generic_words, 8) == 0x200040);
    assert(rt_typed_words_u32_set(generic_words, 8, 0x300040));
    assert(rt_typed_words_u32_at(generic_words, 8) == 0x300040);
    assert(rt_typed_words_u64_set(generic_words, 8, 0x400040));
    assert(rt_typed_words_u64_at(generic_words, 8) == 0x400040);
    assert(rt_typed_words_u64_store_known_data_at(
        rt_array_header_ptr(generic_words), rt_array_data_ptr(generic_words), 8, 0x500040));
    assert(rt_typed_words_u64_at(generic_words, 8) == 0x500040);
    assert(rt_array_get(generic_words, 8) == rt_value_int(0x500040));
    assert(rt_typed_words_u64_push(generic_words, -1));
    assert(rt_typed_words_u64_at(generic_words, 12) == -1);
    assert(rt_typed_words_u64_set(generic_words, 0, 0x300000));
    assert(rt_typed_words_u64_at(generic_words, 0) == 0x300000);
    SplArray* packed_words = rt_array_new_with_cap_u64(1);
    assert(rt_typed_words_u64_push(packed_words, 0x123456789abcdef0LL));
    assert((uint64_t)rt_typed_words_u64_at(packed_words, 0) == 0x123456789abcdef0ULL);
    assert(rt_typed_words_u64_store_known_data_at(
        rt_array_header_ptr(packed_words), rt_array_data_ptr(packed_words), 0, 0x0fedcba987654321LL));
    assert((uint64_t)rt_typed_words_u64_at(packed_words, 0) == 0x0fedcba987654321ULL);
    SplArray* packed_words_equal = rt_array_new_with_cap_u64(3);
    SplArray* generic_words_equal = rt_array_new(3);
    for (int64_t i = -1; i < 2; i++) {
        assert(rt_typed_words_u64_push(packed_words_equal, i));
        assert(rt_typed_words_u64_push(generic_words_equal, i));
    }
    assert(rt_native_eq((int64_t)(uintptr_t)packed_words_equal,
                        (int64_t)(uintptr_t)generic_words_equal));
    int64_t tuple = rt_tuple_new(9);
    assert(rt_tuple_set(tuple, 8, rt_value_int(88)));
    assert(rt_tuple_get(tuple, 8) == rt_value_int(88));
    assert(rt_is_none(rt_value_nil()));
    assert(!rt_is_some(rt_value_nil()));
    assert(rt_math_pow(2.0, 3.0) == 8.0);
    uint64_t mmio = 0;
    rt_volatile_write_u8((int64_t)(uintptr_t)&mmio, 0x12);
    assert(rt_volatile_read_u8((int64_t)(uintptr_t)&mmio) == 0x12);
    rt_volatile_write_u64((int64_t)(uintptr_t)&mmio, 0x123456789abcdef0ULL);
    assert((uint64_t)rt_volatile_read_u64((int64_t)(uintptr_t)&mmio) == 0x123456789abcdef0ULL);
    rt_memory_barrier();
    rt_write_cr3(0x12345000);
    assert(rt_read_cr3() == 0x12345000);
    rt_write_cr3_raw(0x6789a000);
    assert(rt_read_cr3_raw() == 0x6789a000);
    rt_invlpg(0);
    serial_println(text(""));

    int64_t parent = rt_path_parent((const uint8_t*)"a/b/file.spl", 10);
    assert(strcmp((const char*)rt_string_data(parent), "a/b") == 0);
    int64_t path = text("a/b/file.spl");
    assert(strcmp((const char*)rt_string_data(rt_path_filename(path)), "file.spl") == 0);
    assert(strcmp((const char*)rt_string_data(rt_path_extension(path)), "spl") == 0);

    int64_t glyph = rt_gui_get_glyph_8x16('A');
    assert(rt_array_len((SplArray*)(uintptr_t)glyph) == 16);
    assert(rt_array_get((SplArray*)(uintptr_t)glyph, 0) == 0);
    assert(rt_array_get((SplArray*)(uintptr_t)glyph, 1) != 0);
    rt_sleep_secs(0);
    rt_thread_sleep(0);
    int64_t atomic = rt_atomic_int_new(7);
    assert(atomic != 0);
    assert(rt_atomic_int_load(atomic) == 7);
    assert(rt_atomic_int_compare_exchange(atomic, 7, 9));
    assert(!rt_atomic_int_compare_exchange(atomic, 7, 11));
    assert(rt_atomic_int_load(atomic) == 9);
    assert(rt_signal_install(SIGUSR1) == 1);
    assert(raise(SIGUSR1) == 0);
    assert(rt_signal_check(SIGUSR1) == 1);
    assert(rt_signal_check(SIGUSR1) == 0);
    assert(rt_atexit_install() == 1);
    assert(rt_atexit_check() == 0);
    int64_t monotonic_before = rt_time_now_monotonic_ms();
    assert(monotonic_before > 0);
    assert(rt_time_now_monotonic_ms() >= monotonic_before);
    int64_t epoch_ms = rt_time_ms();
    assert(epoch_ms >= (int64_t)time(NULL) * 1000 - 1000);
    assert(epoch_ms <= (int64_t)time(NULL) * 1000 + 1000);
    int64_t pointer_text = text("pointer");
    assert(strcmp((const char*)(uintptr_t)spl_str_ptr((const char*)(uintptr_t)pointer_text),
                  "pointer") == 0);
    const char* raw_pointer = "raw-pointer";
    assert((const char*)(uintptr_t)spl_str_ptr(raw_pointer) == raw_pointer);

    pid_t panic_child = fork();
    assert(panic_child >= 0);
    if (panic_child == 0) {
        (void)freopen("/dev/null", "w", stderr);
        panic(text("focused panic"));
        _exit(1);
    }
    int panic_status = 0;
    assert(waitpid(panic_child, &panic_status, 0) == panic_child);
    assert(WIFEXITED(panic_status) && WEXITSTATUS(panic_status) == 1);

    char crlf_url[] = "http://127.0.0.1\r\n:1/";
    int64_t invalid = rt_http_request(text("GET"), text(crlf_url),
                                      (int64_t)rt_array_new(0), text(""));
    assert(rt_value_as_int(rt_tuple_get(invalid, 0)) == -1);
    char control_url[] = "http://127.0.0.1:1/\x01";
    invalid = rt_http_request(text("GET"), text(control_url),
                              (int64_t)rt_array_new(0), text(""));
    assert(rt_value_as_int(rt_tuple_get(invalid, 0)) == -1);
    invalid = rt_http_request(text("GE T"), text("http://127.0.0.1:1/"),
                              (int64_t)rt_array_new(0), text(""));
    assert(rt_value_as_int(rt_tuple_get(invalid, 0)) == -1);
    invalid = rt_http_request(text("GET"), text("http://127.0.0.1:1/bad path"),
                              (int64_t)rt_array_new(0), text(""));
    assert(rt_value_as_int(rt_tuple_get(invalid, 0)) == -1);

    char nul_path[128];
    int nul_prefix_len = snprintf(nul_path, sizeof(nul_path),
                                  "/tmp/simple-runtime-create-%ld", (long)getpid());
    assert(nul_prefix_len > 0 && (size_t)nul_prefix_len + 7 < sizeof(nul_path));
    memcpy(nul_path + nul_prefix_len + 1, "suffix", 6);
    unlink(nul_path);
    assert(rt_file_create_excl(nul_path, nul_prefix_len + 7, "x", 1) == 0);
    assert(access(nul_path, F_OK) != 0);

    unsigned short port;
    pid_t child = start_server(&port, "hello", 0);
    char url[64];
    snprintf(url, sizeof(url), "http://127.0.0.1:%u/", port);
    int64_t response = rt_http_get(text(url));
    assert(rt_value_as_int(rt_tuple_get(response, 0)) == 200);
    assert(strcmp((const char*)rt_string_data(rt_tuple_get(response, 1)), "hello") == 0);
    assert(strcmp((const char*)rt_string_data(rt_tuple_get(response, 2)), "") == 0);
    assert(waitpid(child, NULL, 0) == child);

    child = start_server(&port, "request", 0);
    snprintf(url, sizeof(url), "http://127.0.0.1:%u/", port);
    response = rt_http_request(text("GET"), text(url), (int64_t)rt_array_new(0), text(""));
    assert(rt_value_as_int(rt_tuple_get(response, 0)) == 200);
    assert(strcmp((const char*)rt_string_data(rt_tuple_get(response, 1)), "request") == 0);
    assert(waitpid(child, NULL, 0) == child);

    int64_t client = rt_http_client_create();
    assert(client > 0);
    assert(!rt_http_client_set_timeout(client, -1));
    assert(rt_http_client_set_timeout(client, 50));
    unsigned short delayed_port;
    child = start_server(&delayed_port, "too late", 200);
    snprintf(url, sizeof(url), "http://127.0.0.1:%u/", delayed_port);
    int64_t started = rt_time_now_monotonic_ms();
    int64_t timed_out = rt_http_client_request(
        client, text("GET"), text(url), (int64_t)rt_array_new(0), text(""));
    int64_t elapsed = rt_time_now_monotonic_ms() - started;
    assert(rt_value_as_int(rt_tuple_get(timed_out, 0)) == -1);
    assert(strstr((const char*)rt_string_data(rt_tuple_get(timed_out, 2)), "timed out") != NULL);
    assert(elapsed >= 0 && elapsed < 1000);
    assert(waitpid(child, NULL, 0) == child);
    rt_http_client_destroy(client);
    int64_t destroyed = rt_http_client_request(
        client, text("GET"), text(url), (int64_t)rt_array_new(0), text(""));
    assert(rt_value_as_int(rt_tuple_get(destroyed, 0)) == -1);
    assert(strstr((const char*)rt_string_data(rt_tuple_get(destroyed, 2)), "invalid HTTP client") != NULL);
    int64_t replacement = rt_http_client_create();
    assert(replacement > 0 && replacement != client);
    assert(!rt_http_client_set_timeout(client, 1));
    rt_http_client_destroy(replacement);

    int64_t clients[80];
    int client_count = 0;
    while (client_count < 80 && (clients[client_count] = rt_http_client_create()) > 0) client_count++;
    assert(client_count == 64);
    assert(rt_http_client_create() == 0);
    for (int i = 0; i < client_count; i++) rt_http_client_destroy(clients[i]);

    unsigned short download_port;
    child = start_server(&download_port, "abc", 0);
    snprintf(url, sizeof(url), "http://127.0.0.1:%u/", download_port);
    const char* output = "/tmp/simple-runtime-native-download-test";
    int64_t downloaded = rt_http_download(text(url), text(output));
    assert(rt_value_as_int(rt_tuple_get(downloaded, 0)) == 200);
    assert(rt_value_as_int(rt_tuple_get(downloaded, 1)) == 3);
    FILE* file = fopen(output, "rb");
    char bytes[4] = {0};
    assert(file && fread(bytes, 1, 3, file) == 3 && memcmp(bytes, "abc", 3) == 0);
    fclose(file);
    unlink(output);
    assert(waitpid(child, NULL, 0) == child);
    return 0;
}
