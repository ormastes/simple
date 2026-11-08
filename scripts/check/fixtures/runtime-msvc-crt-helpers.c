/* Compile with clang-cl /Werror:deprecated-declarations and run on Windows. */
#include <assert.h>
#include <stdio.h>
#include <windows.h>
#include "runtime_memtrack.h"
#include "runtime_memory_guard.h"
#include "platform/runtime_win_long_path.h"
#include "runtime_payload_text.h"

int g_memtrack_enabled = 1;
static int recorded;
static int64_t recorded_size;
void spl_memtrack_record(void* ptr, int64_t size, const char* tag) {
    assert(ptr && strcmp(tag, "fixture") == 0);
    recorded++;
    recorded_size = size;
}
void spl_memtrack_unrecord(void* ptr) { assert(ptr); recorded--; }

int main(void) {
    struct { char before; char text[4096]; char after; } payload;
    char source[4200];
    memset(source, 'x', sizeof(source));
    source[sizeof(source) - 1] = '\0';
    payload.before = 'a'; payload.after = 'z';
    rt_host_gpu_queue_copy_payload_text(NULL, source);
    rt_host_gpu_queue_copy_payload_text(payload.text, NULL);
    assert(payload.text[0] == '\0');
    rt_host_gpu_queue_copy_payload_text(payload.text, "");
    assert(payload.text[0] == '\0');
    rt_host_gpu_queue_copy_payload_text(payload.text, "short");
    assert(strcmp(payload.text, "short") == 0);
    rt_host_gpu_queue_copy_payload_text(payload.text, source);
    assert(strlen(payload.text) == 4095);
    assert(memcmp(payload.text, source, 4095) == 0);
    source[4095] = '\0';
    rt_host_gpu_queue_copy_payload_text(payload.text, source);
    assert(strlen(payload.text) == 4095);
    assert(payload.before == 'a' && payload.after == 'z');
    char* value = spl_rt_strdup("hello", "fixture");
    assert(value && strcmp(value, "hello") == 0);
    assert(recorded == 1 && recorded_size == 6);
    spl_rt_free(value);
    assert(recorded == 0);
    value = spl_rt_strdup("", "fixture");
    assert(value && *value == '\0' && recorded_size == 1);
    spl_rt_free(value);
    assert(_putenv_s("SIMPLE_MEM_GUARD_RATE", "17") == 0);
    assert(rt_mem_guard_rate() == 17);
    assert(_putenv_s("SIMPLE_MEM_GUARD_RATE", "29") == 0);
    assert(rt_mem_guard_rate() == 17); /* Read once, as before. */
    rt_mem_guard_rate_cached = -1;
    assert(_putenv_s("SIMPLE_MEM_GUARD_RATE", "invalid") == 0);
    assert(rt_mem_guard_rate() == 0);
    rt_mem_guard_rate_cached = -1;
    assert(_putenv_s("SIMPLE_MEM_GUARD_RATE", "") == 0);
    assert(rt_mem_guard_rate() == 0);
    FILE* file = NULL;
    assert(fopen_s(&file, "msvc-crt-fixture.tmp", "wb") == 0);
    assert(fwrite("ok", 1, 2, file) == 2);
    assert(fclose(file) == 0);
    file = rt_win_fopen_read_shared("msvc-crt-fixture.tmp");
    assert(file && fgetc(file) == 'o' && fgetc(file) == 'k');
    assert(fclose(file) == 0);
    assert(remove("msvc-crt-fixture.tmp") == 0);
    assert(!rt_win_fopen_read_shared("missing-msvc-crt-fixture.tmp"));
    /* Invalid UTF-8 forces the CRT fallback; the missing file must fail. */
    assert(!rt_win_fopen_read_shared("missing-\xff-msvc-crt-fixture.tmp"));
    /* The ANSI CRT accepts this name, while UTF-8 widening rejects it.
     * Preserve the original fallback's sharing with concurrent writers. */
    const char* fallback_path = "fallback-\xff-msvc-crt-fixture.tmp";
    FILE* writer = _fsopen(fallback_path, "wb", _SH_DENYNO);
    assert(writer && fputc('x', writer) == 'x' && fclose(writer) == 0);
    file = rt_win_fopen_read_shared(fallback_path);
    assert(file && fgetc(file) == 'x');
    writer = _fsopen(fallback_path, "rb+", _SH_DENYNO);
    assert(writer && fclose(writer) == 0);
    assert(fclose(file) == 0 && remove(fallback_path) == 0);
    puts("runtime MSVC CRT helpers: PASS");
    return 0;
}
