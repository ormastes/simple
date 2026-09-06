/* Behavioural probe for two native-runtime producer contracts.
 *
 * Built and run by scripts/check/check-native-text-abi-and-binary-read.shs.
 * It is a C harness on purpose: both contracts are properties of the C runtime
 * that the compiler's `text` extern ABI depends on, and a Simple-level probe
 * would need a deployed compiler to observe them.
 *
 * Contract 1 -- text-literal extern ABI.
 *   The compiler lowers a `text` extern argument to the PAIR
 *   (rt_string_data(v), rt_string_len(v)). A `text` LITERAL is a bare pointer
 *   into .rodata, not a heap RtCoreString. rt_string_len already returned
 *   strlen() for that case; rt_string_data returned NULL, and the resulting
 *   (NULL, len) pair is rejected by rt_text_arg_to_path, so every text-ABI
 *   extern called with a literal failed.
 *
 * Contract 2 -- binary file read length.
 *   rt_file_read_text must report the file's BYTE COUNT. It used to strlen()
 *   the buffer, so content stopped at the first NUL. FileFingerprint.from_file
 *   hashes that text, so an object file's fingerprint became a constant.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

extern const uint8_t* rt_string_data(int64_t string);
extern int64_t rt_string_len(int64_t string);
extern int64_t rt_file_read_text(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_file_size(const uint8_t* path_ptr, uint64_t path_len);

static int failures = 0;
static int checked = 0;

static void report(const char* name, int ok, const char* detail) {
    checked++;
    if (!ok) {
        failures++;
        printf("FAILED-CHECK %s: %s\n", name, detail);
    } else {
        printf("ok %s: %s\n", name, detail);
    }
}

int main(int argc, char** argv) {
    char detail[512];
    if (argc < 2) {
        printf("ERROR — nothing was checked (no scratch path argument)\n");
        return 2;
    }

    /* Contract 1: a .rodata literal must decode to a usable (ptr, len) pair. */
    static const char literal[] = "/etc/hostname";
    int64_t as_value = (int64_t)(uintptr_t)literal;
    const uint8_t* data = rt_string_data(as_value);
    int64_t len = rt_string_len(as_value);
    snprintf(detail, sizeof(detail),
             "rt_string_data(literal)=%p rt_string_len(literal)=%lld",
             (const void*)data, (long long)len);
    report("text-literal-decodes", data != NULL && len == 13, detail);

    if (data != NULL) {
        snprintf(detail, sizeof(detail), "bytes='%.*s'", (int)len, (const char*)data);
        report("text-literal-bytes", len == 13 && memcmp(data, literal, 13) == 0, detail);
    } else {
        report("text-literal-bytes", 0, "rt_string_data returned NULL");
    }

    /* Contract 2: a file with an embedded NUL must read back at full length. */
    const char* path = argv[1];
    static const char payload[8] = { 0x7f, 'E', 'L', 'F', 0x02, 0x00, 0x00, 'Z' };
    FILE* f = fopen(path, "wb");
    if (!f) {
        printf("ERROR — nothing was checked (cannot write scratch file %s)\n", path);
        return 2;
    }
    fwrite(payload, 1, sizeof(payload), f);
    fclose(f);

    uint64_t path_len = (uint64_t)strlen(path);
    int64_t size = rt_file_size((const uint8_t*)path, path_len);
    snprintf(detail, sizeof(detail), "rt_file_size=%lld expected=8", (long long)size);
    report("binary-file-size", size == 8, detail);

    int64_t text = rt_file_read_text((const uint8_t*)path, path_len);
    if (text == 3) {
        report("binary-read-length", 0, "rt_file_read_text returned nil for a readable file");
    } else {
        int64_t text_len = rt_string_len(text);
        snprintf(detail, sizeof(detail),
                 "rt_file_read_text text_len=%lld expected=8 (pre-fix strlen truncation stops at the NUL and gives 5)",
                 (long long)text_len);
        report("binary-read-length", text_len == 8, detail);
    }

    if (checked == 0) {
        printf("ERROR — nothing was checked (0 contracts evaluated)\n");
        return 2;
    }
    if (failures != 0) {
        printf("FAIL — %d contract(s) checked, %d failed\n", checked, failures);
        return 1;
    }
    printf("PASS — %d contract(s) checked, 0 failed\n", checked);
    return 0;
}
