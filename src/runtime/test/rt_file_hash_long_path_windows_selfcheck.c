/* Execute the real core-C hash entry on Windows paths beyond MAX_PATH.
 * Link genuine runtime translation units; no test runtime/FFI replacements.
 */
#ifdef _WIN32
#include "runtime.h"
#include "platform/runtime_win_long_path.h"
#include <direct.h>
#include <io.h>

static int failures;
#define CHECK(c, message) do { if (!(c)) { fprintf(stderr, "FAIL: %s\n", message); failures++; } } while (0)
#define PL(s) (const uint8_t*)(s), (uint64_t)strlen(s)

static int hash_is(const char* path, const char* expected) {
    int64_t actual = rt_file_hash_sha256(PL(path));
    return !rt_is_none(actual) && rt_string_len(actual) == 64 &&
        memcmp(rt_string_data(actual), expected, 64) == 0;
}

/* Fixture creation/cleanup uses the existing wide-path owner. Hashing always
 * calls the exported production rt_file_hash_sha256 above. */
static int make_dir(const char* path) {
    wchar_t* wide = rt_win_long_path_widen(path);
    if (!wide) return 0;
    int result = _wmkdir(wide);
    free(wide);
    return result == 0;
}

static int write_fixture(const char* path, const unsigned char* bytes, size_t size) {
    wchar_t* wide = rt_win_long_path_widen(path);
    if (!wide) return 0;
    FILE* file = _wfopen(wide, L"wb");
    free(wide);
    if (!file) return 0;
    int written = fwrite(bytes, 1, size, file) == size;
    return fclose(file) == 0 && written;
}

static void remove_fixture(const char* path, int directory) {
    wchar_t* wide = rt_win_long_path_widen(path);
    if (!wide) { CHECK(0, "widen cleanup path"); return; }
    int result = directory ? _wrmdir(wide) : _wunlink(wide);
    free(wide);
    CHECK(result == 0, "remove fixture");
}

int main(void) {
    static const unsigned char binary[] = {0, 1, 0x7f, 0x80, 0xff, 10, 13, 0};
    const char* binary_hash = "1dc70ef8cde6b98f0b511be620f0e95df1385dc17f6078c9d65f15f0791933d7";
    const char* empty_hash = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
    wchar_t temp_wide[32768];
    char temp[4096], root[1024], current[1024], dirs[24][1024];
    DWORD length = GetTempPathW(32768, temp_wide);
    if (!length || length >= 32768 ||
        !WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, temp_wide, -1,
            temp, sizeof(temp), NULL, NULL) || strlen(temp) > 180) return 2;
    snprintf(root, sizeof(root), "%ssimple-hash-%lu-%llu", temp,
        (unsigned long)GetCurrentProcessId(), (unsigned long long)GetTickCount64());
    if (!make_dir(root)) return 2;
    strcpy(current, root);
    int depth = 0;
    while (strlen(current) < 300 && depth < 24) {
        snprintf(dirs[depth], sizeof(dirs[depth]), "%s/segment-%02d-abcdefghijklmnopqrstuvwx", current, depth);
        if (!make_dir(dirs[depth])) return 2;
        strcpy(current, dirs[depth++]);
    }
    char short_binary[1024], short_empty[1024], short_missing[1024];
    char long_binary[1024], long_empty[1024], long_missing[1024];
    snprintf(short_binary, sizeof(short_binary), "%s/binary.dat", root);
    snprintf(short_empty, sizeof(short_empty), "%s/empty.dat", root);
    snprintf(short_missing, sizeof(short_missing), "%s/missing.dat", root);
    snprintf(long_binary, sizeof(long_binary), "%s/binary-\xc3\xa9.dat", current);
    snprintf(long_empty, sizeof(long_empty), "%s/empty.dat", current);
    snprintf(long_missing, sizeof(long_missing), "%s/missing.dat", current);
    CHECK(strlen(short_binary) < 260 && strlen(long_binary) > 260, "short and long fixture lengths");
    CHECK(write_fixture(short_binary, binary, sizeof(binary)), "write short binary");
    CHECK(write_fixture(long_binary, binary, sizeof(binary)), "write long binary");
    CHECK(write_fixture(short_empty, binary, 0), "write short empty file");
    CHECK(write_fixture(long_empty, binary, 0), "write long empty file");
    CHECK(hash_is(short_binary, binary_hash), "short binary hash including NUL and non-ASCII bytes");
    CHECK(hash_is(long_binary, binary_hash), "long UTF-8 path has identical binary hash");
    CHECK(hash_is(short_empty, empty_hash), "short empty file SHA256");
    CHECK(hash_is(long_empty, empty_hash), "long empty file SHA256");
    CHECK(rt_is_none(rt_file_hash_sha256(PL(short_missing))), "short missing file returns nil");
    CHECK(rt_is_none(rt_file_hash_sha256(PL(long_missing))), "long missing file returns nil");
    const char invalid_utf8[] = {(char)0xff, 0};
    CHECK(rt_is_none(rt_file_hash_sha256(PL(invalid_utf8))), "invalid UTF-8 path returns nil");
    remove_fixture(short_binary, 0);
    remove_fixture(short_empty, 0);
    remove_fixture(long_binary, 0);
    remove_fixture(long_empty, 0);
    while (depth) remove_fixture(dirs[--depth], 1);
    remove_fixture(root, 1);
    if (!failures) puts("PASS: Windows SHA256 short/long binary, empty, missing files");
    return failures ? 1 : 0;
}
#endif /* _WIN32 */
