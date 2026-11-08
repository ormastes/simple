#include "runtime_sosix_directory_roots_v1.h"
#define CHECK(x) do { if (!(x)) { fprintf(stderr, "failed line %d: %s\n", __LINE__, #x); return 1; } } while (0)
int main(int argc, char **argv) {
    CHECK(argc == 2);
    char shared[RT_SDR_PATH_V1], private_root[RT_SDR_PATH_V1];
    CHECK(snprintf(shared, sizeof shared, "%s/shared", argv[1]) > 0);
    CHECK(snprintf(private_root, sizeof private_root, "%s/private/child", argv[1]) > 0);
    wchar_t wide[RT_SDR_PATH_V1];
    CHECK(MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, shared, -1, wide, RT_SDR_PATH_V1));
    CHECK(CreateDirectoryW(wide, NULL));
    int64_t token = rt_sdr_open_v1(shared, private_root);
    CHECK(token > 0);
    uint64_t snapshot[RT_SDR_WORDS_V1];
    CHECK(rt_sdr_snapshot_v1(token, snapshot, sizeof snapshot) == 0);
    CHECK(snapshot[6] == (uint64_t)token);
    CHECK(rt_sdr_revalidate_v1(token) == 0);
    CHECK(rt_sdr_check_v1(shared, private_root) == 0);
    CHECK(rt_sdr_check_v1(shared, private_root) == 0);
    CHECK(rt_sdr_close_v1(token) == 0);
    CHECK(rt_sdr_check_v1(shared, shared) == RT_SDR_OVERLAP_V1);
    char too_long[RT_SDR_PATH_V1 + 1], canonical[RT_SDR_PATH_V1];
    memset(too_long, 'a', sizeof too_long); too_long[sizeof too_long - 1] = 0;
    CHECK(rt_sdr_path_v1(too_long, canonical) == -ENAMETOOLONG);
    CHECK(rt_sdr_check_v1(shared, too_long) == -ENAMETOOLONG);
    /* A maximum accepted canonical path preserves its trailing NUL. */
    too_long[0] = 'C'; too_long[1] = ':'; too_long[2] = '/';
    too_long[RT_SDR_PATH_V1 - 1] = 0;
    CHECK(rt_sdr_path_v1(too_long, canonical) == 0);
    CHECK(strlen(canonical) == RT_SDR_PATH_V1 - 1);
    puts("PASS sosix directory CRT copies: creation, cache, overlap, bounds");
    return 0;
}
