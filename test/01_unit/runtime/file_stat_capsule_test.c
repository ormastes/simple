#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int64_t rt_stat_open(const char* path);
int64_t rt_file_stat_size(int64_t handle);
int64_t rt_file_stat_mtime(int64_t handle);
int rt_file_stat_is_dir(int64_t handle);
int rt_file_stat_is_file(int64_t handle);
void rt_file_stat_free(int64_t handle);

int main(int argc, char** argv) {
    if (argc != 4) return 90;
    int64_t expected_mtime = strtoll(argv[3], NULL, 10);

    if (rt_stat_open(NULL) != 0) return 91;
    if (rt_stat_open(argv[2]) != 0) return 92;
    if (rt_file_stat_mtime(0) != 0) return 93;
    if (rt_file_stat_size(0) != 0) return 94;
    if (rt_file_stat_is_dir(0) != 0) return 95;
    if (rt_file_stat_is_file(0) != 0) return 96;
    rt_file_stat_free(0);

    int64_t file_handle = rt_stat_open(argv[1]);
    if (!file_handle) return 97;
    if (rt_file_stat_size(file_handle) != 4) return 98;
    if (rt_file_stat_mtime(file_handle) != expected_mtime) return 99;
    if (!rt_file_stat_is_file(file_handle)) return 100;
    if (rt_file_stat_is_dir(file_handle)) return 101;
    rt_file_stat_free(file_handle);

    int64_t dir_handle = rt_stat_open(".");
    if (!dir_handle) return 102;
    if (!rt_file_stat_is_dir(dir_handle)) return 103;
    if (rt_file_stat_is_file(dir_handle)) return 104;
    rt_file_stat_free(dir_handle);

    puts("file stat capsule: PASS");
    return 0;
}
