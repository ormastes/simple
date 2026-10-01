/* Direct group charge at a compiler phase boundary. This is the same
 * JobObject/cgroup metric as the broker's enforced process-tree budget,
 * distinct from the compiler process's resident working set. */
#ifndef SIMPLE_RUNTIME_GROUP_SELF_CHARGE_H
#define SIMPLE_RUNTIME_GROUP_SELF_CHARGE_H

#include <stdint.h>
#include <stddef.h>
#include <limits.h>
#if defined(__linux__)
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/vfs.h>
#include <unistd.h>
#include <linux/magic.h>
#endif

#if defined(__linux__)
static inline int rt_group_charge_read_at(int dir, const char* name, int64_t* value) {
    int fd = openat(dir, name, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    char data[64];
    ssize_t n = read(fd, data, sizeof(data) - 1);
    int closed = close(fd);
    if (n <= 0 || n >= (ssize_t)sizeof(data) || closed != 0) return 0;
    data[n] = '\0';
    if (data[0] < '0' || data[0] > '9') return 0;
    uint64_t parsed = 0;
    size_t i = 0;
    for (; data[i] >= '0' && data[i] <= '9'; ++i) {
        uint64_t digit = (uint64_t)(data[i] - '0');
        if (parsed > ((uint64_t)INT64_MAX - digit) / 10) return 0;
        parsed = parsed * 10 + digit;
    }
    if (data[i] != '\0' && !(data[i] == '\n' && data[i + 1] == '\0')) return 0;
    *value = (int64_t)parsed;
    return 1;
}
#endif

static inline int rt_group_self_charge_snapshot(int64_t* current, int64_t* peak) {
    if (!current || !peak) return 0;
    *current = -1; *peak = -1;
#if defined(__linux__)
    FILE* file = fopen("/proc/self/cgroup", "re");
    if (!file) return 0;
    char line[4096], path[4096];
    int found = 0;
    while (fgets(line, sizeof(line), file)) {
        if (strncmp(line, "0::/", 4) != 0) continue;
        size_t n = strcspn(line + 3, "\r\n");
        if (n == 0 || n > sizeof(path) - 15) break;
        memcpy(path, "/sys/fs/cgroup", 14);
        memcpy(path + 14, line + 3, n);
        path[14 + n] = '\0';
        found = 1;
        break;
    }
    fclose(file);
    if (!found) return 0;
    size_t path_len = strlen(path);
    if (strstr(path, "/../") || strstr(path, "/./") ||
            strcmp(path + path_len - 3, "/..") == 0 ||
            strcmp(path + path_len - 2, "/.") == 0) return 0;
    int dir = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (dir < 0) return 0;
    struct statfs fs;
    int valid = fstatfs(dir, &fs) == 0 &&
        (unsigned long)fs.f_type == CGROUP2_SUPER_MAGIC &&
        rt_group_charge_read_at(dir, "memory.current", current) &&
        rt_group_charge_read_at(dir, "memory.peak", peak) &&
        *peak >= *current;
    close(dir);
    if (!valid) { *current = -1; *peak = -1; }
    return valid;
#else
    /* Win32's public extended-limit row exposes a lifetime Job peak and
     * single-process peak, but no current aggregate charge. Fail closed. */
    return 0;
#endif
}

#endif
