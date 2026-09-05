#ifndef SIMPLEOS_ARM_FS_ROOT_DIRENT_H
#define SIMPLEOS_ARM_FS_ROOT_DIRENT_H

#include <stddef.h>
#include <stdint.h>

struct arm_fs_root_dirent_metadata_v1 {
    uint32_t first_cluster;
    uint32_t size;
};

static int arm_fs_root_dirent_metadata(const uint8_t *entry, size_t available,
                                       uint32_t route,
                                       struct arm_fs_root_dirent_metadata_v1 *out)
{
    static const uint8_t names[4][11] = {
        {'Q','E','M','U','N','O','N','C','T','X','T'},
        {'F','S','E','X','E','C',' ',' ','E','L','F'},
        {'S','I','M','P','L','E',' ',' ','E','L','F'},
        {'H','E','L','L','O',' ',' ',' ','S','P','L'}
    };
    if (!entry || available < 32 || route < 1 || route > 4 ||
        entry[0] == 0 || entry[0] == 0xe5 || entry[11] == 0x0f) return 0;
    for (size_t i = 0; i < 11; ++i)
        if (entry[i] != names[route - 1][i]) return 0;
    if (out) {
        out->first_cluster = ((uint32_t)entry[20] | ((uint32_t)entry[21] << 8)) << 16;
        out->first_cluster |= (uint32_t)entry[26] | ((uint32_t)entry[27] << 8);
        out->size = (uint32_t)entry[28] | ((uint32_t)entry[29] << 8) |
                    ((uint32_t)entry[30] << 16) | ((uint32_t)entry[31] << 24);
    }
    return 1;
}

#endif
