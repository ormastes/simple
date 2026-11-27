/* Private: argv construction shared by the POSIX spawn entry points
 * (runtime_legacy_core.c, runtime_process_tree.c). Not an exported API. */
#ifndef RUNTIME_EXEC_ARGV_PRIVATE_H
#define RUNTIME_EXEC_ARGV_PRIVATE_H

#include <stdint.h>
#include <stdlib.h>

/* argv = { cmd, args[0..arg_count-1], NULL } as a shallow calloc'd array the
 * caller frees. Returns NULL with calloc's errno (ENOMEM) on failure. The
 * caller validates cmd/args/arg_count (arg_count >= 0) and must call this
 * BEFORE fork: a multithreaded parent may hold the allocator lock. */
static inline char** spawn_argv_build(const char* cmd, const char** args,
                                      int64_t arg_count) {
    char** argv = (char**)calloc((size_t)arg_count + 2, sizeof(char*));
    if (!argv) return NULL;
    argv[0] = (char*)cmd;
    for (int64_t i = 0; i < arg_count; i++) argv[i + 1] = (char*)args[i];
    return argv;
}

#endif
