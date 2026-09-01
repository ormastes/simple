#ifndef SIMPLE_RUNTIME_STARTUP_ARGS_H
#define SIMPLE_RUNTIME_STARTUP_ARGS_H

#include <stdlib.h>
#include <string.h>

/* Remove runtime-owned extension options from the argv view published to
 * Simple code. The original argv remains untouched for the pre-main loader. */
static int simple_runtime_filter_startup_args(int argc, char **argv,
        char ***owned_argv, char ***visible_argv) {
    const char *option = "--startup-extension";
    size_t option_len = strlen(option);
    int source;
    int target = 0;
    int terminated = 0;
    char **filtered = (char**)malloc(((size_t)argc + 1) * sizeof(char*));
    if (!filtered) {
        *visible_argv = argv;
        return argc;
    }
    for (source = 0; source < argc; source++) {
        char *arg = argv[source];
        if (source > 0 && !terminated && strcmp(arg, "--") == 0) {
            terminated = 1;
        } else if (source > 0 && !terminated && strcmp(arg, option) == 0) {
            if (source + 1 < argc) source++;
            continue;
        } else if (source > 0 && !terminated &&
                strncmp(arg, option, option_len) == 0 &&
                arg[option_len] == '=') {
            continue;
        }
        filtered[target++] = arg;
    }
    filtered[target] = NULL;
    free(*owned_argv);
    *owned_argv = filtered;
    *visible_argv = filtered;
    return target;
}

#endif
