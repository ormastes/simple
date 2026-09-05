#include "runtime_startup_args.h"
#include <stdio.h>

static int check(int argc, char **argv, int expected_argc,
        const char *expected_1, const char *expected_2) {
    char **owned = NULL;
    char **visible = NULL;
    int count = simple_runtime_filter_startup_args(argc, argv, &owned, &visible);
    int ok = count == expected_argc;
    if (ok && expected_1) ok = strcmp(visible[1], expected_1) == 0;
    if (ok && expected_2) ok = strcmp(visible[2], expected_2) == 0;
    free(owned);
    return ok;
}

int main(void) {
    char *equals[] = {"app", "--startup-extension=a.so", "user", NULL};
    char *split[] = {"app", "--startup-extension", "a.so", "user", NULL};
    char *repeated[] = {"app", "--startup-extension=a.so",
        "--startup-extension", "b.so", "user", NULL};
    char *terminated[] = {"app", "--", "--startup-extension=a.so", NULL};
    if (!check(3, equals, 2, "user", NULL)) return 1;
    if (!check(4, split, 2, "user", NULL)) return 2;
    if (!check(5, repeated, 2, "user", NULL)) return 3;
    if (!check(3, terminated, 3, "--", "--startup-extension=a.so")) return 4;
    puts("PASS startup extension argv filtering: 4 cases");
    return 0;
}
