#include "../runtime_linux_cgroup_events_private.h"
#include <string.h>
#include <stdio.h>
static int failures;
static int checks;
static void check(const char *s, int expected, int value) {
    int actual = -1;
    int result = rt_lg_parse_populated(s, strlen(s), &actual);
    checks++;
    if (result != expected || actual != (expected ? value : -1)) {
        fprintf(stderr, "FAIL fixture %d: accepted=%d value=%d\n", checks, result, actual);
        failures++;
    }
}
int main(void) {
    check("populated 0\nfrozen 0\n", 1, 0);
    check("frozen 0\npopulated 1\n", 1, 1);
    check("populated 0garbage\n", 0, 0);
    check("populated 0\npopulated 1\n", 0, 0);
    check("populated 0\npopulated 0\n", 0, 0);
    check("populated 2\n", 0, 0);
    check("populated\npopulated 0\n", 0, 0);
    check("populated\t0\npopulated 0\n", 0, 0);
    check("populated \n", 0, 0);
    check("frozen 0\n", 0, 0);
    check("unpopulated 0\n", 0, 0);
    check("populated 0\ngarbage", 0, 0);
    check("populated 0\nunknown 3\n", 0, 0);
    check("populated 0\npopulated\r1\n", 0, 0);
    check("populated 0", 0, 0);
    check("populated 0\nfrozen 0", 0, 0);
    check("populated 0\nfrozen 0\nfrozen 1\n", 0, 0);
    check("populated 0\nfrozen 2\n", 0, 0);
    check("populated 0\nfrozen 0junk\n", 0, 0);
    check("populated 0\n\n", 0, 0);
    check(" populated 0\n", 0, 0);
    check("populated 1\nfrozen 1\n", 1, 1);
    check("populated 0\n", 1, 0);
    check("", 0, 0);
    const char embedded[] = "populated 0\n\0populated 1\n";
    int value = -1;
    checks++;
    if (rt_lg_parse_populated(embedded, sizeof(embedded) - 1, &value) || value != -1) failures++;
    checks++;
    if (rt_lg_parse_populated(NULL, 0, &value) || value != -1) failures++;
    checks++;
    if (rt_lg_parse_populated("populated 0\n", 12, NULL)) failures++;
    printf("cgroup.events parser: %d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
