#include "../runtime_linux_cgroup_events_private.h"
#include <assert.h>
#include <string.h>
#include <stdio.h>
static void check(const char *s, int expected, int value) {
    int actual = -1;
    assert(rt_lg_parse_populated(s, strlen(s), &actual) == expected);
    if (expected) assert(actual == value);
    else assert(actual == -1);
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
    const char embedded[] = "populated 0\n\0populated 1\n";
    int value = -1; assert(!rt_lg_parse_populated(embedded, sizeof(embedded) - 1, &value));
    assert(value == -1);
    puts("cgroup.events parser selfcheck passed");
}
