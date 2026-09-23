#include "runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define RT_NIL_VALUE 3

#if !defined(_WIN32)
#include <dlfcn.h>
#endif

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (strcmp(argv[1], "invalid-tag") == 0) {
        (void)rt_gui_present_html(RT_NIL_VALUE);
        return 3; /* The provider boundary must exit 70 first. */
    }
    if (strcmp(argv[1], "present") != 0) return 2;

    int64_t html = rt_string_new((const uint8_t *)"<p>ok</p>", 9);
    rt_gui_present_html(html);
    rt_gui_present_html(html);
#if !defined(_WIN32)
    const char *path = getenv("SIMPLE_GUI_HTML_PROVIDER_PATH");
    if (!path) return 5;
    void *library = dlopen(path, RTLD_NOLOAD | RTLD_NOW);
    if (!library) return 6;
    union { void *symbol; int64_t (*call)(void); } counts;
    counts.symbol = dlsym(library, "simple_gui_test_call_counts_v1");
    if (!counts.call || counts.call() != 102) {
        fprintf(stderr, "expected one ABI lookup and two present calls\n");
        return 7;
    }
    dlclose(library);
#endif
    return 0;
}
