/* ABI adapter/ownership fixture, not authenticated provider admission. */
#import <Cocoa/Cocoa.h>
#include <assert.h>
#define SIMPLE_COCOA_PROVIDER_ONLY
#include "../../../src/runtime/hosted_cocoa.c"

int main(void) {
    assert(raw_title_to_cstr(NULL, 1) == NULL);
    assert(raw_title_to_cstr("x", -1) == NULL);
    assert(raw_title_to_cstr("x", COCOA_TITLE_MAX_BYTES + 1) == NULL);
    assert(raw_title_to_cstr("a\0b", 3) == NULL);
    char bytes[] = {'b', 'o', 'u', 'n', 'd', 'X'};
    char *copy = raw_title_to_cstr(bytes, 5);
    assert(copy && !strcmp(copy, "bound"));
    bytes[0] = 'z';
    assert(!strcmp(copy, "bound"));
    free(copy);
    copy = raw_title_to_cstr(NULL, 0);
    assert(copy && !strcmp(copy, "untitled"));
    free(copy);
    puts("Cocoa raw title bounded copy: PASS");
    return 0;
}
