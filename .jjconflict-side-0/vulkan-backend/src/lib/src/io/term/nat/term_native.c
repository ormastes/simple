#include <string.h>

long term_add(long a, long b) {
    return a + b;
}

long term_strlen(const char* s) {
    if (!s) {
        return -1;
    }
    return (long)strlen(s);
}
