#include <stdint.h>
#include <stdio.h>
extern int64_t thread_local_boundary_probe(void);
int main(void) {
    int64_t result = thread_local_boundary_probe();
    if (result != 0) {
        fprintf(stderr, "Simple TLS boundary failure: %lld\n", (long long)result);
        return 1;
    }
    puts("Simple TLS boundary: PASS");
    return 0;
}
