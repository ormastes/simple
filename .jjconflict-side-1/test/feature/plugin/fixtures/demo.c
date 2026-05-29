/* AC-1 demo plugin fixture.
 * WFFI calling convention: int64_t fn(int64_t* args, int64_t nargs).
 * simple_demo_add returns args[0] + args[1]. */

#include <stdint.h>

int64_t simple_demo_add(int64_t* args, int64_t nargs) {
    if (nargs < 2) {
        return 0;
    }
    return args[0] + args[1];
}
