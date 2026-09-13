#include "../runtime.h"
#include "../runtime_hosted_safe_artifact_v1.h"
#include <assert.h>
#include <stdio.h>

int main(void) {
    assert(rt_hosted_safe_artifact_root_open_v1((const uint8_t*)"/", 1) == -1);
    assert(!rt_hosted_safe_artifact_root_close_v1(1));
    int64_t read_result = rt_hosted_safe_artifact_read_v1(1, (const uint8_t*)"x", 1, 1);
    assert(read_result == rt_value_nil() && read_result == 3);
    assert(rt_is_none(read_result) && !rt_is_some(read_result));
    assert(!rt_is_none(0));
    assert(rt_hosted_safe_artifact_publish_v1(1, (const uint8_t*)"x", 1, 0, 1) == -3);
    puts("PASS: unsupported hosted-safe-artifact provider fails closed");
    return 0;
}
