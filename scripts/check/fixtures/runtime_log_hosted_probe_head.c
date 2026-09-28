/* ASan regression probe for the hosted logger's snprintf/write boundary. */
#include "../../../src/runtime/startup/common/runtime_log_hosted.c"

int main(void) {
    rt_log_hosted_probe("device_write", INT64_MIN, 0, INT64_MIN);
    return 0;
}
