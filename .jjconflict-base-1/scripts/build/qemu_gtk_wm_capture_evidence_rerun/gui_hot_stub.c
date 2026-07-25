#include <stdint.h>
int64_t gui_dynlib_hot_probe_tick(int64_t batch_ptr, int64_t batch_len) {
    return batch_len > 0 ? batch_len : 0;
}
