#include <assert.h>
#include <stdio.h>

#include "cosmos_hal.h"
#include "cosmos_storage.h"

int main(void) {
    assert(COSMOS_IS_QEMU);
    assert(cosmos_storage_init() == COSMOS_UNAVAILABLE);
    assert(cosmos_storage_factory_initialize_erased() == COSMOS_UNAVAILABLE);
    assert(cosmos_storage_poll() == COSMOS_UNAVAILABLE);
    puts("cosmos storage QEMU fail-closed startup: PASS");
    return 0;
}
