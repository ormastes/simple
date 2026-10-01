#include <stddef.h>

/* Deliberate foreign-provider sabotage: success with a null required output. */
int rt_sffi_acceptance_create(void **out_handle) {
    if (out_handle != NULL) {
        *out_handle = NULL;
    }
    return 0;
}
