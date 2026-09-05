/* Uninstrumented event driver for rv32_hal_io_event_ref.c. */
#include <stdint.h>
#include <stdio.h>

int rv32_smp_should_wait_ref(uint32_t, uint32_t, uint32_t, uint32_t);
int64_t rv32_optional_firmware_default_ref(void);

int main(void) {
    const int both_open = rv32_smp_should_wait_ref(2, 10, 3, 100);
    const int target_reached = rv32_smp_should_wait_ref(3, 10, 3, 100);
    const int budget_exhausted = rv32_smp_should_wait_ref(2, 100, 3, 100);
    const int64_t optional_default = rv32_optional_firmware_default_ref();

    printf("event|case=both-open|wait=%d\n", both_open);
    printf("event|case=target-reached|wait=%d\n", target_reached);
    printf("event|case=budget-exhausted|wait=%d\n", budget_exhausted);
    printf("event|case=optional-firmware-default|result=%lld\n",
           (long long)optional_default);

    return (both_open != 1) | (target_reached != 0) |
           (budget_exhausted != 0) | (optional_default != 0);
}
