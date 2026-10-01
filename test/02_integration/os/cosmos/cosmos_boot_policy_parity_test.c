#include <assert.h>
#include <limits.h>
#include <stdio.h>

#include "cosmos_boot_policy_oracle.h"
#ifdef COSMOS_BOOT_POLICY_COVERAGE_ONLY
#define cosmos_boot_policy_uart_should_attempt cosmos_boot_oracle_uart_should_attempt
#define cosmos_boot_policy_uart_next_enabled cosmos_boot_oracle_uart_next_enabled
#define cosmos_boot_policy_exception_should_capture cosmos_boot_oracle_exception_should_capture
#define cosmos_boot_policy_exception_message_kind cosmos_boot_oracle_exception_message_kind
#define cosmos_boot_policy_status_kind cosmos_boot_oracle_status_kind
#define cosmos_boot_policy_stage_allowed cosmos_boot_oracle_stage_allowed
#define cosmos_boot_policy_software_ready cosmos_boot_oracle_software_ready
#define cosmos_boot_policy_selftest cosmos_boot_oracle_selftest
#define cosmos_boot_policy_handoff_allows_devices cosmos_boot_oracle_handoff_allows_devices
#define cosmos_boot_policy_storage_init_allowed cosmos_boot_oracle_storage_init_allowed
#define cosmos_boot_policy_secondary_release_allowed cosmos_boot_oracle_secondary_release_allowed
#define cosmos_boot_policy_terminal_verdict cosmos_boot_oracle_terminal_verdict
#define cosmos_boot_policy_irq_enable_allowed cosmos_boot_oracle_irq_enable_allowed
#define cosmos_boot_policy_storage_poll_allowed cosmos_boot_oracle_storage_poll_allowed
#define cosmos_boot_policy_storage_poll_action cosmos_boot_oracle_storage_poll_action
#else
#include "cosmos_boot_policy.h"
#endif

static unsigned int parity_rows;

#define CHECK_EQ(actual, expected) do { assert((actual) == (expected)); parity_rows++; } while (0)

static void exercise_unary(void) {
    static const int statuses[] = {-1, 0, 1, 2, 3, 4, 5, 6, INT_MAX};
    static const unsigned int states[] = {0U, 1U, 0x434C4541U, 0x41435449U};
    unsigned int i;
    for (i = 0U; i < sizeof(statuses) / sizeof(statuses[0]); i++) {
        int status = statuses[i];
        CHECK_EQ(cosmos_boot_policy_status_kind(status),
            cosmos_boot_oracle_status_kind(status));
        CHECK_EQ(cosmos_boot_policy_stage_allowed(status),
            cosmos_boot_oracle_stage_allowed(status));
        CHECK_EQ(cosmos_boot_policy_irq_enable_allowed(status),
            cosmos_boot_oracle_irq_enable_allowed(status));
        CHECK_EQ(cosmos_boot_policy_storage_poll_allowed(status),
            cosmos_boot_oracle_storage_poll_allowed(status));
        CHECK_EQ(cosmos_boot_policy_storage_poll_action(status),
            cosmos_boot_oracle_storage_poll_action(status));
    }
    for (i = 0U; i < sizeof(states) / sizeof(states[0]); i++) {
        CHECK_EQ(cosmos_boot_policy_exception_should_capture(states[i]),
            cosmos_boot_oracle_exception_should_capture(states[i]));
        CHECK_EQ(cosmos_boot_policy_exception_message_kind(states[i]),
            cosmos_boot_oracle_exception_message_kind(states[i]));
    }
}

static void exercise_uart(void) {
    static const unsigned int masks[] = {0U, 1U, 2U, 3U, UINT_MAX};
    static const unsigned int bits[] = {1U, 2U, 4U};
    static const int statuses[] = {0, 3};
    unsigned int a;
    unsigned int b;
    unsigned int c;
    for (a = 0U; a < sizeof(masks) / sizeof(masks[0]); a++) {
        for (b = 0U; b < sizeof(bits) / sizeof(bits[0]); b++) {
            for (c = 0U; c < sizeof(statuses) / sizeof(statuses[0]); c++) {
                CHECK_EQ(cosmos_boot_policy_uart_should_attempt(masks[a], bits[b]),
                    cosmos_boot_oracle_uart_should_attempt(masks[a], bits[b]));
                CHECK_EQ(cosmos_boot_policy_uart_next_enabled(
                        masks[a], bits[b], statuses[c]),
                    cosmos_boot_oracle_uart_next_enabled(
                        masks[a], bits[b], statuses[c]));
            }
        }
    }
}

static void exercise_combinations(void) {
    static const int bits[] = {0, 1};
    unsigned int a;
    unsigned int b;
    unsigned int c;
    unsigned int d;
    unsigned int e;
    unsigned int f;
    unsigned int g;
    for (a = 0U; a < 2U; a++) {
        CHECK_EQ(cosmos_boot_policy_selftest(bits[a]),
            cosmos_boot_oracle_selftest(bits[a]));
        for (b = 0U; b < 2U; b++) {
            CHECK_EQ(cosmos_boot_policy_secondary_release_allowed(bits[a], bits[b]),
                cosmos_boot_oracle_secondary_release_allowed(bits[a], bits[b]));
            for (c = 0U; c < 2U; c++) {
                CHECK_EQ(cosmos_boot_policy_handoff_allows_devices(
                        bits[a], bits[b], bits[c]),
                    cosmos_boot_oracle_handoff_allows_devices(
                        bits[a], bits[b], bits[c]));
                CHECK_EQ(cosmos_boot_policy_storage_init_allowed(bits[b], bits[c]),
                    cosmos_boot_oracle_storage_init_allowed(bits[b], bits[c]));
                for (d = 0U; d < 2U; d++) {
                    CHECK_EQ(cosmos_boot_policy_software_ready(
                            bits[a], bits[b], bits[c], bits[d]),
                        cosmos_boot_oracle_software_ready(
                            bits[a], bits[b], bits[c], bits[d]));
                    for (e = 0U; e < 2U; e++) {
                        for (f = 0U; f < 2U; f++) {
                            for (g = 0U; g < 2U; g++) {
                                CHECK_EQ(cosmos_boot_policy_terminal_verdict(
                                        bits[a], bits[b], bits[c], bits[d],
                                        bits[e], bits[f], bits[g]),
                                    cosmos_boot_oracle_terminal_verdict(
                                        bits[a], bits[b], bits[c], bits[d],
                                        bits[e], bits[f], bits[g]));
                            }
                        }
                    }
                }
            }
        }
    }
}

int main(void) {
#ifndef COSMOS_BOOT_POLICY_COVERAGE_ONLY
    cosmos_boot_policy_coverage_reset();
#endif
    exercise_unary();
    exercise_uart();
    exercise_combinations();
    assert(parity_rows == 279U);
#ifndef COSMOS_BOOT_POLICY_COVERAGE_ONLY
    assert(cosmos_boot_policy_coverage_decisions() == 38U);
    assert(cosmos_boot_policy_coverage_low() ==
        cosmos_boot_policy_coverage_required_low());
    assert(cosmos_boot_policy_coverage_high() ==
        cosmos_boot_policy_coverage_required_high());
#endif
    printf("STATUS: PASS cosmos boot policy parity rows=%u\n", parity_rows);
    return 0;
}
