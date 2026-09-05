#include <limits.h>
#include <stddef.h>
#include <stdio.h>

#include "../../../../src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic_policy.h"

static const unsigned int unary_inputs[] = {
    0U, 1U, 15U, 16U, 31U, 32U, 33U, 61U,
    1019U, 1020U, 1023U, UINT_MAX
};

static void dump_unary_rows(void) {
    size_t i;
    for (i = 0U; i < sizeof(unary_inputs) / sizeof(unary_inputs[0]); i++) {
        unsigned int x = unary_inputs[i];
        printf("P|limit|%u|%u\n", x, cosmos_gic_limit_words(x));
        printf("P|typer|%u|%u\n", x, cosmos_gic_words_from_typer(x));
        printf("P|target|%u|%u\n", x, cosmos_gic_target_for_word(x));
        printf("P|generation|%u|%u\n", x, cosmos_smp_next_generation(x));
        printf("P|ready|%u|%d\n", x, cosmos_smp_ready_observed(x));
        printf("P|poll|%u|%d\n", x, cosmos_smp_poll_allowed(x));
        printf("P|irq-id|%u|%u\n", x, cosmos_gic_irq_id(x));
        printf("P|spurious|%u|%d\n", x, cosmos_gic_irq_is_spurious(x));
        printf("P|disable-offset|%u|%u\n", x, cosmos_gic_disable_offset(x));
        printf("P|disable-mask|%u|%u\n", x, cosmos_gic_disable_mask(x));
        printf("P|byte-shift|%u|%u\n", x, cosmos_gic_byte_shift(x));
        printf("P|config-shift|%u|%u\n", x, cosmos_gic_config_shift(x));
        printf("P|priority-offset|%u|%u\n", x, cosmos_gic_priority_offset(x));
        printf("P|target-offset|%u|%u\n", x, cosmos_gic_target_offset(x));
        printf("P|config-offset|%u|%u\n", x, cosmos_gic_config_offset(x));
        printf("P|pcie-range|%u|%d\n", x, cosmos_gic_pcie_irq_in_range(x));
        printf("P|eoir|%u|%d\n", x, cosmos_gic_eoir_required(x));
    }
}

static void dump_multi_rows(void) {
    static const int results[] = {-1, 0, 1, 4};
    static const unsigned int release[][3] = {
        {0U, 0x00100000U, 0x00200000U},
        {1U, 0x00100000U, 0x00200000U},
        {0U, 0U, 0x00200000U},
        {0U, 0x00100000U, 0U},
        {0U, 0x00100002U, 0x00200000U},
        {0U, 0x00100000U, 0x00200004U}
    };
    static const unsigned int ack[][3] = {
        {3U, 41U, 41U}, {2U, 41U, 41U}, {3U, 40U, 41U}, {3U, UINT_MAX, UINT_MAX}
    };
    static const unsigned int values[][2] = {
        {0U, 0U}, {0U, 61U}, {UINT_MAX, 61U}, {0x12345678U, 1023U}
    };
    static const struct {
        unsigned int interrupt_id;
        int result;
    } quiesce[] = {{61U, 0}, {61U, 1}, {7U, 4}, {1020U, 4}};
    size_t i;

    for (i = 0U; i < sizeof(results) / sizeof(results[0]); i++) {
        printf("P|secondary|%d|%u\n", results[i], cosmos_smp_secondary_state(results[i]));
    }
    for (i = 0U; i < sizeof(release) / sizeof(release[0]); i++) {
        printf("P|release|%u|%u|%u|%d\n", release[i][0], release[i][1], release[i][2],
            cosmos_smp_release_request_valid(release[i][0], release[i][1], release[i][2]));
    }
    for (i = 0U; i < sizeof(ack) / sizeof(ack[0]); i++) {
        printf("P|ack|%u|%u|%u|%d\n", ack[i][0], ack[i][1], ack[i][2],
            cosmos_smp_ack_observed(ack[i][0], ack[i][1], ack[i][2]));
    }
    for (i = 0U; i < sizeof(values) / sizeof(values[0]); i++) {
        printf("P|priority-value|%u|%u|%u\n", values[i][0], values[i][1],
            cosmos_gic_priority_value(values[i][0], values[i][1]));
        printf("P|target-value|%u|%u|%u\n", values[i][0], values[i][1],
            cosmos_gic_target_cpu0_value(values[i][0], values[i][1]));
        printf("P|config-value|%u|%u|%u\n", values[i][0], values[i][1],
            cosmos_gic_level_config_value(values[i][0], values[i][1]));
    }
    for (i = 0U; i < sizeof(quiesce) / sizeof(quiesce[0]); i++) {
        printf("P|quiesce|%u|%d|%u\n", quiesce[i].interrupt_id, quiesce[i].result,
            cosmos_gic_quiesce_kind(quiesce[i].interrupt_id, quiesce[i].result));
    }
}

int main(void) {
    dump_unary_rows();
    dump_multi_rows();
    return 0;
}
