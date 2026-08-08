#include <assert.h>
#include <limits.h>
#include <stdio.h>

#include "../../../../src/os/kernel/arch/arm32/cosmos/cosmos_profile_openssd2_8ch8way_v300.h"

#define COSMOS_POLL_LIMIT 1000000U
#define COSMOS_OK 0
#define COSMOS_UNAVAILABLE 1
#define COSMOS_HW_ERROR 4
#define COSMOS_SMP_EMPTY 0U
#define COSMOS_SMP_READY 1U
#define COSMOS_SMP_RELEASED 2U
#define COSMOS_SMP_ACKED 3U
#define COSMOS_SMP_CANCELLED 4U
#define COSMOS_GIC_QUIESCE_NONE 0U
#define COSMOS_GIC_QUIESCE_CPU 1U
#define COSMOS_GIC_QUIESCE_LINE 2U

unsigned int cosmos_contract_cache_way_shift(unsigned int ways);
unsigned int cosmos_contract_cache_setway_operand(
    unsigned int level,
    unsigned int way,
    unsigned int set,
    unsigned int line_shift,
    unsigned int way_shift
);
unsigned int cosmos_contract_ttbr0_value(unsigned int table_address);
unsigned int cosmos_contract_scu_invalidate_mask(unsigned int cpu_id);
int cosmos_contract_cache_enable_allowed(unsigned int scu_control, unsigned int actlr);
int cosmos_contract_mmu_poll_allowed(unsigned int poll);
unsigned int cosmos_contract_l1_descriptor(
    unsigned int address,
    unsigned int firmware_l2_table_address,
    unsigned int ocm_l2_table_address
);
unsigned int cosmos_contract_firmware_l2_descriptor(
    unsigned int address,
    unsigned int rx_end
);
int cosmos_contract_l2_descriptor_executable(unsigned int descriptor);
int cosmos_contract_l2_descriptor_priv_writable(unsigned int descriptor);
int cosmos_contract_l2_descriptor_write_execute(unsigned int descriptor);
unsigned int cosmos_contract_ocm_l2_descriptor(unsigned int address);

unsigned int cosmos_contract_gic_limit_words(unsigned int words);
unsigned int cosmos_contract_gic_words_from_typer(unsigned int typer);
unsigned int cosmos_contract_gic_target_for_word(unsigned int word);
unsigned int cosmos_contract_smp_next_generation(unsigned int generation);
int cosmos_contract_smp_release_request_valid(
    unsigned int cpu_id,
    unsigned int entry,
    unsigned int stack_top
);
int cosmos_contract_smp_ready_observed(unsigned int state);
unsigned int cosmos_contract_smp_secondary_state(int result);
int cosmos_contract_smp_ack_observed(
    unsigned int state,
    unsigned int ack,
    unsigned int generation
);
int cosmos_contract_smp_poll_allowed(unsigned int poll);
unsigned int cosmos_contract_gic_pcie_irq_id(void);
unsigned int cosmos_contract_gic_pcie_enable_offset(void);
unsigned int cosmos_contract_gic_pcie_disable_offset(void);
unsigned int cosmos_contract_gic_pcie_mask(void);
unsigned int cosmos_contract_gic_pcie_priority_offset(void);
unsigned int cosmos_contract_gic_pcie_priority_value(unsigned int current);
unsigned int cosmos_contract_gic_pcie_target_offset(void);
unsigned int cosmos_contract_gic_pcie_target_value(unsigned int current);
unsigned int cosmos_contract_gic_pcie_config_offset(void);
unsigned int cosmos_contract_gic_pcie_level_config_value(unsigned int current);
int cosmos_contract_gic_pcie_irq_in_range(unsigned int words);
int cosmos_contract_gic_eoir_required(unsigned int interrupt_id);
unsigned int cosmos_contract_gic_quiesce_kind(
    unsigned int interrupt_id,
    int handler_result
);

static void test_cache_contract(void) {
    unsigned int way_shift = cosmos_contract_cache_way_shift(4U);
    unsigned int firmware_l2 = 0x12345000U;
    unsigned int ocm_l2 = 0x12345678U;
    unsigned int rx_end = 0x00108000U;
    unsigned int rx;
    unsigned int rw;
    unsigned int dma;
    unsigned int device;

    assert(cosmos_contract_cache_way_shift(1U) == 0U);
    assert(cosmos_contract_cache_way_shift(2U) == 31U);
    assert(way_shift == 30U);
    assert(cosmos_contract_cache_way_shift(8U) == 29U);
    assert(cosmos_contract_cache_setway_operand(0U, 3U, 127U, 5U, way_shift) ==
        0xC0000FE0U);
    assert(cosmos_contract_cache_setway_operand(1U, 3U, 127U, 5U, way_shift) ==
        0xC0000FE2U);

    assert(cosmos_contract_ttbr0_value(0U) == 0x4AU);
    assert(cosmos_contract_ttbr0_value(0x12345678U) == 0x1234404AU);

    assert(cosmos_contract_scu_invalidate_mask(0U) == 0xFFFFU);
    assert(cosmos_contract_scu_invalidate_mask(1U) == 0U);
    assert(!cosmos_contract_cache_enable_allowed(0U, 0U));
    assert(!cosmos_contract_cache_enable_allowed(1U, 0U));
    assert(!cosmos_contract_cache_enable_allowed(0U, 0x40U));
    assert(cosmos_contract_cache_enable_allowed(1U, 0x40U));

    assert(cosmos_contract_mmu_poll_allowed(0U));
    assert(cosmos_contract_mmu_poll_allowed(COSMOS_POLL_LIMIT - 1U));
    assert(!cosmos_contract_mmu_poll_allowed(COSMOS_POLL_LIMIT));
    assert(!cosmos_contract_mmu_poll_allowed(UINT_MAX));

    assert(COSMOS_DDR_IDENTITY_BASE == 0x00100000U);
    assert(COSMOS_DDR_IDENTITY_END == 0x3FFFFFFFU);
    assert(COSMOS_FIRMWARE_IDENTITY_BASE == COSMOS_DDR_IDENTITY_BASE);
    assert(COSMOS_FIRMWARE_IDENTITY_END + 1U ==
        COSMOS_NFC_DMA_IDENTITY_BASE);
    assert(COSMOS_NFC_DATA_BUFFER_ADDRESS == 0x10000000U);
    assert(COSMOS_NFC_COMPLETE_FLAG_ADDRESS == 0x17000000U);
    assert(COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS == 0x17000D00U);
    assert(COSMOS_NFC_DMA_IDENTITY_END + 1U ==
        COSMOS_DDR_CACHED_RESUME_ADDRESS);

    assert(cosmos_contract_l1_descriptor(
        0x00000000U, firmware_l2, ocm_l2) == 0U);
    assert(cosmos_contract_l1_descriptor(
        0x000FFFFFU, firmware_l2, ocm_l2) == 0U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_FIRMWARE_IDENTITY_BASE, firmware_l2, ocm_l2) == 0x12345001U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_FIRMWARE_IDENTITY_END, firmware_l2, ocm_l2) == 0x12345001U);

    rx = cosmos_contract_firmware_l2_descriptor(
        COSMOS_FIRMWARE_IDENTITY_BASE, rx_end);
    assert(rx == 0x0010065EU);
    assert(cosmos_contract_l2_descriptor_executable(rx));
    assert(!cosmos_contract_l2_descriptor_priv_writable(rx));
    assert(!cosmos_contract_l2_descriptor_write_execute(rx));
    assert(cosmos_contract_firmware_l2_descriptor(
        rx_end - 1U, rx_end) == 0x0010765EU);

    rw = cosmos_contract_firmware_l2_descriptor(rx_end, rx_end);
    assert(rw == 0x0010845FU);
    assert(!cosmos_contract_l2_descriptor_executable(rw));
    assert(cosmos_contract_l2_descriptor_priv_writable(rw));
    assert(!cosmos_contract_l2_descriptor_write_execute(rw));
    assert(cosmos_contract_firmware_l2_descriptor(
        COSMOS_FIRMWARE_IDENTITY_END, rx_end) == 0x001FF45FU);

    dma = cosmos_contract_l1_descriptor(
        COSMOS_NFC_DMA_IDENTITY_BASE, firmware_l2, ocm_l2);
    assert(dma == 0x00211412U);
    assert((dma & 0x0000000CU) == 0U);
    assert((dma & 0x00011010U) == 0x00011010U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_NFC_DATA_BUFFER_ADDRESS, firmware_l2, ocm_l2) == 0x10011412U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_NFC_COMPLETE_FLAG_ADDRESS, firmware_l2, ocm_l2) == 0x17011412U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS, firmware_l2, ocm_l2) == 0x17011412U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_NFC_DMA_IDENTITY_END, firmware_l2, ocm_l2) == 0x17F11412U);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_DDR_CACHED_RESUME_ADDRESS, firmware_l2, ocm_l2) == 0x1801141EU);
    assert(cosmos_contract_l1_descriptor(
        COSMOS_DDR_IDENTITY_END, firmware_l2, ocm_l2) == 0x3FF1141EU);
    assert(cosmos_contract_l1_descriptor(
        0x40000000U, firmware_l2, ocm_l2) == 0U);
    assert(cosmos_contract_l1_descriptor(
        0x70000000U, firmware_l2, ocm_l2) == 0U);

    device = cosmos_contract_l1_descriptor(0x43C00000U, firmware_l2, ocm_l2);
    assert(device == 0x43C10416U);
    assert((device & 0x00001008U) == 0U);
    assert((device & 0x00010014U) == 0x00010014U);
    assert(cosmos_contract_l1_descriptor(
        0x83C00000U, firmware_l2, ocm_l2) == 0x83C10416U);
    assert(cosmos_contract_l1_descriptor(
        0xE0000000U, firmware_l2, ocm_l2) == 0xE0010416U);
    assert(cosmos_contract_l1_descriptor(
        0xF8000000U, firmware_l2, ocm_l2) == 0xF8010416U);
    assert(cosmos_contract_l1_descriptor(
        0xF8F00000U, firmware_l2, ocm_l2) == 0xF8F10416U);

    assert(cosmos_contract_l1_descriptor(
        0xFFF00000U, firmware_l2, ocm_l2) == 0x12345401U);
    assert(cosmos_contract_ocm_l2_descriptor(0xFFF00000U) == 0U);
    assert(cosmos_contract_ocm_l2_descriptor(0xFFFBFFFFU) == 0U);
    assert(cosmos_contract_ocm_l2_descriptor(
        0xFFFC0000U) == 0xFFFC0453U);
    assert(cosmos_contract_ocm_l2_descriptor(
        0xFFFFFFFFU) == 0xFFFFF453U);
}

static void test_cpu1_contract(void) {
    unsigned int generation = cosmos_contract_smp_next_generation(40U);
    unsigned int state = COSMOS_SMP_EMPTY;

    assert(cosmos_contract_smp_release_request_valid(0U, 0x00100000U, 0x00200000U));
    assert(!cosmos_contract_smp_release_request_valid(1U, 0x00100000U, 0x00200000U));
    assert(!cosmos_contract_smp_release_request_valid(0U, 0x00100002U, 0x00200000U));
    assert(!cosmos_contract_smp_release_request_valid(0U, 0x00100000U, 0x00200004U));
    assert(cosmos_contract_smp_next_generation(0U) == 1U);
    assert(generation == 41U);
    assert(cosmos_contract_smp_next_generation(UINT_MAX) == 1U);

    state = COSMOS_SMP_READY;
    assert(cosmos_contract_smp_ready_observed(state));
    state = COSMOS_SMP_RELEASED;
    assert(!cosmos_contract_smp_ack_observed(state, generation, generation));
    state = cosmos_contract_smp_secondary_state(0);
    assert(state == COSMOS_SMP_ACKED);
    assert(cosmos_contract_smp_ack_observed(state, generation, generation));
    assert(!cosmos_contract_smp_ack_observed(state, generation - 1U, generation));
    assert(cosmos_contract_smp_secondary_state(-1) == COSMOS_SMP_CANCELLED);

    assert(cosmos_contract_smp_poll_allowed(0U));
    assert(cosmos_contract_smp_poll_allowed(COSMOS_POLL_LIMIT - 1U));
    assert(!cosmos_contract_smp_poll_allowed(COSMOS_POLL_LIMIT));
    assert(!cosmos_contract_smp_poll_allowed(UINT_MAX));
}

static void test_gic_contract(void) {
    assert(cosmos_contract_gic_limit_words(0U) == 0U);
    assert(cosmos_contract_gic_limit_words(1U) == 1U);
    assert(cosmos_contract_gic_limit_words(32U) == 32U);
    assert(cosmos_contract_gic_limit_words(33U) == 0U);
    assert(cosmos_contract_gic_words_from_typer(0U) == 1U);
    assert(cosmos_contract_gic_words_from_typer(31U) == 32U);
    assert(cosmos_contract_gic_words_from_typer(UINT_MAX) == 32U);
    assert(cosmos_contract_gic_target_for_word(0U) == 0U);
    assert(cosmos_contract_gic_target_for_word(1U) == 0x01010101U);
    assert(cosmos_contract_gic_target_for_word(31U) == 0x01010101U);
    assert(cosmos_contract_gic_pcie_irq_id() == 61U);
    assert(cosmos_contract_gic_pcie_enable_offset() == 0x104U);
    assert(cosmos_contract_gic_pcie_disable_offset() == 0x184U);
    assert(cosmos_contract_gic_pcie_mask() == 0x20000000U);
    assert(cosmos_contract_gic_pcie_priority_offset() == 0x43CU);
    assert(cosmos_contract_gic_pcie_priority_value(0U) == 0x0000A000U);
    assert(cosmos_contract_gic_pcie_priority_value(UINT_MAX) == 0xFFFFA0FFU);
    assert(cosmos_contract_gic_pcie_target_offset() == 0x83CU);
    assert(cosmos_contract_gic_pcie_target_value(0U) == 0x00000100U);
    assert(cosmos_contract_gic_pcie_target_value(UINT_MAX) == 0xFFFF01FFU);
    assert(cosmos_contract_gic_pcie_config_offset() == 0xC0CU);
    assert(cosmos_contract_gic_pcie_level_config_value(UINT_MAX) == 0xF3FFFFFFU);
    assert(!cosmos_contract_gic_pcie_irq_in_range(1U));
    assert(cosmos_contract_gic_pcie_irq_in_range(2U));
    assert(cosmos_contract_gic_pcie_irq_in_range(32U));
    assert(cosmos_contract_gic_eoir_required(61U));
    assert(!cosmos_contract_gic_eoir_required(1020U));
    assert(cosmos_contract_gic_quiesce_kind(
        61U, COSMOS_OK) == COSMOS_GIC_QUIESCE_NONE);
    assert(cosmos_contract_gic_quiesce_kind(
        61U, COSMOS_UNAVAILABLE) == COSMOS_GIC_QUIESCE_LINE);
    assert(cosmos_contract_gic_quiesce_kind(
        7U, COSMOS_HW_ERROR) == COSMOS_GIC_QUIESCE_CPU);
    assert(cosmos_contract_gic_quiesce_kind(
        1020U, COSMOS_HW_ERROR) == COSMOS_GIC_QUIESCE_NONE);
}

int main(void) {
    test_cache_contract();
    test_cpu1_contract();
    test_gic_contract();
    puts("STATUS: PASS cosmos SMP/cache contract");
    return 0;
}
