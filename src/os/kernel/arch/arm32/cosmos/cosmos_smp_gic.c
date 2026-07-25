/* Cortex-A9 MPCore / GICv1 support for the Cosmos+ Zynq-7000 lane.
 *
 * The mailbox is defined by cosmos_start.S so a secondary can park before C
 * has a stack.  CPU0 writes entry and stack before changing state, then uses
 * SEV to wake CPU1.  Every wait is bounded; an unavailable secondary leaves
 * CPU0 running and CPU1 parked.
 */
#ifdef COSMOS_CONTRACT_TEST
#define COSMOS_OK 0
#define COSMOS_UNAVAILABLE 1
#define COSMOS_HW_ERROR 4
#define COSMOS_POLL_LIMIT 1000000U
#else
#include "cosmos_hal.h"
#endif
#include "cosmos_pcie_regs.h"

#define GICD_CTLR       0x000U
#define GICD_TYPER      0x004U
#define GICD_IGROUPR    0x080U
#define GICD_ISENABLER  0x100U
#define GICD_ICENABLER  0x180U
#define GICD_ICPENDR    0x280U
#define GICD_ICACTIVER  0x380U
#define GICD_IPRIORITYR 0x400U
#define GICD_ITARGETSR  0x800U
#define GICD_ICFGR      0xC00U
#define GICC_CTLR       0x000U
#define GICC_PMR        0x004U
#define GICC_BPR        0x008U
#define GICC_IAR        0x00CU
#define GICC_EOIR       0x010U

#define COSMOS_GIC_MAX_WORDS 32U
#define COSMOS_GIC_ENABLE     1U
#define COSMOS_GIC_PRIORITY   0xA0A0A0A0U
#define COSMOS_GIC_PCI_PRIORITY 0xA0U
#define COSMOS_GIC_CPU0       0x01010101U
#define COSMOS_GIC_CPU0_TARGET 0x01U
#define COSMOS_GIC_IRQ_ID_MASK 0x3FFU
#define COSMOS_GIC_SPURIOUS_MIN 1020U
#define COSMOS_ZYNQ_CPU1_START 0xFFFFFFF0U

#define COSMOS_GIC_QUIESCE_NONE 0U
#define COSMOS_GIC_QUIESCE_CPU  1U
#define COSMOS_GIC_QUIESCE_LINE 2U

#define COSMOS_SMP_EMPTY      0U
#define COSMOS_SMP_READY      1U
#define COSMOS_SMP_RELEASED   2U
#define COSMOS_SMP_ACKED      3U
#define COSMOS_SMP_CANCELLED  4U

static unsigned int cosmos_gic_limit_words(unsigned int words) {
    return words != 0U && words <= COSMOS_GIC_MAX_WORDS ? words : 0U;
}

static unsigned int cosmos_gic_words_from_typer(unsigned int typer) {
    return cosmos_gic_limit_words((typer & 0x1FU) + 1U);
}

static unsigned int cosmos_gic_target_for_word(unsigned int word) {
    return word == 0U ? 0U : COSMOS_GIC_CPU0;
}

static unsigned int cosmos_smp_next_generation(unsigned int generation) {
    generation++;
    return generation == 0U ? 1U : generation;
}

static int cosmos_smp_release_request_valid(
    unsigned int cpu_id,
    unsigned int entry,
    unsigned int stack_top
) {
    return cpu_id == 0U && entry != 0U && stack_top != 0U &&
        (entry & 3U) == 0U && (stack_top & 7U) == 0U;
}

static int cosmos_smp_ready_observed(unsigned int state) {
    return state == COSMOS_SMP_READY;
}

static unsigned int cosmos_smp_secondary_state(int result) {
    return result == COSMOS_OK ? COSMOS_SMP_ACKED : COSMOS_SMP_CANCELLED;
}

static int cosmos_smp_ack_observed(
    unsigned int state,
    unsigned int ack,
    unsigned int generation
) {
    return state == COSMOS_SMP_ACKED && ack == generation;
}

static int cosmos_smp_poll_allowed(unsigned int poll) {
    return poll < COSMOS_POLL_LIMIT;
}

static unsigned int cosmos_gic_irq_id(unsigned int acknowledge) {
    return acknowledge & COSMOS_GIC_IRQ_ID_MASK;
}

static int cosmos_gic_irq_is_spurious(unsigned int interrupt_id) {
    return interrupt_id >= COSMOS_GIC_SPURIOUS_MIN;
}

static unsigned int cosmos_gic_disable_offset(unsigned int interrupt_id) {
    return GICD_ICENABLER + (interrupt_id / 32U) * 4U;
}

static unsigned int cosmos_gic_disable_mask(unsigned int interrupt_id) {
    return 1U << (interrupt_id & 31U);
}

static unsigned int cosmos_gic_byte_shift(unsigned int interrupt_id) {
    return (interrupt_id & 3U) * 8U;
}

static unsigned int cosmos_gic_config_shift(unsigned int interrupt_id) {
    return (interrupt_id & 15U) * 2U;
}

static unsigned int cosmos_gic_priority_offset(unsigned int interrupt_id) {
    return GICD_IPRIORITYR + (interrupt_id / 4U) * 4U;
}

static unsigned int cosmos_gic_target_offset(unsigned int interrupt_id) {
    return GICD_ITARGETSR + (interrupt_id / 4U) * 4U;
}

static unsigned int cosmos_gic_config_offset(unsigned int interrupt_id) {
    return GICD_ICFGR + (interrupt_id / 16U) * 4U;
}

static unsigned int cosmos_gic_priority_value(
    unsigned int current,
    unsigned int interrupt_id
) {
    unsigned int shift = cosmos_gic_byte_shift(interrupt_id);
    unsigned int mask = 0xFFU << shift;

    return (current & ~mask) | (COSMOS_GIC_PCI_PRIORITY << shift);
}

static unsigned int cosmos_gic_target_cpu0_value(
    unsigned int current,
    unsigned int interrupt_id
) {
    unsigned int shift = cosmos_gic_byte_shift(interrupt_id);
    unsigned int mask = 0xFFU << shift;

    return (current & ~mask) | (COSMOS_GIC_CPU0_TARGET << shift);
}

static unsigned int cosmos_gic_level_config_value(
    unsigned int current,
    unsigned int interrupt_id
) {
    return current & ~(3U << cosmos_gic_config_shift(interrupt_id));
}

static int cosmos_gic_pcie_irq_in_range(unsigned int words) {
    return cosmos_gic_limit_words(words) != 0U &&
        (COSMOS_PCIE_PL_IRQ_ID / 32U) < words;
}

static int cosmos_gic_eoir_required(unsigned int interrupt_id) {
    return !cosmos_gic_irq_is_spurious(interrupt_id);
}

static unsigned int cosmos_gic_quiesce_kind(
    unsigned int interrupt_id,
    int handler_result
) {
    if (handler_result == COSMOS_OK ||
        cosmos_gic_irq_is_spurious(interrupt_id)) {
        return COSMOS_GIC_QUIESCE_NONE;
    }
    return interrupt_id < 16U ? COSMOS_GIC_QUIESCE_CPU : COSMOS_GIC_QUIESCE_LINE;
}

_Static_assert(COSMOS_GIC_SPURIOUS_MIN == 1020U,
    "GICv1 IDs 1020..1023 are reserved/spurious");
_Static_assert(COSMOS_PCIE_PL_IRQ_ID == 61U,
    "Cosmos+ OpenSSD HDF routes PCIe dev_irq_assert to GIC ID 61");

#ifdef COSMOS_CONTRACT_TEST
unsigned int cosmos_contract_gic_limit_words(unsigned int words) {
    return cosmos_gic_limit_words(words);
}

unsigned int cosmos_contract_gic_words_from_typer(unsigned int typer) {
    return cosmos_gic_words_from_typer(typer);
}

unsigned int cosmos_contract_gic_target_for_word(unsigned int word) {
    return cosmos_gic_target_for_word(word);
}

unsigned int cosmos_contract_smp_next_generation(unsigned int generation) {
    return cosmos_smp_next_generation(generation);
}

int cosmos_contract_smp_release_request_valid(
    unsigned int cpu_id,
    unsigned int entry,
    unsigned int stack_top
) {
    return cosmos_smp_release_request_valid(cpu_id, entry, stack_top);
}

int cosmos_contract_smp_ready_observed(unsigned int state) {
    return cosmos_smp_ready_observed(state);
}

unsigned int cosmos_contract_smp_secondary_state(int result) {
    return cosmos_smp_secondary_state(result);
}

int cosmos_contract_smp_ack_observed(
    unsigned int state,
    unsigned int ack,
    unsigned int generation
) {
    return cosmos_smp_ack_observed(state, ack, generation);
}

int cosmos_contract_smp_poll_allowed(unsigned int poll) {
    return cosmos_smp_poll_allowed(poll);
}

unsigned int cosmos_contract_gic_irq_id(unsigned int acknowledge) {
    return cosmos_gic_irq_id(acknowledge);
}

int cosmos_contract_gic_irq_is_spurious(unsigned int interrupt_id) {
    return cosmos_gic_irq_is_spurious(interrupt_id);
}

unsigned int cosmos_contract_gic_disable_offset(unsigned int interrupt_id) {
    return cosmos_gic_disable_offset(interrupt_id);
}

unsigned int cosmos_contract_gic_disable_mask(unsigned int interrupt_id) {
    return cosmos_gic_disable_mask(interrupt_id);
}

unsigned int cosmos_contract_gic_pcie_irq_id(void) {
    return COSMOS_PCIE_PL_IRQ_ID;
}

unsigned int cosmos_contract_gic_pcie_enable_offset(void) {
    return GICD_ISENABLER + (COSMOS_PCIE_PL_IRQ_ID / 32U) * 4U;
}

unsigned int cosmos_contract_gic_pcie_disable_offset(void) {
    return cosmos_gic_disable_offset(COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_mask(void) {
    return cosmos_gic_disable_mask(COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_priority_offset(void) {
    return cosmos_gic_priority_offset(COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_priority_value(unsigned int current) {
    return cosmos_gic_priority_value(current, COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_target_offset(void) {
    return cosmos_gic_target_offset(COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_target_value(unsigned int current) {
    return cosmos_gic_target_cpu0_value(current, COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_config_offset(void) {
    return cosmos_gic_config_offset(COSMOS_PCIE_PL_IRQ_ID);
}

unsigned int cosmos_contract_gic_pcie_level_config_value(unsigned int current) {
    return cosmos_gic_level_config_value(current, COSMOS_PCIE_PL_IRQ_ID);
}

int cosmos_contract_gic_pcie_irq_in_range(unsigned int words) {
    return cosmos_gic_pcie_irq_in_range(words);
}

int cosmos_contract_gic_eoir_required(unsigned int interrupt_id) {
    return cosmos_gic_eoir_required(interrupt_id);
}

unsigned int cosmos_contract_gic_quiesce_kind(
    unsigned int interrupt_id,
    int handler_result
) {
    return cosmos_gic_quiesce_kind(interrupt_id, handler_result);
}
#else
extern volatile unsigned int cosmos_secondary_release_entry;
extern volatile unsigned int cosmos_secondary_release_stack;
extern volatile unsigned int cosmos_secondary_release_generation;
extern volatile unsigned int cosmos_secondary_release_ack;
extern volatile unsigned int cosmos_secondary_release_state;
extern void cosmos_secondary_start(void);

_Static_assert((COSMOS_ZYNQ_CPU1_START & 3U) == 0U, "CPU1 start vector alignment");

static void cosmos_mailbox_clean(void) {
    unsigned int first = (unsigned int)&cosmos_secondary_release_entry;
    unsigned int last = (unsigned int)&cosmos_secondary_release_state;
    __asm__ volatile("mcr p15, 0, %0, c7, c10, 1" : : "r"(first) : "memory");
    __asm__ volatile("mcr p15, 0, %0, c7, c10, 1" : : "r"(last) : "memory");
    cosmos_data_sync_barrier();
}

static void cosmos_mailbox_invalidate(void) {
    unsigned int first = (unsigned int)&cosmos_secondary_release_entry;
    unsigned int last = (unsigned int)&cosmos_secondary_release_state;
    __asm__ volatile("mcr p15, 0, %0, c7, c6, 1" : : "r"(first) : "memory");
    __asm__ volatile("mcr p15, 0, %0, c7, c6, 1" : : "r"(last) : "memory");
    cosmos_data_sync_barrier();
}

static unsigned int cosmos_gic_words(void) {
    return cosmos_gic_words_from_typer(
        cosmos_mmio_read32(COSMOS_GIC_DIST_BASE + GICD_TYPER));
}

static int cosmos_gic_cpu_init(void) {
    cosmos_mmio_write32(COSMOS_GIC_CPU_BASE + GICC_CTLR, 0U);
    cosmos_mmio_write32(COSMOS_GIC_CPU_BASE + GICC_PMR, 0xFFU);
    cosmos_mmio_write32(COSMOS_GIC_CPU_BASE + GICC_BPR, 0U);
    cosmos_data_sync_barrier();
    cosmos_mmio_write32(COSMOS_GIC_CPU_BASE + GICC_CTLR, COSMOS_GIC_ENABLE);
    cosmos_instruction_sync_barrier();
    return (cosmos_mmio_read32(COSMOS_GIC_CPU_BASE + GICC_CTLR) & COSMOS_GIC_ENABLE) != 0U
        ? COSMOS_OK : COSMOS_HW_ERROR;
}

int cosmos_gic_enable_pcie_irq(void) {
    unsigned int words = cosmos_gic_words();
    unsigned int word_offset = (COSMOS_PCIE_PL_IRQ_ID / 32U) * 4U;
    unsigned int mask = cosmos_gic_disable_mask(COSMOS_PCIE_PL_IRQ_ID);
    unsigned int priority;
    unsigned int target;
    unsigned int config;

    if (!cosmos_gic_pcie_irq_in_range(words) ||
        (cosmos_mmio_read32(COSMOS_GIC_DIST_BASE + GICD_CTLR) & COSMOS_GIC_ENABLE) == 0U ||
        (cosmos_mmio_read32(COSMOS_GIC_CPU_BASE + GICC_CTLR) & COSMOS_GIC_ENABLE) == 0U) {
        return COSMOS_UNAVAILABLE;
    }

    cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ICENABLER + word_offset, mask);
    cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ICPENDR + word_offset, mask);
    cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ICACTIVER + word_offset, mask);

    priority = cosmos_mmio_read32(
        COSMOS_GIC_DIST_BASE + cosmos_gic_priority_offset(COSMOS_PCIE_PL_IRQ_ID));
    cosmos_mmio_write32(
        COSMOS_GIC_DIST_BASE + cosmos_gic_priority_offset(COSMOS_PCIE_PL_IRQ_ID),
        cosmos_gic_priority_value(priority, COSMOS_PCIE_PL_IRQ_ID));

    target = cosmos_mmio_read32(
        COSMOS_GIC_DIST_BASE + cosmos_gic_target_offset(COSMOS_PCIE_PL_IRQ_ID));
    cosmos_mmio_write32(
        COSMOS_GIC_DIST_BASE + cosmos_gic_target_offset(COSMOS_PCIE_PL_IRQ_ID),
        cosmos_gic_target_cpu0_value(target, COSMOS_PCIE_PL_IRQ_ID));

    config = cosmos_mmio_read32(
        COSMOS_GIC_DIST_BASE + cosmos_gic_config_offset(COSMOS_PCIE_PL_IRQ_ID));
    cosmos_mmio_write32(
        COSMOS_GIC_DIST_BASE + cosmos_gic_config_offset(COSMOS_PCIE_PL_IRQ_ID),
        cosmos_gic_level_config_value(config, COSMOS_PCIE_PL_IRQ_ID));

    cosmos_data_sync_barrier();
    cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ISENABLER + word_offset, mask);
    cosmos_data_sync_barrier();
    return (cosmos_mmio_read32(COSMOS_GIC_DIST_BASE + GICD_ISENABLER + word_offset) &
            mask) != 0U ? COSMOS_OK : COSMOS_HW_ERROR;
}

__attribute__((weak))
int cosmos_platform_irq_handle(unsigned int interrupt_id) {
    (void)interrupt_id;
    return COSMOS_UNAVAILABLE;
}

static void cosmos_gic_quiesce_unhandled(unsigned int interrupt_id) {
    if (cosmos_gic_quiesce_kind(interrupt_id, COSMOS_UNAVAILABLE) ==
        COSMOS_GIC_QUIESCE_CPU) {
        /* SGIs cannot be disabled individually; fail closed on this CPU. */
        cosmos_mmio_write32(COSMOS_GIC_CPU_BASE + GICC_CTLR, 0U);
    } else {
        cosmos_mmio_write32(
            COSMOS_GIC_DIST_BASE + cosmos_gic_disable_offset(interrupt_id),
            cosmos_gic_disable_mask(interrupt_id));
    }
    cosmos_data_sync_barrier();
}

void cosmos_gic_irq_dispatch(void) {
    unsigned int acknowledge =
        cosmos_mmio_read32(COSMOS_GIC_CPU_BASE + GICC_IAR);
    unsigned int interrupt_id = cosmos_gic_irq_id(acknowledge);

    /* One acknowledged interrupt per exception keeps this path strictly bounded. */
    if (!cosmos_gic_eoir_required(interrupt_id)) {
        return;
    }
    if (cosmos_platform_irq_handle(interrupt_id) != COSMOS_OK) {
        cosmos_gic_quiesce_unhandled(interrupt_id);
    }
    cosmos_data_sync_barrier();
    cosmos_mmio_write32(COSMOS_GIC_CPU_BASE + GICC_EOIR, acknowledge);
    cosmos_data_sync_barrier();
}

void cosmos_irq_enable(void) {
    cosmos_data_sync_barrier();
    __asm__ volatile("cpsid f\n\tcpsie i" ::: "memory");
    cosmos_instruction_sync_barrier();
}

unsigned int cosmos_cpu_id(void) {
    unsigned int mpidr;
    __asm__ volatile("mrc p15, 0, %0, c0, c0, 5" : "=r"(mpidr));
    return mpidr & 3U;
}

int cosmos_gic_init_primary(void) {
    unsigned int word;
    unsigned int words;

    if (cosmos_cpu_id() != 0U) {
        return COSMOS_INVALID;
    }
    words = cosmos_gic_words();
    if (words == 0U) {
        return COSMOS_UNAVAILABLE;
    }

    cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_CTLR, 0U);
    cosmos_data_sync_barrier();
    for (word = 0U; word < words; word++) {
        unsigned int offset = word * 4U;
        unsigned int priority;

        cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_IGROUPR + offset, 0U);
        cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ICENABLER + offset, 0xFFFFFFFFU);
        cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ICPENDR + offset, 0xFFFFFFFFU);
        cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ICACTIVER + offset, 0xFFFFFFFFU);
        for (priority = 0U; priority < 8U; priority++) {
            cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_IPRIORITYR + offset * 8U + priority * 4U,
                COSMOS_GIC_PRIORITY);
        }
        if (cosmos_gic_target_for_word(word) != 0U) {
            for (priority = 0U; priority < 8U; priority++) {
                cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_ITARGETSR + offset * 8U + priority * 4U,
                    cosmos_gic_target_for_word(word));
            }
        }
    }
    cosmos_data_sync_barrier();
    cosmos_mmio_write32(COSMOS_GIC_DIST_BASE + GICD_CTLR, COSMOS_GIC_ENABLE);
    cosmos_instruction_sync_barrier();
    return cosmos_gic_cpu_init();
}

int cosmos_gic_init_secondary(void) {
    return cosmos_cpu_id() == 0U ? COSMOS_INVALID : cosmos_gic_cpu_init();
}

int cosmos_smp_secondary_prepare(void) {
    int result;

    if (cosmos_cpu_id() == 0U) {
        return COSMOS_INVALID;
    }
    result = cosmos_mmu_cache_init();
    if (result == COSMOS_OK) {
        result = cosmos_gic_init_secondary();
    }
    if (result != COSMOS_OK) {
        cosmos_secondary_release_state = cosmos_smp_secondary_state(result);
        cosmos_data_sync_barrier();
        return result;
    }

    cosmos_secondary_release_ack = cosmos_secondary_release_generation;
    cosmos_secondary_release_state = cosmos_smp_secondary_state(result);
    cosmos_data_sync_barrier();
    return COSMOS_OK;
}

int cosmos_smp_release_secondary(unsigned int entry, unsigned int stack_top) {
    unsigned int poll;
    unsigned int generation;

    if (!cosmos_smp_release_request_valid(cosmos_cpu_id(), entry, stack_top)) {
        return COSMOS_INVALID;
    }
    generation = cosmos_smp_next_generation(cosmos_secondary_release_generation);
    cosmos_secondary_release_entry = entry;
    cosmos_secondary_release_stack = stack_top;
    cosmos_secondary_release_ack = 0U;
    cosmos_secondary_release_state = COSMOS_SMP_EMPTY;
    cosmos_mailbox_clean();

    cosmos_mmio_write32(COSMOS_ZYNQ_CPU1_START, (unsigned int)cosmos_secondary_start);
    cosmos_data_sync_barrier();
    __asm__ volatile("sev" ::: "memory");
    for (poll = 0U; cosmos_smp_poll_allowed(poll); poll++) {
        cosmos_mailbox_invalidate();
        if (cosmos_smp_ready_observed(cosmos_secondary_release_state)) {
            break;
        }
    }
    if (!cosmos_smp_poll_allowed(poll)) {
        return COSMOS_UNAVAILABLE;
    }

    cosmos_secondary_release_generation = generation;
    cosmos_secondary_release_state = COSMOS_SMP_RELEASED;
    cosmos_mailbox_clean();
    __asm__ volatile("sev" ::: "memory");

    for (poll = 0U; cosmos_smp_poll_allowed(poll); poll++) {
        cosmos_mailbox_invalidate();
        if (cosmos_smp_ack_observed(
                cosmos_secondary_release_state,
                cosmos_secondary_release_ack,
                generation)) {
            return COSMOS_OK;
        }
    }
    cosmos_secondary_release_state = cosmos_smp_secondary_state(COSMOS_TIMEOUT);
    cosmos_data_sync_barrier();
    __asm__ volatile("sev" ::: "memory");
    return COSMOS_TIMEOUT;
}

int cosmos_smp_selftest(void) {
    unsigned int state = cosmos_secondary_release_state;

    if (cosmos_cpu_id() > 1U ||
        state > COSMOS_SMP_CANCELLED ||
        cosmos_gic_irq_id(0xABCDE02AU) != 42U ||
        cosmos_gic_irq_is_spurious(1019U) ||
        !cosmos_gic_irq_is_spurious(1020U) ||
        cosmos_gic_disable_offset(63U) != GICD_ICENABLER + 4U ||
        cosmos_gic_disable_mask(63U) != 0x80000000U) {
        return COSMOS_INVALID;
    }
    if (cosmos_cpu_id() == 0U &&
        ((cosmos_mmio_read32(COSMOS_GIC_CPU_BASE + GICC_CTLR) & COSMOS_GIC_ENABLE) == 0U ||
         (cosmos_mmio_read32(COSMOS_GIC_DIST_BASE + GICD_CTLR) & COSMOS_GIC_ENABLE) == 0U)) {
        return COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}

/* Called opportunistically from start.S.  A failure deliberately does not stop CPU0 boot. */
int cosmos_smp_gic_bootstrap(void) {
    int result = cosmos_gic_init_primary();
    return result == COSMOS_OK ? cosmos_smp_selftest() : result;
}
#endif
