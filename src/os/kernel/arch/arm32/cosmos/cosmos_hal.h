#ifndef SIMPLE_COSMOS_HAL_H
#define SIMPLE_COSMOS_HAL_H

/* Shared Cosmos+ HAL contract. All polling must be bounded. */
enum cosmos_status {
    COSMOS_OK = 0,
    COSMOS_UNAVAILABLE = 1,
    COSMOS_INVALID = 2,
    COSMOS_TIMEOUT = 3,
    COSMOS_HW_ERROR = 4,
    COSMOS_RETRY = 5,
    COSMOS_COMPLETION_UNCERTAIN = 6
};

#define COSMOS_DDR_BASE       0x00100000U
#define COSMOS_OCM_HIGH       0xFFFC0000U
#define COSMOS_SLCR_BASE      0xF8000000U
#define COSMOS_GIC_CPU_BASE   0xF8F00100U
#define COSMOS_GIC_DIST_BASE  0xF8F01000U
#define COSMOS_SCU_BASE       0xF8F00000U
#define COSMOS_PL310_BASE     0xF8F02000U
#define COSMOS_NFC_BASE       0x43C00000U
#define COSMOS_PCIE_BASE      0x83C00000U
#ifndef COSMOS_POLL_LIMIT
#define COSMOS_POLL_LIMIT     1000000U
#endif

#if defined(COSMOS_SILICON)
#define COSMOS_IS_QEMU 0
#else
#define COSMOS_IS_QEMU 1
#endif

#if defined(COSMOS_MMIO_TEST)
unsigned int cosmos_mmio_test_read32(unsigned int address);
void cosmos_mmio_test_write32(unsigned int address, unsigned int value);

static inline unsigned int cosmos_mmio_read32(unsigned int address) {
    return cosmos_mmio_test_read32(address);
}

static inline void cosmos_mmio_write32(unsigned int address,
                                       unsigned int value) {
    cosmos_mmio_test_write32(address, value);
}

static inline void cosmos_data_sync_barrier(void) {
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
}

static inline void cosmos_instruction_sync_barrier(void) {
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
}
#else
static inline unsigned int cosmos_mmio_read32(unsigned int address) {
    return *(volatile unsigned int *)address;
}

static inline void cosmos_mmio_write32(unsigned int address,
                                       unsigned int value) {
    *(volatile unsigned int *)address = value;
}

static inline void cosmos_data_sync_barrier(void) {
    __asm__ volatile("dsb sy" ::: "memory");
}

static inline void cosmos_instruction_sync_barrier(void) {
    __asm__ volatile("isb sy" ::: "memory");
}
#endif

int cosmos_nfc_init(void);
int cosmos_nfc_selftest(void);

int cosmos_pcie_init(void);
int cosmos_pcie_selftest(void);

/*
 * Minimal, bounded NVMe I/O adapter contract. The adapter owns queue DMA,
 * PRP/SGL decoding, and FTL/media translation. This core does not bind PCIe,
 * implement an FTL, or claim persistent media semantics.
 *
 * The PCIe adapter preserves both PRP entries and the captured command slot.
 * Cosmos+ media implementations use AUTO DMA so the controller hardware,
 * rather than firmware, walks PRP lists.
 */
#define COSMOS_NVME_NAMESPACE_ID 1U
#define COSMOS_NVME_OPCODE_FLUSH 0x00U
#define COSMOS_NVME_OPCODE_WRITE 0x01U
#define COSMOS_NVME_OPCODE_READ  0x02U
#define COSMOS_NVME_OPCODE_WRITE_ZEROES 0x08U
#define COSMOS_NVME_OPCODE_DATASET_MANAGEMENT 0x09U
#define COSMOS_NVME_MAX_NLB      0x0000FFFFU
#define COSMOS_NVME_MAX_CID      0x0000FFFFU
#define COSMOS_NVME_MAX_DSM_RANGES 256U
#define COSMOS_NVME_DSM_RANGE_BYTES 16U
#define COSMOS_NVME_DMA_ALIGNMENT 4U
#define COSMOS_NVME_SERVICE_BUDGET 8U
#define COSMOS_NVME_RW_FUA (1U << 30U)
#define COSMOS_NVME_RW_LR  (1U << 31U)
#define COSMOS_NVME_RW_CONTROL_MASK (COSMOS_NVME_RW_FUA | COSMOS_NVME_RW_LR)

#define COSMOS_NVME_DSM_ATTRIBUTE_DEALLOCATE (1U << 2U)
#define COSMOS_NVME_DSM_ATTRIBUTE_MASK 0x00000007U
#define COSMOS_NVME_WRITE_ZEROES_DEAC (1U << 25U)
#define COSMOS_NVME_WRITE_ZEROES_FUA  (1U << 30U)
#define COSMOS_NVME_WRITE_ZEROES_LR   (1U << 31U)
#define COSMOS_NVME_WRITE_ZEROES_CONTROL_MASK \
    (COSMOS_NVME_WRITE_ZEROES_DEAC | COSMOS_NVME_WRITE_ZEROES_FUA | \
     COSMOS_NVME_WRITE_ZEROES_LR)

/* NVMe Base Specification status-code types and codes. */
#define COSMOS_NVME_SCT_GENERIC                 0U
#define COSMOS_NVME_SCT_COMMAND_SPECIFIC        1U
#define COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY    2U
#define COSMOS_NVME_SC_SUCCESS                   0x00U
#define COSMOS_NVME_SC_INVALID_OPCODE            0x01U
#define COSMOS_NVME_SC_INVALID_FIELD             0x02U
#define COSMOS_NVME_SC_DATA_TRANSFER_ERROR       0x04U
#define COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR     0x06U
#define COSMOS_NVME_SC_LBA_OUT_OF_RANGE          0x80U
#define COSMOS_NVME_SC_NAMESPACE_NOT_READY       0x82U
#define COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT  0x0BU
#define COSMOS_NVME_SC_WRITE_FAULT               0x80U
#define COSMOS_NVME_SC_UNRECOVERED_READ_ERROR    0x81U

struct cosmos_nvme_status {
    unsigned int sct;
    unsigned int sc;
    unsigned int dnr;
};

struct cosmos_nvme_command {
    unsigned int queue_id;
    unsigned int slot_tag;
    unsigned int sequence;
    unsigned int cid;
    unsigned int namespace_id;
    unsigned int opcode;
    unsigned int lba_low;
    unsigned int lba_high;
    unsigned int nlb;
    unsigned int data_address_low;
    unsigned int data_address_high;
    unsigned int data_address2_low;
    unsigned int data_address2_high;
    unsigned int data_bytes;
    unsigned int control;
    unsigned int dataset_attributes;
    unsigned int dataset_range_count;
};

struct cosmos_nvme_completion {
    unsigned int queue_id;
    unsigned int slot_tag;
    unsigned int sequence;
    unsigned int cid;
    struct cosmos_nvme_status status;
};

enum cosmos_nvme_post_result {
    COSMOS_NVME_POST_COMMITTED = 0,
    COSMOS_NVME_POST_NOT_COMMITTED_RETRY = 1,
    COSMOS_NVME_POST_AMBIGUOUS = 2,
    COSMOS_NVME_POST_HARD_FAILED = 3
};

enum cosmos_nvme_completion_state {
    COSMOS_NVME_COMPLETION_NONE = 0,
    COSMOS_NVME_COMPLETION_RETRY = 1,
    COSMOS_NVME_COMPLETION_BLOCKED = 2
};

struct cosmos_nvme_adapter {
    void *context;
    int (*fetch_command)(void *context, struct cosmos_nvme_command *command);
    enum cosmos_nvme_post_result (*post_completion)(
        void *context, const struct cosmos_nvme_completion *completion);
    int (*media_read)(void *context,
                      const struct cosmos_nvme_command *command);
    int (*media_program)(void *context,
                         const struct cosmos_nvme_command *command);
    int (*media_flush)(void *context);
    int (*media_write_zeroes)(
        void *context, const struct cosmos_nvme_command *command);
    int (*media_deallocate)(
        void *context, const struct cosmos_nvme_command *command);
};

struct cosmos_nvme_service {
    struct cosmos_nvme_adapter adapter;
    unsigned int namespace_blocks_low;
    unsigned int namespace_blocks_high;
    unsigned int block_bytes;
    enum cosmos_nvme_completion_state completion_state;
    int completion_terminal_status;
    struct cosmos_nvme_completion pending_completion;
};

int cosmos_nvme_service_init(struct cosmos_nvme_service *service,
                             const struct cosmos_nvme_adapter *adapter,
                             unsigned int namespace_blocks_low,
                             unsigned int namespace_blocks_high,
                             unsigned int block_bytes);
int cosmos_nvme_service_poll(struct cosmos_nvme_service *service);

void cosmos_runtime_init(void);
int cosmos_runtime_selftest(void);

unsigned int cosmos_cpu_id(void);
int cosmos_gic_init_primary(void);
int cosmos_gic_init_secondary(void);
int cosmos_smp_release_secondary(unsigned int entry, unsigned int stack_top);
int cosmos_smp_selftest(void);

int cosmos_mmu_cache_init(void);
int cosmos_mmu_cache_selftest(void);

int cosmos_fsbl_validate_handoff(void);
int cosmos_fsbl_selftest(void);

#endif
