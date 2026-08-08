#ifndef SIMPLE_COSMOS_PCIE_REGS_H
#define SIMPLE_COSMOS_PCIE_REGS_H

/*
 * Cosmos+ OpenSSD 8Ch8Way 3.0.0 NVMeHostController v2.0.0 contract.
 *
 * Provenance:
 * https://github.com/Cosmos-OpenSSD/Cosmos-plus-OpenSSD/tree/
 * 78601486bb5581e40628ec7e841dea8e97eff034
 * - project/Prebuild/8Ch8Way-3.0.0/OpenSSD2-8C8W-Prebuild-3.0.0.hdf,
 *   embedded OpenSSD2_bd.tcl: AXI base 0x83c00000, span 0x10000.
 *   OpenSSD2.hwh: NVMeHostController_0/dev_irq_assert is IRQID 61 on
 *   ps7_scugic_0/IRQ_F2P.
 * - source/software/GreedyFTL-3.0.0/nvme/host_lld.h: register offsets.
 * - source/software/GreedyFTL-3.0.0/nvme/host_lld.c: get_nvme_cmd()
 *   and set_nvme_cpl() transport ordering.
 * - source/hardware/nvme/nvme_host_ctrl_8lane-1.0.0/s_axi_reg.v:
 *   synthesized status/function/queue bit layout.
 * - source/hardware/nvme/nvme_host_ctrl_8lane-1.0.0/pcie_hcmd_sq_recv.v:
 *   command FIFO metadata source: {cmdSeqNum, cmdSlotTag, qID}.
 * - source/hardware/nvme/nvme_host_ctrl_8lane-1.0.0/
 *   pcie_7x_0_core_top/pcie_7x_0_core_top.xci: BAR, ID and MSI contract.
 * - AMD/Xilinx PG054:
 *   https://docs.amd.com/r/en-US/pg054-7series-pcie/Common-Interface
 *   https://docs.amd.com/r/en-US/pg054-7series-pcie/cfg_command-15-0
 *   https://docs.amd.com/r/en-US/pg054-7series-pcie/Generating-Interrupt-Requests
 *
 * Define COSMOS_PCIE_BITSTREAM_CONTRACT to the token below only when the
 * packaged bitstream is that exact upstream design. There is no IP ID register,
 * so an unbound build must not probe this AXI aperture.
 */
#define COSMOS_PCIE_CONTRACT_8CH8WAY_V300 0x030000U

#define COSMOS_PCIE_HOST_BASE              0x83C00000U
#define COSMOS_PCIE_HOST_SPAN              0x00010000U
#define COSMOS_PCIE_PL_IRQ_ID              61U

#define COSMOS_PCIE_CONTROL_OFFSET         0x0000U
#define COSMOS_PCIE_IRQ_MASK_OFFSET        0x0004U
#define COSMOS_PCIE_IRQ_CLEAR_OFFSET       0x0008U
#define COSMOS_PCIE_IRQ_STATUS_OFFSET      0x000CU
#define COSMOS_PCIE_STATUS_OFFSET          0x0100U
#define COSMOS_PCIE_FUNCTION_OFFSET        0x0104U
#define COSMOS_PCIE_NVME_STATUS_OFFSET     0x0200U
#define COSMOS_PCIE_HOST_DMA_FIFO_COUNT_OFFSET 0x0204U
#define COSMOS_PCIE_ADMIN_QUEUE_OFFSET     0x021CU
#define COSMOS_PCIE_IO_SQ_OFFSET           0x0220U
#define COSMOS_PCIE_IO_CQ_OFFSET           0x0260U
#define COSMOS_PCIE_NVME_CMD_FIFO_OFFSET   0x0300U
#define COSMOS_PCIE_NVME_CPL_FIFO_OFFSET   0x0304U
#define COSMOS_PCIE_HOST_DMA_CMD_FIFO_OFFSET 0x0310U
#define COSMOS_PCIE_NVME_CMD_SRAM_OFFSET   0x2000U

/*
 * host_lld.h HOST_DMA_CMD_FIFO_REG, as decoded by s_axi_reg.v.
 * The four writes at +0, +4, +8, and +12 form one direct descriptor; the
 * final +12 write is the FIFO commit.  AUTO descriptors use only +0 and
 * +12 because host_lld.c deliberately omits +4 and +8.
 */
#define COSMOS_PCIE_HOST_DMA_WORD0_OFFSET  0x0000U
#define COSMOS_PCIE_HOST_DMA_WORD1_OFFSET  0x0004U
#define COSMOS_PCIE_HOST_DMA_WORD2_OFFSET  0x0008U
#define COSMOS_PCIE_HOST_DMA_WORD3_OFFSET  0x000CU
#define COSMOS_PCIE_HOST_DMA_MAX_BYTES     0x00001000U
#define COSMOS_PCIE_HOST_DMA_DEVICE_ALIGNMENT 4U
#define COSMOS_PCIE_HOST_DMA_HOST_ALIGNMENT 16U
#define COSMOS_PCIE_HOST_DMA_HOST_HIGH_MASK 0x0000000FU
#define COSMOS_PCIE_HOST_DMA_LENGTH_MASK   0x00001FFFU
#define COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX 255U
#define COSMOS_PCIE_HOST_DMA_SLOT_MASK     0x0000007FU
#define COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_SHIFT 14U
#define COSMOS_PCIE_HOST_DMA_SLOT_SHIFT    23U
#define COSMOS_PCIE_HOST_DMA_DIRECTION_SHIFT 30U
#define COSMOS_PCIE_HOST_DMA_TYPE_SHIFT    31U
#define COSMOS_PCIE_HOST_DMA_TYPE_AUTO     0U
#define COSMOS_PCIE_HOST_DMA_TYPE_DIRECT   1U
#define COSMOS_PCIE_HOST_DMA_DIRECTION_RX  0U
#define COSMOS_PCIE_HOST_DMA_DIRECTION_TX  1U

/* HOST_DMA_FIFO_CNT_REG at +0x204: RX direct, TX direct, RX auto, TX auto. */
#define COSMOS_PCIE_HOST_DMA_DIRECT_RX_COUNT_SHIFT 0U
#define COSMOS_PCIE_HOST_DMA_DIRECT_TX_COUNT_SHIFT 8U
#define COSMOS_PCIE_HOST_DMA_AUTO_RX_COUNT_SHIFT   16U
#define COSMOS_PCIE_HOST_DMA_AUTO_TX_COUNT_SHIFT   24U
#define COSMOS_PCIE_HOST_DMA_COUNT_MASK            0x000000FFU

#define COSMOS_PCIE_IRQ_LINK_CHANGE        (1U << 0)
#define COSMOS_PCIE_IRQ_BUS_MASTER_CHANGE  (1U << 1)
#define COSMOS_PCIE_IRQ_INTX_CHANGE        (1U << 2)
#define COSMOS_PCIE_IRQ_MSI_CHANGE         (1U << 3)
#define COSMOS_PCIE_IRQ_MSIX_CHANGE        (1U << 4)
#define COSMOS_PCIE_IRQ_CC_ENABLE_CHANGE   (1U << 5)
#define COSMOS_PCIE_IRQ_CC_SHN_CHANGE      (1U << 6)
#define COSMOS_PCIE_IRQ_AXI_WRITE_ERROR    (1U << 7)
#define COSMOS_PCIE_IRQ_AXI_READ_ERROR     (1U << 8)
#define COSMOS_PCIE_IRQ_MREQ_ERROR         (1U << 9)
#define COSMOS_PCIE_IRQ_CPLD_ERROR         (1U << 10)
#define COSMOS_PCIE_IRQ_CPLD_LENGTH_ERROR  (1U << 11)
#define COSMOS_PCIE_IRQ_STATE_CHANGE_MASK  0x0000007FU
#define COSMOS_PCIE_IRQ_FATAL_MASK         0x00000F80U
#define COSMOS_PCIE_IRQ_DEFINED_MASK       0x00000FFFU

#define COSMOS_PCIE_STATUS_LTSSM_MASK      0x0000003FU
#define COSMOS_PCIE_STATUS_LINK_UP         (1U << 8)
#define COSMOS_PCIE_LTSSM_L0               0x16U
#define COSMOS_PCIE_STATUS_DEFINED_MASK \
    (COSMOS_PCIE_STATUS_LTSSM_MASK | COSMOS_PCIE_STATUS_LINK_UP)

#define COSMOS_PCIE_FUNCTION_BUS_MASTER    (1U << 0)
#define COSMOS_PCIE_FUNCTION_MSI_ENABLE    (1U << 1)
#define COSMOS_PCIE_FUNCTION_MSIX_ENABLE   (1U << 2)
#define COSMOS_PCIE_FUNCTION_IRQ_DISABLE   (1U << 3)
#define COSMOS_PCIE_FUNCTION_MME_SHIFT     4U
#define COSMOS_PCIE_FUNCTION_MME_MASK      (7U << COSMOS_PCIE_FUNCTION_MME_SHIFT)
#define COSMOS_PCIE_FUNCTION_DEFINED_MASK  0x0000007FU
#define COSMOS_PCIE_FUNCTION_MME_MAX       3U

#define COSMOS_PCIE_NVME_CC_ENABLE         (1U << 0)
#define COSMOS_PCIE_NVME_CC_SHN_MASK       (3U << 1)
#define COSMOS_PCIE_NVME_CSTS_READY        (1U << 4)
#define COSMOS_PCIE_NVME_CSTS_SHST_MASK    (3U << 5)
#define COSMOS_PCIE_NVME_STATUS_DEFINED_MASK 0x00000077U

#define COSMOS_PCIE_ADMIN_CQ_VALID         (1U << 0)
#define COSMOS_PCIE_ADMIN_SQ_VALID         (1U << 1)
#define COSMOS_PCIE_ADMIN_CQ_IRQ_ENABLE    (1U << 2)
#define COSMOS_PCIE_ADMIN_DEFINED_MASK     0x00000007U

#define COSMOS_PCIE_IO_QUEUE_COUNT         8U
#define COSMOS_PCIE_IO_QUEUE_STRIDE        0x0008U
#define COSMOS_PCIE_IO_QUEUE_CONTROL_WORD  0x0004U

/* Synthesized PCI configuration constants; host BAR assignment is not exposed. */
#define COSMOS_PCIE_VENDOR_ID              0x10EEU
#define COSMOS_PCIE_DEVICE_ID              0x7028U
#define COSMOS_PCIE_CLASS_CODE             0x010802U
#define COSMOS_PCIE_BAR0_MASK              0xFFFFE000U
#define COSMOS_PCIE_BAR0_BYTES             0x00002000U

/*
 * host_lld.h NVME_CMD_FIFO_REG:
 * bits 3:0 qID, 14:8 cmdSlotTag, 23:16 cmdSeqNum, 31 cmdValid.
 * s_axi_reg.v packs the read data as
 * {1'b1, 7'b0, seq[7:0], 1'b0, slot[6:0], 4'b0, qID[3:0]}.
 */
#define COSMOS_PCIE_NVME_QUEUE_COUNT       9U
#define COSMOS_PCIE_NVME_MAX_QUEUE_ID      8U
#define COSMOS_PCIE_NVME_CMD_SLOT_COUNT    128U
#define COSMOS_PCIE_NVME_CMD_DWORDS        16U
#define COSMOS_PCIE_NVME_CMD_BYTES         64U
#define COSMOS_PCIE_NVME_CMD_QUEUE_MASK    0x0000000FU
#define COSMOS_PCIE_NVME_CMD_SLOT_SHIFT    8U
#define COSMOS_PCIE_NVME_CMD_SLOT_MASK     0x00007F00U
#define COSMOS_PCIE_NVME_CMD_SEQ_SHIFT     16U
#define COSMOS_PCIE_NVME_CMD_SEQ_MASK      0x00FF0000U
#define COSMOS_PCIE_NVME_CMD_VALID         0x80000000U
#define COSMOS_PCIE_NVME_CMD_RESERVED_MASK 0x7F0080F0U

/*
 * host_lld.h NVME_CPL_FIFO_REG / host_lld.c set_auto_nvme_cpl():
 * word0: cid[15:0], sqId[19:16]; word1: specific; word2:
 * cmdSlotTag[6:0], cplType[15:14], statusFieldWord[31:16].
 * AUTO completion writes word1 then word2 and releases the captured slot.
 */
#define COSMOS_PCIE_NVME_CPL_WORD0_OFFSET  0x0000U
#define COSMOS_PCIE_NVME_CPL_WORD1_OFFSET  0x0004U
#define COSMOS_PCIE_NVME_CPL_WORD2_OFFSET  0x0008U
#define COSMOS_PCIE_NVME_CPL_TYPE_ONLY     0U
#define COSMOS_PCIE_NVME_CPL_TYPE_AUTO     1U
#define COSMOS_PCIE_NVME_CPL_TYPE_RELEASE  2U
#define COSMOS_PCIE_NVME_CPL_STATUS_SC_SHIFT 1U
#define COSMOS_PCIE_NVME_CPL_STATUS_SC_MASK 0x01FEU
#define COSMOS_PCIE_NVME_CPL_STATUS_SCT_SHIFT 9U
#define COSMOS_PCIE_NVME_CPL_STATUS_SCT_MASK 0x0E00U
#define COSMOS_PCIE_NVME_CPL_STATUS_MORE   0x4000U
#define COSMOS_PCIE_NVME_CPL_STATUS_DNR    0x8000U
#define COSMOS_PCIE_NVME_CPL_STATUS_RESERVED_MASK 0x3001U

struct cosmos_pcie_nvme_command {
    unsigned int queue_id;
    unsigned int slot_tag;
    unsigned int sequence;
    unsigned int raw_dword[COSMOS_PCIE_NVME_CMD_DWORDS];
};

struct cosmos_pcie_nvme_completion {
    unsigned int queue_id;
    unsigned int slot_tag;
    unsigned int sequence;
    unsigned int cid;
    unsigned int specific;
    unsigned int status_word;
};

enum cosmos_pcie_nvme_completion_result {
    COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED = 0,
    COSMOS_PCIE_NVME_COMPLETION_COMMITTED = 1,
    /* A transport observed a failure after CQE publication started. */
    COSMOS_PCIE_NVME_COMPLETION_AMBIGUOUS = 2
};

enum cosmos_pcie_host_dma_direction {
    COSMOS_PCIE_HOST_TO_DEVICE = 0,
    COSMOS_PCIE_DEVICE_TO_HOST = 1
};

int cosmos_pcie_is_available(void);
int cosmos_pcie_service_irq(void);
int cosmos_pcie_nvme_status_word(unsigned int sct, unsigned int sc,
                                 unsigned int dnr,
                                 unsigned int *status_word);
int cosmos_pcie_nvme_fetch_command(struct cosmos_pcie_nvme_command *command);
int cosmos_pcie_nvme_io_sq_words(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high,
    unsigned int *word0, unsigned int *word1);
int cosmos_pcie_nvme_io_cq_words(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high, unsigned int *word0,
    unsigned int *word1);
int cosmos_pcie_nvme_configure_io_sq(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high);
int cosmos_pcie_nvme_configure_io_cq(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high);
enum cosmos_pcie_nvme_completion_result cosmos_pcie_nvme_post_completion(
    const struct cosmos_pcie_nvme_completion *completion);
enum cosmos_pcie_nvme_completion_result cosmos_pcie_nvme_post_completion_fields(
    unsigned int queue_id, unsigned int slot_tag, unsigned int sequence,
    unsigned int cid, unsigned int specific, unsigned int sct,
    unsigned int sc, unsigned int dnr);

/*
 * Submit one contiguous direct DMA transfer.  device_address must be in the
 * profile-owned data DMA pool; host_address_high:low is the 36-bit endpoint
 * address accepted by the pinned controller.  COSMOS_OK means the final
 * descriptor word was written and the operation is committed.  A non-OK
 * result is returned before that final write and is safe not to retry blindly.
 */
int cosmos_pcie_host_dma_submit_host_to_device(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length);
int cosmos_pcie_host_dma_submit_device_to_host(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length);
int cosmos_pcie_host_dma_poll_direct(
    enum cosmos_pcie_host_dma_direction direction);

/*
 * AUTO DMA uses the controller's captured NVMe command PRP state.  It does
 * not parse PRPs in software and the bitstream exposes no software-visible
 * auto-completion control bit; completion is tracked by the AUTO counters.
 */
int cosmos_pcie_host_dma_submit_auto_host_to_device(
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address);
int cosmos_pcie_host_dma_submit_auto_device_to_host(
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address);
int cosmos_pcie_host_dma_poll_auto(
    enum cosmos_pcie_host_dma_direction direction);

#endif
