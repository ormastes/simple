#ifndef SIMPLE_COSMOS_NVME_ADMIN_H
#define SIMPLE_COSMOS_NVME_ADMIN_H

#include "cosmos_hal.h"

/* Bounded NVMe admin floor. It owns no PCIe, PRP, or persistent media state. */
#define COSMOS_NVME_ADMIN_SERVICE_BUDGET 8U
#define COSMOS_NVME_ADMIN_MAX_IO_QUEUES 4U
#define COSMOS_NVME_ADMIN_MAX_QUEUE_ENTRIES 64U
#define COSMOS_NVME_ADMIN_IDENTIFY_BYTES 4096U
#define COSMOS_NVME_ADMIN_SMART_BYTES 512U
#define COSMOS_NVME_ADMIN_NAMESPACE_ALL 0xFFFFFFFFU

#define COSMOS_NVME_ADMIN_DELETE_IO_SQ 0x00U
#define COSMOS_NVME_ADMIN_CREATE_IO_SQ 0x01U
#define COSMOS_NVME_ADMIN_GET_LOG_PAGE 0x02U
#define COSMOS_NVME_ADMIN_DELETE_IO_CQ 0x04U
#define COSMOS_NVME_ADMIN_CREATE_IO_CQ 0x05U
#define COSMOS_NVME_ADMIN_IDENTIFY 0x06U
#define COSMOS_NVME_ADMIN_ABORT 0x08U
#define COSMOS_NVME_ADMIN_SET_FEATURES 0x09U
#define COSMOS_NVME_ADMIN_GET_FEATURES 0x0AU
#define COSMOS_NVME_ADMIN_ASYNC_EVENT_REQUEST 0x0CU
#define COSMOS_NVME_ADMIN_FIRMWARE_COMMIT 0x10U
#define COSMOS_NVME_ADMIN_FIRMWARE_IMAGE_DOWNLOAD 0x11U
#define COSMOS_NVME_ADMIN_FORMAT_NVM 0x80U

#define COSMOS_NVME_ADMIN_IDENTIFY_NAMESPACE 0x00U
#define COSMOS_NVME_ADMIN_IDENTIFY_CONTROLLER 0x01U
#define COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES 0x07U
#define COSMOS_NVME_ADMIN_LOG_SMART_HEALTH 0x02U

#define COSMOS_NVME_ADMIN_SC_COMMAND_SEQUENCE_ERROR 0x0CU
#define COSMOS_NVME_ADMIN_SC_COMPLETION_QUEUE_INVALID 0x00U
#define COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER 0x01U
#define COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_SIZE 0x02U
#define COSMOS_NVME_ADMIN_SC_ABORT_COMMAND_LIMIT_EXCEEDED 0x03U
#define COSMOS_NVME_ADMIN_SC_AER_LIMIT_EXCEEDED 0x05U
#define COSMOS_NVME_ADMIN_SC_INVALID_INTERRUPT_VECTOR 0x08U
#define COSMOS_NVME_ADMIN_SC_INVALID_LOG_PAGE 0x09U
#define COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_DELETION 0x0CU
#define COSMOS_NVME_ADMIN_SC_FEATURE_NOT_SAVEABLE 0x0DU
#define COSMOS_NVME_ADMIN_SC_FEATURE_NOT_NAMESPACE_SPECIFIC 0x0FU

struct cosmos_nvme_admin_command {
    unsigned int queue_id;
    unsigned int slot_tag;
    unsigned int sequence;
    unsigned int cid;
    unsigned int opcode;
    unsigned int namespace_id;
    unsigned int cdw10;
    unsigned int cdw11;
    unsigned int cdw12;
    unsigned int cdw13;
    unsigned int payload_address_low;
    unsigned int payload_address_high;
    unsigned int payload_address2_low;
    unsigned int payload_address2_high;
    unsigned int payload_bytes;
    unsigned int invalid_field;
};

struct cosmos_nvme_admin_completion {
    unsigned int queue_id;
    unsigned int slot_tag;
    unsigned int sequence;
    unsigned int cid;
    unsigned int result_low;
    unsigned int result_high;
    struct cosmos_nvme_status status;
};

/* NOT_COMMITTED guarantees that the host payload is not visible. */
enum cosmos_nvme_admin_payload_result {
    COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED = 0,
    COSMOS_NVME_ADMIN_PAYLOAD_NOT_COMMITTED = 1,
    COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED = 2
};

struct cosmos_nvme_admin_adapter {
    void *context;
    int (*fetch_command)(void *context,
                         struct cosmos_nvme_admin_command *command);
    enum cosmos_nvme_post_result (*post_completion)(
        void *context, const struct cosmos_nvme_admin_completion *completion);
    enum cosmos_nvme_admin_payload_result (*write_payload)(
        void *context, const struct cosmos_nvme_admin_command *command,
        const unsigned char *payload, unsigned int payload_bytes);
    /* COSMOS_UNAVAILABLE means no event; COSMOS_OK returns completion DW0. */
    int (*poll_async_event)(void *context, unsigned int *result_low);
    int (*configure_io_sq)(
        void *context, unsigned int queue_id, unsigned int valid,
        unsigned int completion_queue_id, unsigned int entries,
        unsigned int address_low, unsigned int address_high);
    int (*configure_io_cq)(
        void *context, unsigned int queue_id, unsigned int valid,
        unsigned int irq_enable, unsigned int irq_vector,
        unsigned int entries, unsigned int address_low,
        unsigned int address_high);
};

struct cosmos_nvme_admin_queue {
    unsigned int entries;
    unsigned int completion_queue_id;
    unsigned int valid;
};

struct cosmos_nvme_admin_service {
    struct cosmos_nvme_admin_adapter adapter;
    unsigned int namespace_blocks_low;
    unsigned int namespace_blocks_high;
    unsigned int block_bytes;
    unsigned int negotiated_queue_count;
    struct cosmos_nvme_admin_queue completion_queues[
        COSMOS_NVME_ADMIN_MAX_IO_QUEUES];
    struct cosmos_nvme_admin_queue submission_queues[
        COSMOS_NVME_ADMIN_MAX_IO_QUEUES];
    enum cosmos_nvme_completion_state completion_state;
    int completion_terminal_status;
    struct cosmos_nvme_admin_completion pending_completion;
    unsigned int async_event_pending;
    struct cosmos_nvme_admin_command pending_async_event;
    unsigned char payload[COSMOS_NVME_ADMIN_IDENTIFY_BYTES];
};

int cosmos_nvme_admin_init(struct cosmos_nvme_admin_service *service,
                           const struct cosmos_nvme_admin_adapter *adapter,
                           unsigned int namespace_blocks_low,
                           unsigned int namespace_blocks_high,
                           unsigned int block_bytes);
int cosmos_nvme_admin_accept(struct cosmos_nvme_admin_service *service,
                             const struct cosmos_nvme_admin_command *command);
int cosmos_nvme_admin_poll(struct cosmos_nvme_admin_service *service);

#endif
