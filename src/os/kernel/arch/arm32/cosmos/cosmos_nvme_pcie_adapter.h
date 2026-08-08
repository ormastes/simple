#ifndef SIMPLE_COSMOS_NVME_PCIE_ADAPTER_H
#define SIMPLE_COSMOS_NVME_PCIE_ADAPTER_H

#include "cosmos_hal.h"
#include "cosmos_nvme_admin.h"

struct cosmos_pcie_nvme_command;

typedef int (*cosmos_nvme_pcie_media_io_fn)(
    void *context, const struct cosmos_nvme_command *command);
typedef int (*cosmos_nvme_pcie_media_flush_fn)(void *context);
typedef int (*cosmos_nvme_pcie_media_zeroes_fn)(
    void *context, const struct cosmos_nvme_command *command);
typedef int (*cosmos_nvme_pcie_media_deallocate_fn)(
    void *context, const struct cosmos_nvme_command *command);

struct cosmos_nvme_pcie_bridge {
    void *media_context;
    cosmos_nvme_pcie_media_io_fn media_read;
    cosmos_nvme_pcie_media_io_fn media_program;
    cosmos_nvme_pcie_media_flush_fn media_flush;
    cosmos_nvme_pcie_media_zeroes_fn media_write_zeroes;
    cosmos_nvme_pcie_media_deallocate_fn media_deallocate;
    unsigned int block_bytes;
};

int cosmos_nvme_pcie_service_init(
    struct cosmos_nvme_service *service,
    struct cosmos_nvme_pcie_bridge *bridge,
    void *media_context,
    cosmos_nvme_pcie_media_io_fn media_read,
    cosmos_nvme_pcie_media_io_fn media_program,
    cosmos_nvme_pcie_media_flush_fn media_flush,
    cosmos_nvme_pcie_media_zeroes_fn media_write_zeroes,
    cosmos_nvme_pcie_media_deallocate_fn media_deallocate,
    unsigned int namespace_blocks_low,
    unsigned int namespace_blocks_high,
    unsigned int block_bytes);
int cosmos_nvme_pcie_decode_io(
    const struct cosmos_nvme_pcie_bridge *bridge,
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command);
int cosmos_nvme_pcie_decode_admin(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_admin_command *command);
enum cosmos_nvme_post_result cosmos_nvme_pcie_post_admin_completion(
    void *context, const struct cosmos_nvme_admin_completion *completion);
int cosmos_nvme_pcie_admin_service_init(
    struct cosmos_nvme_admin_service *service,
    struct cosmos_nvme_pcie_bridge *bridge,
    unsigned int namespace_blocks_low,
    unsigned int namespace_blocks_high,
    unsigned int block_bytes);
int cosmos_nvme_pcie_configure_io_sq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high);
int cosmos_nvme_pcie_configure_io_cq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high);

#endif
