#ifndef SIMPLE_COSMOS_NVME_FTL_MEDIA_H
#define SIMPLE_COSMOS_NVME_FTL_MEDIA_H

#include "cosmos_ftl.h"
#include "cosmos_nfc_regs.h"
#include "cosmos_nvme_pcie_adapter.h"
#include "cosmos_pcie_regs.h"

#define COSMOS_NVME_FTL_MEDIA_DSM_BYTES \
    (COSMOS_NVME_MAX_DSM_RANGES * COSMOS_NVME_DSM_RANGE_BYTES)

/*
 * The caller owns these DMA regions and must keep them exclusive while an
 * NVMe media callback is running. The adapter is intentionally single-flight:
 * the PCIe service dispatches one captured command at a time.
 */
struct cosmos_nvme_ftl_media {
    struct cosmos_ftl *ftl;
    unsigned int namespace_lba_low;
    unsigned int namespace_lba_high;
    unsigned int data_address;
    unsigned int spare_address;
    unsigned int completion_address;
    unsigned int status_report_address;
    unsigned int error_info_address;
    unsigned int nfc_retry_limit;
    unsigned int busy;
    cosmos_nvme_pcie_media_io_fn media_read;
    cosmos_nvme_pcie_media_io_fn media_program;
    cosmos_nvme_pcie_media_flush_fn media_flush;
    cosmos_nvme_pcie_media_zeroes_fn media_write_zeroes;
    cosmos_nvme_pcie_media_deallocate_fn media_deallocate;
};

int cosmos_nvme_ftl_media_init(
    struct cosmos_nvme_ftl_media *media, struct cosmos_ftl *ftl,
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address);

int cosmos_nvme_ftl_media_read(
    void *context, const struct cosmos_nvme_command *command);
int cosmos_nvme_ftl_media_program(
    void *context, const struct cosmos_nvme_command *command);
int cosmos_nvme_ftl_media_flush(void *context);
int cosmos_nvme_ftl_media_write_zeroes(
    void *context, const struct cosmos_nvme_command *command);
int cosmos_nvme_ftl_media_deallocate(
    void *context, const struct cosmos_nvme_command *command);

/* Install this as cosmos_ftl_backend.program_data for the media's FTL. */
int cosmos_nvme_ftl_media_program_data(
    void *context, unsigned int ppa, unsigned int lpn,
    unsigned long long generation);
int cosmos_nvme_ftl_media_copy_data(
    void *context, unsigned int source_ppa, unsigned int destination_ppa,
    unsigned int lpn, unsigned long long generation);

/* The shared FTL header owns this API; this declaration documents the seam. */
int cosmos_ftl_discard_page(struct cosmos_ftl *ftl, unsigned int lpn);

#endif
