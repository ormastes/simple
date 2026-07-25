#include <stdint.h>

#include "cosmos_storage.h"
#include "cosmos_ftl_nfc_backend.h"
#include "cosmos_nvme_dispatch.h"
#include "cosmos_nvme_ftl_media.h"

#if !COSMOS_IS_QEMU
#define COSMOS_STORAGE_GC_POLL_MASK 0xFFFFFU

static struct cosmos_ftl_nfc_backend storage_backend;
static struct cosmos_ftl storage_ftl;
static struct cosmos_nvme_ftl_media storage_media;
static struct cosmos_nvme_pcie_bridge storage_bridge;
static struct cosmos_nvme_service storage_io;
static struct cosmos_nvme_admin_service storage_admin;
static struct cosmos_nvme_dispatch storage_dispatch;
static unsigned int storage_gc_polls;
static unsigned int storage_prepared;
static unsigned int storage_ready;
#endif

int cosmos_storage_init(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    const struct cosmos_ftl_nfc_dma dma = {
        .metadata_address =
            COSMOS_NFC_DATA_POOL_BASE + COSMOS_NFC_PAGE_DATA_BYTES,
        .payload_address = COSMOS_NFC_DATA_POOL_BASE,
        .spare_address = COSMOS_NFC_SPARE_POOL_BASE,
        .error_info_address = COSMOS_NFC_ERROR_POOL_BASE,
        .completion_address = COSMOS_NFC_COMPLETION_POOL_BASE,
        .status_report_address = COSMOS_NFC_STATUS_POOL_BASE
    };
    int status;

    storage_prepared = 0U;
    storage_ready = 0U;
    status = cosmos_ftl_nfc_backend_init(
        &storage_backend, &dma, 0, COSMOS_FTL_NAMESPACE_PAGE_COUNT,
        COSMOS_FTL_BLOCK_COUNT, 0ULL);
    if (status == COSMOS_OK) {
        status = cosmos_ftl_init(
            &storage_ftl, &storage_backend.ftl,
            (unsigned int *)(uintptr_t)COSMOS_FTL_L2P_BASE,
            COSMOS_FTL_NAMESPACE_PAGE_COUNT,
            (struct cosmos_ftl_block *)(uintptr_t)
                COSMOS_FTL_BLOCK_TABLE_BASE,
            COSMOS_FTL_BLOCK_COUNT);
    }
    if (status == COSMOS_OK) {
        storage_prepared = 1U;
    }
    if (status == COSMOS_OK) {
        status = cosmos_ftl_nfc_backend_mount(&storage_backend);
    }
    if (status == COSMOS_OK) {
        status = cosmos_ftl_recover(&storage_ftl);
    }
    if (status == COSMOS_OK) {
        status = cosmos_nvme_ftl_media_init(
            &storage_media, &storage_ftl,
            COSMOS_NFC_DATA_POOL_BASE, COSMOS_NFC_SPARE_POOL_BASE,
            COSMOS_NFC_COMPLETION_POOL_BASE, COSMOS_NFC_STATUS_POOL_BASE,
            COSMOS_NFC_ERROR_POOL_BASE);
    }
    if (status == COSMOS_OK) {
        status = cosmos_nvme_pcie_service_init(
            &storage_io, &storage_bridge, &storage_media,
            storage_media.media_read, storage_media.media_program,
            storage_media.media_flush, storage_media.media_write_zeroes,
            storage_media.media_deallocate,
            COSMOS_FTL_NAMESPACE_BLOCK_COUNT, 0U,
            COSMOS_FTL_NVME_BLOCK_BYTES);
    }
    if (status == COSMOS_OK) {
        status = cosmos_nvme_pcie_admin_service_init(
            &storage_admin, &storage_bridge,
            COSMOS_FTL_NAMESPACE_BLOCK_COUNT, 0U,
            COSMOS_FTL_NVME_BLOCK_BYTES);
    }
    if (status == COSMOS_OK) {
        status = cosmos_nvme_dispatch_init(
            &storage_dispatch, &storage_bridge, &storage_io,
            &storage_admin);
    }
    if (status == COSMOS_OK) {
        storage_gc_polls = 0U;
        storage_ready = 1U;
    }
    return status;
#endif
}

int cosmos_storage_factory_initialize_erased(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    int status;

    if (storage_prepared == 0U || storage_ready != 0U) {
        return COSMOS_INVALID;
    }
    status = cosmos_ftl_nfc_backend_format(&storage_backend);
    if (status == COSMOS_OK) {
        status = cosmos_ftl_factory_initialize_erased(&storage_ftl);
    }
    return status;
#endif
}

int cosmos_storage_poll(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    int status;

    if (storage_ready == 0U) {
        return COSMOS_UNAVAILABLE;
    }
    status = cosmos_nvme_dispatch_poll(&storage_dispatch);
    if (status != COSMOS_OK) {
        return status;
    }
    storage_gc_polls++;
    if ((storage_gc_polls & COSMOS_STORAGE_GC_POLL_MASK) != 0U) {
        return COSMOS_OK;
    }
    status = cosmos_ftl_gc_step(&storage_ftl, 1U);
    if (status == COSMOS_UNAVAILABLE || status == COSMOS_RETRY) {
        return COSMOS_OK;
    }
    if (status != COSMOS_OK) {
        storage_ready = 0U;
    }
    return status;
#endif
}
