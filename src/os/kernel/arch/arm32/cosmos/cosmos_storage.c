/*
 * Native acquisition boundary for the pure-Simple Cosmos+ storage policy.
 *
 * cosmos_storage_policy.spl owns initialization sequencing, readiness state,
 * factory-format admission, GC cadence, and status mapping.  This file owns
 * only the C object graph and the unavoidable FTL/NFC/NVMe ABI calls.
 */
#include <stdint.h>

#include "cosmos_storage_policy.h"
#include "cosmos_ftl_nfc_backend.h"
#include "cosmos_nvme_dispatch.h"
#include "cosmos_nvme_ftl_media.h"

#if defined(COSMOS_STORAGE_POLICY_TEST)
extern int cosmos_storage_policy_test_is_qemu;
#define COSMOS_STORAGE_BRIDGE_IS_QEMU cosmos_storage_policy_test_is_qemu
#else
#define COSMOS_STORAGE_BRIDGE_IS_QEMU COSMOS_IS_QEMU
#endif

#if !COSMOS_IS_QEMU
static struct cosmos_ftl_nfc_backend storage_backend;
static struct cosmos_ftl storage_ftl;
static struct cosmos_nvme_ftl_media storage_media;
static struct cosmos_nvme_pcie_bridge storage_bridge;
static struct cosmos_nvme_service storage_io;
static struct cosmos_nvme_admin_service storage_admin;
static struct cosmos_nvme_dispatch storage_dispatch;
#endif

int cosmos_storage_bridge_is_qemu(void) {
    return COSMOS_STORAGE_BRIDGE_IS_QEMU;
}

int cosmos_storage_bridge_backend_init(void) {
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

    return cosmos_ftl_nfc_backend_init(
        &storage_backend, &dma, 0, COSMOS_FTL_NAMESPACE_PAGE_COUNT,
        COSMOS_FTL_BLOCK_COUNT, 0ULL);
#endif
}

int cosmos_storage_bridge_ftl_init(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_ftl_init(
        &storage_ftl, &storage_backend.ftl,
        (unsigned int *)(uintptr_t)COSMOS_FTL_L2P_BASE,
        COSMOS_FTL_NAMESPACE_PAGE_COUNT,
        (struct cosmos_ftl_block *)(uintptr_t)COSMOS_FTL_BLOCK_TABLE_BASE,
        COSMOS_FTL_BLOCK_COUNT);
#endif
}

int cosmos_storage_bridge_backend_mount(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_ftl_nfc_backend_mount(&storage_backend);
#endif
}

int cosmos_storage_bridge_ftl_recover(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_ftl_recover(&storage_ftl);
#endif
}

int cosmos_storage_bridge_media_init(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_nvme_ftl_media_init(
        &storage_media, &storage_ftl,
        COSMOS_NFC_DATA_POOL_BASE, COSMOS_NFC_SPARE_POOL_BASE,
        COSMOS_NFC_COMPLETION_POOL_BASE, COSMOS_NFC_STATUS_POOL_BASE,
        COSMOS_NFC_ERROR_POOL_BASE);
#endif
}

int cosmos_storage_bridge_io_init(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_nvme_pcie_service_init(
        &storage_io, &storage_bridge, &storage_media,
        storage_media.media_read, storage_media.media_program,
        storage_media.media_flush, storage_media.media_write_zeroes,
        storage_media.media_deallocate,
        COSMOS_FTL_NAMESPACE_BLOCK_COUNT, 0U,
        COSMOS_FTL_NVME_BLOCK_BYTES);
#endif
}

int cosmos_storage_bridge_admin_init(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_nvme_pcie_admin_service_init(
        &storage_admin, &storage_bridge,
        COSMOS_FTL_NAMESPACE_BLOCK_COUNT, 0U,
        COSMOS_FTL_NVME_BLOCK_BYTES);
#endif
}

int cosmos_storage_bridge_dispatch_init(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_nvme_dispatch_init(
        &storage_dispatch, &storage_bridge, &storage_io, &storage_admin);
#endif
}

int cosmos_storage_bridge_backend_format(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_ftl_nfc_backend_format(&storage_backend);
#endif
}

int cosmos_storage_bridge_factory_initialize_erased(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_ftl_factory_initialize_erased(&storage_ftl);
#endif
}

int cosmos_storage_bridge_dispatch_poll(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_nvme_dispatch_poll(&storage_dispatch);
#endif
}

int cosmos_storage_bridge_gc_step(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    return cosmos_ftl_gc_step(&storage_ftl, 1U);
#endif
}
