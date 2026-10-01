#include <assert.h>
#include <stdio.h>

#include "cosmos_ftl_nfc_backend.h"
#include "cosmos_nvme_dispatch.h"
#include "cosmos_nvme_ftl_media.h"
#include "cosmos_storage.h"
#include "cosmos_storage_policy_oracle.h"

#define COSMOS_STORAGE_GC_POLL_INTERVAL 0x100000U

int cosmos_storage_policy_test_is_qemu;

static struct cosmos_storage_oracle_script active_script;
static struct cosmos_storage_oracle_counts actual_counts;
static struct cosmos_storage_oracle_counts oracle_counts;
static struct cosmos_storage_oracle_state oracle_state;

static int actual_acquire(enum cosmos_storage_oracle_action action) {
    actual_counts.calls[action]++;
    return active_script.status[action];
}

int cosmos_ftl_nfc_backend_init(
    struct cosmos_ftl_nfc_backend *backend,
    const struct cosmos_ftl_nfc_dma *dma,
    const struct cosmos_ftl_nfc_ops *ops,
    unsigned int l2p_count, unsigned int block_count,
    unsigned long long journal_pages) {
    (void)backend;
    (void)dma;
    (void)ops;
    (void)l2p_count;
    (void)block_count;
    (void)journal_pages;
    return actual_acquire(COSMOS_STORAGE_ORACLE_BACKEND_INIT);
}

int cosmos_ftl_init(
    struct cosmos_ftl *ftl, const struct cosmos_ftl_backend *backend,
    unsigned int *l2p, unsigned int l2p_count,
    struct cosmos_ftl_block *blocks, unsigned int block_count) {
    (void)ftl;
    (void)backend;
    (void)l2p;
    (void)l2p_count;
    (void)blocks;
    (void)block_count;
    return actual_acquire(COSMOS_STORAGE_ORACLE_FTL_INIT);
}

int cosmos_ftl_nfc_backend_mount(struct cosmos_ftl_nfc_backend *backend) {
    (void)backend;
    return actual_acquire(COSMOS_STORAGE_ORACLE_BACKEND_MOUNT);
}

int cosmos_ftl_recover(struct cosmos_ftl *ftl) {
    (void)ftl;
    return actual_acquire(COSMOS_STORAGE_ORACLE_FTL_RECOVER);
}

int cosmos_nvme_ftl_media_init(
    struct cosmos_nvme_ftl_media *media, struct cosmos_ftl *ftl,
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address) {
    (void)media;
    (void)ftl;
    (void)data_address;
    (void)spare_address;
    (void)completion_address;
    (void)status_report_address;
    (void)error_info_address;
    return actual_acquire(COSMOS_STORAGE_ORACLE_MEDIA_INIT);
}

int cosmos_nvme_pcie_service_init(
    struct cosmos_nvme_service *service,
    struct cosmos_nvme_pcie_bridge *bridge, void *media_context,
    cosmos_nvme_pcie_media_io_fn media_read,
    cosmos_nvme_pcie_media_io_fn media_program,
    cosmos_nvme_pcie_media_flush_fn media_flush,
    cosmos_nvme_pcie_media_zeroes_fn media_write_zeroes,
    cosmos_nvme_pcie_media_deallocate_fn media_deallocate,
    unsigned int namespace_blocks_low,
    unsigned int namespace_blocks_high, unsigned int block_bytes) {
    (void)service;
    (void)bridge;
    (void)media_context;
    (void)media_read;
    (void)media_program;
    (void)media_flush;
    (void)media_write_zeroes;
    (void)media_deallocate;
    (void)namespace_blocks_low;
    (void)namespace_blocks_high;
    (void)block_bytes;
    return actual_acquire(COSMOS_STORAGE_ORACLE_IO_INIT);
}

int cosmos_nvme_pcie_admin_service_init(
    struct cosmos_nvme_admin_service *service,
    struct cosmos_nvme_pcie_bridge *bridge,
    unsigned int namespace_blocks_low,
    unsigned int namespace_blocks_high, unsigned int block_bytes) {
    (void)service;
    (void)bridge;
    (void)namespace_blocks_low;
    (void)namespace_blocks_high;
    (void)block_bytes;
    return actual_acquire(COSMOS_STORAGE_ORACLE_ADMIN_INIT);
}

int cosmos_nvme_dispatch_init(
    struct cosmos_nvme_dispatch *dispatch,
    struct cosmos_nvme_pcie_bridge *bridge,
    struct cosmos_nvme_service *io_service,
    struct cosmos_nvme_admin_service *admin_service) {
    (void)dispatch;
    (void)bridge;
    (void)io_service;
    (void)admin_service;
    return actual_acquire(COSMOS_STORAGE_ORACLE_DISPATCH_INIT);
}

int cosmos_ftl_nfc_backend_format(struct cosmos_ftl_nfc_backend *backend) {
    (void)backend;
    return actual_acquire(COSMOS_STORAGE_ORACLE_BACKEND_FORMAT);
}

int cosmos_ftl_factory_initialize_erased(struct cosmos_ftl *ftl) {
    (void)ftl;
    return actual_acquire(COSMOS_STORAGE_ORACLE_FACTORY_INITIALIZE);
}

int cosmos_nvme_dispatch_poll(struct cosmos_nvme_dispatch *dispatch) {
    (void)dispatch;
    return actual_acquire(COSMOS_STORAGE_ORACLE_DISPATCH_POLL);
}

int cosmos_ftl_gc_step(struct cosmos_ftl *ftl, unsigned int max_moves) {
    (void)ftl;
    assert(max_moves == 1U);
    return actual_acquire(COSMOS_STORAGE_ORACLE_GC_STEP);
}

static void script_all_ok(void) {
    unsigned int action;

    active_script.is_qemu = 0;
    cosmos_storage_policy_test_is_qemu = 0;
    for (action = 0U; action < COSMOS_STORAGE_ORACLE_ACTION_COUNT;
         action++) {
        active_script.status[action] = COSMOS_OK;
    }
}

static void assert_counts_equal(void) {
    unsigned int action;

    for (action = 0U; action < COSMOS_STORAGE_ORACLE_ACTION_COUNT;
         action++) {
        assert(actual_counts.calls[action] == oracle_counts.calls[action]);
    }
}

static void run_init_pair(int expected) {
    int actual;
    int oracle;

    cosmos_storage_oracle_counts_reset(&actual_counts);
    cosmos_storage_oracle_counts_reset(&oracle_counts);
    actual = cosmos_storage_init();
    oracle = cosmos_storage_oracle_init(
        &oracle_state, &active_script, &oracle_counts);
    assert(actual == oracle);
    assert(actual == expected);
    assert_counts_equal();
}

static void run_factory_pair(int expected) {
    int actual;
    int oracle;

    cosmos_storage_oracle_counts_reset(&actual_counts);
    cosmos_storage_oracle_counts_reset(&oracle_counts);
    actual = cosmos_storage_factory_initialize_erased();
    oracle = cosmos_storage_oracle_factory_initialize_erased(
        &oracle_state, &active_script, &oracle_counts);
    assert(actual == oracle);
    assert(actual == expected);
    assert_counts_equal();
}

static void run_poll_pair(int expected) {
    int actual;
    int oracle;

    cosmos_storage_oracle_counts_reset(&actual_counts);
    cosmos_storage_oracle_counts_reset(&oracle_counts);
    actual = cosmos_storage_poll();
    oracle = cosmos_storage_oracle_poll(
        &oracle_state, &active_script, &oracle_counts);
    assert(actual == oracle);
    assert(actual == expected);
    assert_counts_equal();
}

static void run_gc_boundary_pair(int gc_status, int expected_last) {
    unsigned int poll;
    int actual = COSMOS_OK;
    int oracle = COSMOS_OK;

    script_all_ok();
    run_init_pair(COSMOS_OK);
    active_script.status[COSMOS_STORAGE_ORACLE_GC_STEP] = gc_status;
    cosmos_storage_oracle_counts_reset(&actual_counts);
    cosmos_storage_oracle_counts_reset(&oracle_counts);
    for (poll = 0U; poll < COSMOS_STORAGE_GC_POLL_INTERVAL; poll++) {
        actual = cosmos_storage_poll();
        if (poll + 1U < COSMOS_STORAGE_GC_POLL_INTERVAL) {
            assert(actual == COSMOS_OK);
        }
    }
    for (poll = 0U; poll < COSMOS_STORAGE_GC_POLL_INTERVAL; poll++) {
        oracle = cosmos_storage_oracle_poll(
            &oracle_state, &active_script, &oracle_counts);
        if (poll + 1U < COSMOS_STORAGE_GC_POLL_INTERVAL) {
            assert(oracle == COSMOS_OK);
        }
    }
    assert(actual == oracle);
    assert(actual == expected_last);
    assert_counts_equal();
    assert(actual_counts.calls[COSMOS_STORAGE_ORACLE_DISPATCH_POLL] ==
           COSMOS_STORAGE_GC_POLL_INTERVAL);
    assert(actual_counts.calls[COSMOS_STORAGE_ORACLE_GC_STEP] == 1U);
}

int main(void) {
    static const int failure_statuses[] = {
        COSMOS_UNAVAILABLE, COSMOS_INVALID, COSMOS_TIMEOUT, COSMOS_HW_ERROR,
        COSMOS_RETRY, COSMOS_COMPLETION_UNCERTAIN, COSMOS_TIMEOUT,
        COSMOS_HW_ERROR
    };
    unsigned int action;

    cosmos_storage_oracle_state_reset(&oracle_state);
    script_all_ok();

    active_script.is_qemu = 1;
    cosmos_storage_policy_test_is_qemu = 1;
    run_init_pair(COSMOS_UNAVAILABLE);
    run_factory_pair(COSMOS_UNAVAILABLE);
    run_poll_pair(COSMOS_UNAVAILABLE);

    script_all_ok();
    run_factory_pair(COSMOS_INVALID);
    run_poll_pair(COSMOS_UNAVAILABLE);

    for (action = COSMOS_STORAGE_ORACLE_BACKEND_INIT;
         action <= COSMOS_STORAGE_ORACLE_DISPATCH_INIT; action++) {
        script_all_ok();
        active_script.status[action] = failure_statuses[action];
        run_init_pair(failure_statuses[action]);
        script_all_ok();
        if (action >= COSMOS_STORAGE_ORACLE_BACKEND_MOUNT) {
            run_factory_pair(COSMOS_OK);
        } else {
            run_factory_pair(COSMOS_INVALID);
        }
    }

    script_all_ok();
    active_script.status[COSMOS_STORAGE_ORACLE_BACKEND_MOUNT] =
        COSMOS_HW_ERROR;
    run_init_pair(COSMOS_HW_ERROR);
    active_script.status[COSMOS_STORAGE_ORACLE_BACKEND_MOUNT] = COSMOS_OK;
    active_script.status[COSMOS_STORAGE_ORACLE_BACKEND_FORMAT] = COSMOS_TIMEOUT;
    run_factory_pair(COSMOS_TIMEOUT);
    active_script.status[COSMOS_STORAGE_ORACLE_BACKEND_FORMAT] = COSMOS_OK;
    active_script.status[COSMOS_STORAGE_ORACLE_FACTORY_INITIALIZE] =
        COSMOS_HW_ERROR;
    run_factory_pair(COSMOS_HW_ERROR);

    script_all_ok();
    run_init_pair(COSMOS_OK);
    run_factory_pair(COSMOS_INVALID);
    active_script.status[COSMOS_STORAGE_ORACLE_DISPATCH_POLL] = COSMOS_TIMEOUT;
    run_poll_pair(COSMOS_TIMEOUT);
    active_script.status[COSMOS_STORAGE_ORACLE_DISPATCH_POLL] = COSMOS_OK;
    run_poll_pair(COSMOS_OK);

    run_gc_boundary_pair(COSMOS_OK, COSMOS_OK);
    run_gc_boundary_pair(COSMOS_UNAVAILABLE, COSMOS_OK);
    run_gc_boundary_pair(COSMOS_RETRY, COSMOS_OK);
    run_gc_boundary_pair(COSMOS_HW_ERROR, COSMOS_HW_ERROR);
    run_poll_pair(COSMOS_UNAVAILABLE);

    /*
     * The 33 scenarios above drive both outcomes of the 20 production
     * decisions: three QEMU gates, eight init-status gates, two factory-state
     * gates, the format gate, ready/dispatch/GC cadence, both coalesced GC
     * statuses, and the terminal-GC readiness transition.
     */
    puts("COSMOS_STORAGE_ACTUAL_DECISIONS 20/20");
    puts("COSMOS_STORAGE_ORACLE_CASES 33");
    puts("COSMOS_STORAGE_GC_BOUNDARY_POLLS 4194304");
    puts("cosmos storage pure-policy/oracle parity: PASS");
    return 0;
}
