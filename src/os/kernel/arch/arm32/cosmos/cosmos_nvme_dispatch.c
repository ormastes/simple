#include "cosmos_nvme_dispatch.h"
#include "cosmos_nvme_media_policy.h"
#include "cosmos_pcie_regs.h"

int cosmos_nvme_dispatch_init(
    struct cosmos_nvme_dispatch *dispatch,
    struct cosmos_nvme_pcie_bridge *bridge,
    struct cosmos_nvme_service *io_service,
    struct cosmos_nvme_admin_service *admin_service) {
    if (!cosmos_nvme_media_policy_dispatch_init_valid(
            dispatch != 0 ? 1U : 0U, bridge != 0 ? 1U : 0U,
            io_service != 0 ? 1U : 0U,
            admin_service != 0 ? 1U : 0U,
            io_service != 0 && io_service->adapter.fetch_command != 0
                ? 1U : 0U,
            admin_service != 0 && admin_service->adapter.fetch_command != 0
                ? 1U : 0U)) {
        return COSMOS_INVALID;
    }
    dispatch->bridge = bridge;
    dispatch->io_service = io_service;
    dispatch->admin_service = admin_service;
    dispatch->faulted = 0U;
    return COSMOS_OK;
}

int cosmos_nvme_dispatch_poll(struct cosmos_nvme_dispatch *dispatch) {
    struct cosmos_pcie_nvme_command raw;
    int status;

    if (dispatch == 0 || dispatch->bridge == 0 ||
        dispatch->io_service == 0 || dispatch->admin_service == 0) {
        return COSMOS_INVALID;
    }
    if (dispatch->faulted != 0U) {
        return COSMOS_HW_ERROR;
    }
    status = cosmos_nvme_service_poll(dispatch->io_service);
    if (status != COSMOS_OK) {
        return status;
    }
    status = cosmos_nvme_admin_poll(dispatch->admin_service);
    if (status != COSMOS_OK) {
        return status;
    }
    status = cosmos_pcie_nvme_fetch_command(&raw);
    if (status == COSMOS_UNAVAILABLE) {
        return COSMOS_OK;
    }
    if (status != COSMOS_OK) {
        return status;
    }
    if (raw.queue_id == 0U) {
        struct cosmos_nvme_admin_command command;

        status = cosmos_nvme_pcie_decode_admin(&raw, &command);
        if (status != COSMOS_OK) {
            return status;
        }
        return cosmos_nvme_admin_accept(dispatch->admin_service, &command);
    } else {
        struct cosmos_nvme_command command;
        unsigned int index;
        unsigned int completion_queue_id;

        if (raw.queue_id > dispatch->admin_service->negotiated_queue_count ||
            raw.queue_id > COSMOS_NVME_ADMIN_MAX_IO_QUEUES) {
            status = cosmos_nvme_media_policy_dispatch_queue_status(
                raw.queue_id,
                dispatch->admin_service->negotiated_queue_count,
                0U, 0U, 0U);
            dispatch->faulted = 1U;
            return status;
        }
        index = raw.queue_id - 1U;
        completion_queue_id =
            dispatch->admin_service->submission_queues[index].
                completion_queue_id;
        status = cosmos_nvme_media_policy_dispatch_queue_status(
            raw.queue_id, dispatch->admin_service->negotiated_queue_count,
            dispatch->admin_service->submission_queues[index].valid,
            completion_queue_id,
            completion_queue_id != 0U &&
                completion_queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES
                ? dispatch->admin_service->completion_queues[
                    completion_queue_id - 1U].valid : 0U);
        if (status != COSMOS_OK) {
            dispatch->faulted = 1U;
            return status;
        }
        status = cosmos_nvme_pcie_decode_io(dispatch->bridge, &raw, &command);
        if (status != COSMOS_OK) {
            return status;
        }
        return cosmos_nvme_service_accept(dispatch->io_service, &command);
    }
}
