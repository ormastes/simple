#ifndef SIMPLE_COSMOS_NVME_DISPATCH_H
#define SIMPLE_COSMOS_NVME_DISPATCH_H

#include "cosmos_nvme_admin.h"
#include "cosmos_nvme_firmware.h"
#include "cosmos_nvme_pcie_adapter.h"

struct cosmos_nvme_dispatch {
    struct cosmos_nvme_pcie_bridge *bridge;
    struct cosmos_nvme_service *io_service;
    struct cosmos_nvme_admin_service *admin_service;
    unsigned int faulted;
};

int cosmos_nvme_dispatch_init(
    struct cosmos_nvme_dispatch *dispatch,
    struct cosmos_nvme_pcie_bridge *bridge,
    struct cosmos_nvme_service *io_service,
    struct cosmos_nvme_admin_service *admin_service);
int cosmos_nvme_dispatch_poll(struct cosmos_nvme_dispatch *dispatch);

#endif
