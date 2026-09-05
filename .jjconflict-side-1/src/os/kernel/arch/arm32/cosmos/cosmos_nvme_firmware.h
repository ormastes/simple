#ifndef SIMPLE_COSMOS_NVME_FIRMWARE_H
#define SIMPLE_COSMOS_NVME_FIRMWARE_H

#include "cosmos_hal.h"

int cosmos_nvme_service_accept(struct cosmos_nvme_service *service,
                               const struct cosmos_nvme_command *command);

#endif
