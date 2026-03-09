#pragma once

#include "mapper/mapper.h"
#include "../../cuda_host/mapper/mapper_host.h"
#include "mapper_host_impl.h"

#ifdef __cplusplus
extern "C" {
#endif

// Experimental GPU-backed queue provisioning (Module 57 Mode 5 target)
// - Create a GPU CQ (CUDA device pointer + controller-visible IOVA) and wire a host SQ to it.
// - Requires P2P/DBC-capable mapping and controller support for GPU PRPs.
int nvme_create_gpu_cq(NvmeDevice* dev,
                       uint16_t cqid,
                       void* gpu_cq_dev_ptr,
                       uint64_t gpu_cq_iova,
                       uint16_t gpu_cq_entries);

int nvme_create_host_sq_for_cq(NvmeDevice* dev,
                               uint16_t sq_entries,
                               uint16_t cqid);

#ifdef __cplusplus
}
#endif
