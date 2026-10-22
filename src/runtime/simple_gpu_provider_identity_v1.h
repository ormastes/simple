#ifndef SIMPLE_GPU_PROVIDER_IDENTITY_V1_H
#define SIMPLE_GPU_PROVIDER_IDENTITY_V1_H

#include "simple_gpu_provider_abi_v1.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Optional export; never changes SimpleGpuProviderAbiV1 or its receipts. */
#define SIMPLE_GPU_PROVIDER_DEVICE_IDENTITY_VERSION_V1 1u
typedef struct SimpleGpuProviderDeviceIdentityV1 {
    uint32_t struct_size;
    uint32_t version;
    uint8_t device_uuid[16];
    uint8_t driver_uuid[16];
    uint32_t vendor_id;
    uint32_t device_id;
    uint32_t device_type;
    uint32_t api_version;
    uint32_t driver_version;
    uint32_t reserved;
} SimpleGpuProviderDeviceIdentityV1;

typedef SimpleGpuStatusV1 (*SimpleGpuProviderDeviceIdentityFnV1)(
    SimpleGpuHandleV1 session, SimpleGpuHandleV1 completion,
    SimpleGpuProviderDeviceIdentityV1 *out);

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(SimpleGpuProviderDeviceIdentityV1) == 64,
    "SimpleGpuProviderDeviceIdentityV1 ABI drift");
#endif

#ifdef __cplusplus
}
static_assert(sizeof(SimpleGpuProviderDeviceIdentityV1) == 64,
    "SimpleGpuProviderDeviceIdentityV1 ABI drift");
#endif
#endif
