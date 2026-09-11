#ifndef SIMPLE_GPU_PROVIDER_ABI_V1_H
#define SIMPLE_GPU_PROVIDER_ABI_V1_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define SIMPLE_GPU_PROVIDER_ABI_MAJOR 1u
#define SIMPLE_GPU_PROVIDER_ABI_MINOR 0u

typedef uint64_t SimpleGpuHandleV1;
typedef int32_t SimpleGpuStatusV1;
typedef int64_t (*SimpleGpuOperationV1)(void);

enum {
    SIMPLE_GPU_BACKEND_CUDA = 1u,
    SIMPLE_GPU_BACKEND_VULKAN = 2u,
    SIMPLE_GPU_BACKEND_METAL = 4u
};

enum {
    SIMPLE_GPU_CAP_DEVICE_READBACK = 1u,
    SIMPLE_GPU_CAP_ASYNC_COMPLETION = 2u
};

enum {
    SIMPLE_GPU_STATUS_OK = 0,
    SIMPLE_GPU_STATUS_UNAVAILABLE = -1,
    SIMPLE_GPU_STATUS_INCOMPATIBLE = -2,
    SIMPLE_GPU_STATUS_INVALID = -3,
    SIMPLE_GPU_STATUS_BUSY = -4,
    SIMPLE_GPU_STATUS_TIMEOUT = -5,
    SIMPLE_GPU_STATUS_FAILED = -6,
    /* Submit did not reach a queue and created no completion. */
    SIMPLE_GPU_STATUS_REJECTED = -7,
    /* Submission may have reached a queue; host must retain/quarantine. */
    SIMPLE_GPU_STATUS_UNCERTAIN = -8
};

enum { SIMPLE_GPU_OP_COUNT = 1 };

typedef struct SimpleGpuSubmitV1 {
    uint32_t struct_size;
    uint32_t format;
    const uint8_t *data;
    uint64_t length;
    uint64_t correlation_id;
} SimpleGpuSubmitV1;
/* `data` is immutable and valid only for the duration of submit(). A provider
 * returning OK has copied/consumed it into provider-owned storage; retaining
 * the host pointer is an ABI violation. */

typedef struct SimpleGpuResourceDescV1 {
    uint32_t struct_size;
    uint32_t flags;
    uint64_t size_bytes;
    uint64_t usage_bits;
} SimpleGpuResourceDescV1;

typedef struct SimpleGpuReceiptV1 {
    uint32_t struct_size;
    int32_t status;
    uint64_t correlation_id;
    uint64_t provider_identity;
    uint64_t device_identity;
    uint64_t resource;
    uint64_t checksum;
    uint64_t device_elapsed_ns;
} SimpleGpuReceiptV1;
/* wait() may return OK only after the backend fence is terminal and all
 * receipt fields are final. completion_release() must synchronously drain or
 * cancel terminal work before returning OK. `checksum` is FNV-1a-64 over the
 * exact readback bytes; the host stages and verifies before committing output. */

typedef struct SimpleGpuBytesV1 {
    uint32_t struct_size;
    uint32_t reserved;
    uint8_t *data;
    uint64_t length;
} SimpleGpuBytesV1;

typedef struct SimpleGpuProviderAbiV1 {
    uint32_t struct_size;
    uint16_t abi_major;
    uint16_t abi_minor;
    uint64_t backend_bits;
    uint64_t capability_bits;
    uint64_t provider_identity;
    uint32_t operation_count;
    uint32_t reserved;
    const SimpleGpuOperationV1 *operations;
    SimpleGpuStatusV1 (*shutdown)(void);
    SimpleGpuStatusV1 (*session_open)(uint64_t, uint64_t, SimpleGpuHandleV1 *);
    SimpleGpuStatusV1 (*session_close)(SimpleGpuHandleV1);
    SimpleGpuStatusV1 (*submit)(SimpleGpuHandleV1, const SimpleGpuSubmitV1 *, SimpleGpuHandleV1 *);
    SimpleGpuStatusV1 (*wait)(SimpleGpuHandleV1, SimpleGpuHandleV1, uint64_t, SimpleGpuReceiptV1 *);
    SimpleGpuStatusV1 (*readback)(SimpleGpuHandleV1, SimpleGpuHandleV1, SimpleGpuBytesV1 *);
    SimpleGpuStatusV1 (*resource_alloc)(SimpleGpuHandleV1, const SimpleGpuResourceDescV1 *, SimpleGpuHandleV1 *);
    SimpleGpuStatusV1 (*resource_release)(SimpleGpuHandleV1, SimpleGpuHandleV1);
    SimpleGpuStatusV1 (*completion_release)(SimpleGpuHandleV1, SimpleGpuHandleV1);
} SimpleGpuProviderAbiV1;
/* session_close() is the final retirement fence: it must drain/cancel every
 * resource and completion belonging to the session before returning OK. */
/* Creation callbacks return REJECTED only when no native object/work exists.
 * Any other failure without a successfully drained handle is uncertain and
 * the host retains a quarantine that prevents provider unload. */

typedef const SimpleGpuProviderAbiV1 *(*SimpleGpuProviderQueryV1)(void);

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && UINTPTR_MAX == UINT64_MAX
_Static_assert(sizeof(SimpleGpuSubmitV1) == 32, "SimpleGpuSubmitV1 ABI drift");
_Static_assert(sizeof(SimpleGpuResourceDescV1) == 24, "SimpleGpuResourceDescV1 ABI drift");
_Static_assert(sizeof(SimpleGpuReceiptV1) == 56, "SimpleGpuReceiptV1 ABI drift");
_Static_assert(sizeof(SimpleGpuBytesV1) == 24, "SimpleGpuBytesV1 ABI drift");
_Static_assert(sizeof(SimpleGpuProviderAbiV1) == 120, "SimpleGpuProviderAbiV1 ABI drift");
#endif

#ifdef __cplusplus
}
#endif
#endif
