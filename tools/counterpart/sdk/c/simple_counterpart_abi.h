/* Simple Counterpart Conformance — stable provider adapter ABI, version 1.
 *
 * Design: doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md (§3.1)
 * Frozen Simple-side contracts: src/lib/common/spec/evidence/counterpart/model.spl
 *
 * Every provider package builds `libsimple_counterpart_<provider>.{so,dylib}` /
 * `simple_counterpart_<provider>.dll` exporting exactly one bootstrap symbol,
 * `scf_get_api`. The adapter may link an upstream library, drive a process, or
 * talk to a guest/remote; tests never guess upstream symbol names.
 *
 * Contract properties this header encodes:
 *   - one required bootstrap symbol, versioned function table
 *   - explicit `struct_size` so a caller can reject a table it cannot read
 *   - pointer+length data; NO NUL-termination is assumed anywhere
 *   - caller-owned output writer; the adapter allocates nothing the caller frees
 *   - no upstream object layout crosses the boundary
 *   - explicit instance ownership, `reset` between corpus cases
 *   - errors are STRUCTURED response envelopes, not an overloaded integer zero;
 *     the int32 status codes below describe the CALL, never the component's
 *     semantic verdict.
 *
 * C99, self-contained (stdint.h only).
 */

#ifndef SIMPLE_COUNTERPART_ABI_H
#define SIMPLE_COUNTERPART_ABI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ------------------------------------------------------------------------ */
/* Versioning                                                                */
/* ------------------------------------------------------------------------ */

/* Must stay in sync with COUNTERPART_ABI_VERSION in the frozen Simple model. */
#define SCF_ABI_V1 1u

/* ------------------------------------------------------------------------ */
/* Status codes                                                              */
/* ------------------------------------------------------------------------ */

/* Transport-level outcome of an ABI call. A component that ran and decided the
 * input is bad returns SCF_OK plus an error envelope through the response
 * writer — NOT a nonzero code. Nonzero here means the call itself could not be
 * performed. */
typedef int32_t scf_status_v1;

#define SCF_OK                 0  /* call performed; read the response envelope */
#define SCF_INVALID_ARG        1  /* null pointer, or a slice with data==NULL && size>0 */
#define SCF_UNKNOWN_COMPONENT  2  /* component_id is not in this adapter's manifest */
#define SCF_SCHEMA_MISMATCH    3  /* request envelope schema/version not supported */
#define SCF_INTERNAL           4  /* adapter-internal failure; not the caller's fault */

/* ------------------------------------------------------------------------ */
/* Data transfer                                                             */
/* ------------------------------------------------------------------------ */

/* Borrowed, non-owning byte range. Valid only for the duration of the call it
 * is passed to. `data` may be NULL only when `size` is 0. */
typedef struct {
    const uint8_t *data;
    uint64_t size;
} scf_slice_v1;

/* Caller-owned output sink. The adapter appends bytes by calling `write`; it
 * never allocates a buffer the caller has to free. `write` returns SCF_OK or a
 * status code; an adapter must stop writing on the first nonzero return and
 * propagate it. */
typedef struct {
    void *context;
    int32_t (*write)(void *context, const uint8_t *data, uint64_t size);
} scf_writer_v1;

/* Opaque per-adapter instance. Its layout is private to the adapter. */
typedef struct scf_instance_v1 scf_instance_v1;

/* ------------------------------------------------------------------------ */
/* Function table                                                            */
/* ------------------------------------------------------------------------ */

typedef struct {
    /* sizeof(scf_api_v1) as the ADAPTER compiled it. The caller must reject any
     * table whose struct_size is smaller than the caller's own expectation. */
    uint32_t struct_size;
    /* SCF_ABI_V1 for this revision. */
    uint32_t abi_version;

    /* Write the provider manifest (SDN text) to `output`. Instance-free: the
     * loader reads the manifest before deciding to open anything. */
    int32_t (*manifest)(scf_writer_v1 *output);

    /* Create an instance from SDN configuration text. On SCF_OK,
     * *out_instance is non-NULL and owned by the caller until close(). */
    int32_t (*open)(scf_slice_v1 configuration, scf_instance_v1 **out_instance);

    /* Run one component. `response_envelope` receives the SDN result (which may
     * itself be a structured error envelope); `trace_envelope` receives the SDN
     * execution/trace record. Either writer may be NULL, meaning "discard". */
    int32_t (*invoke)(scf_instance_v1 *instance,
                      scf_slice_v1 component_id,
                      scf_slice_v1 request_envelope,
                      scf_writer_v1 *response_envelope,
                      scf_writer_v1 *trace_envelope);

    /* Return the instance to its post-open state between corpus cases. */
    int32_t (*reset)(scf_instance_v1 *instance);

    /* Destroy the instance. Passing NULL is a no-op. */
    void (*close)(scf_instance_v1 *instance);
} scf_api_v1;

/* The one required export. Returns NULL when `requested_abi` is not supported,
 * so a caller negotiating v1 against a v2-only adapter gets NULL rather than a
 * table it would misread. */
const scf_api_v1 *scf_get_api(uint32_t requested_abi);

/* Convenience typedef for dlsym. */
typedef const scf_api_v1 *(*scf_get_api_fn)(uint32_t requested_abi);

#define SCF_GET_API_SYMBOL "scf_get_api"

#ifdef __cplusplus
}
#endif

#endif /* SIMPLE_COUNTERPART_ABI_H */
