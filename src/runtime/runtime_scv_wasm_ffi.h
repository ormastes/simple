#ifndef SIMPLE_RUNTIME_SCV_WASM_FFI_H
#define SIMPLE_RUNTIME_SCV_WASM_FFI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Invoke the typed SCV WASM shim and return a runtime-owned NUL-terminated
 * copy of its parse output. The caller owns the result and must rt_free it.
 * Returns 0 when validation, allocation, loading, or parsing fails. */
int64_t spl_scv_wasm_parse_blob_copy(int64_t load_fn, int64_t parse_fn,
                                    int64_t free_fn, const char *grammar_ptr,
                                    int64_t grammar_len, const char *source_ptr,
                                    int64_t source_len);

#ifdef __cplusplus
}
#endif

#endif
