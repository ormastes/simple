/* Narrow Rust-runtime provider. Pure-C owns the same engine through
 * runtime_native.c; an unconfigured wildcard build must emit no duplicate
 * endpoints from this translation unit. */
#if defined(SIMPLE_RUNTIME_RUST_COLLECTION_CAPTURE_PROVIDER)
#include "runtime.h"
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>
extern int64_t spl_collection_capture_text_copy(int64_t value, uint8_t* buffer,
                                               size_t max_len);
#define SPL_COLLECTION_CAPTURE_TEXT_COPY(value, buffer, max_len) \
    spl_collection_capture_text_copy((value), (uint8_t*)(buffer), (max_len))
#include "runtime_collection_capture_impl.h"
#endif
