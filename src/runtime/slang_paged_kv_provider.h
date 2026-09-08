#ifndef SLANG_PAGED_KV_PROVIDER_H
#define SLANG_PAGED_KV_PROVIDER_H

#include <stdint.h>

/* Optional Slang physical-page ABI v1.
 *
 * This all-or-nothing group extends the complete independent-request ABI.
 * A backend must advertise capability bit 32, export every declaration below,
 * and return ABI version 1. Slang calls no page entry point otherwise. Handles
 * are positive, generation-safe integers; success statuses are exactly zero
 * and failures are negative. No pointer crosses SFFI.
 *
 * slang_ggml_shim.c exports this interface only when it is compiled against a
 * compatible llama.cpp tree that provides llama-slang-paged.h. Stock upstream
 * llama.cpp builds keep the capability absent. Opaque snapshots and shared
 * sequence cells are not physical KV pages.
 */

#define SLANG_CAP_PHYSICAL_PAGED_KV INT64_C(32)
#define SLANG_CAP_PHYSICAL_LIGHTWEIGHT_REQUESTS INT64_C(64)
#define SLANG_PHYSICAL_PAGE_ABI_V1 INT64_C(1)

int64_t slang_ggml_page_abi_version(void);

/* Provider-owned generation identifying model weights, tokenizer, adapters,
 * KV dtype/layout, attention/position configuration, sharding, and ABI.
 */
int64_t slang_ggml_page_execution_namespace(void);

/* Pool admission reserves actual physical tensor storage within byte_limit. */
int64_t slang_ggml_page_pool_create(int64_t execution_namespace,
                                    int64_t page_tokens,
                                    int64_t page_capacity,
                                    int64_t byte_limit);
int64_t slang_ggml_page_pool_destroy(int64_t pool_handle);

/* Creates tokenizer/output/request identity without allocating a legacy llama
 * context. This separately negotiated extension is required for production
 * physical-mode memory qualification. */
int64_t slang_ggml_page_request_create(int64_t pool_handle, int64_t n_ctx);

/* Pages start request-private and writable. Seal makes a page immutable.
 * Release succeeds only after all references and active borrows have drained.
 */
int64_t slang_ggml_page_reserve(int64_t pool_handle);
int64_t slang_ggml_page_release(int64_t pool_handle, int64_t page_handle);
int64_t slang_ggml_page_seal(int64_t pool_handle, int64_t page_handle);

/* Copy valid_rows from a distinct sealed source into a compatible private,
 * writable destination. Failure preserves the source and may poison the
 * destination, which then must be released rather than published.
 */
int64_t slang_ggml_page_copy_tail(int64_t pool_handle,
                                  int64_t source_page,
                                  int64_t destination_page,
                                  int64_t valid_rows);

/* Exactly one transaction may be active per request. Begin stages a complete
 * ordered page table without modifying the published table or cursor. Push
 * accepts 0 <= valid_rows <= B, writable_capacity >= 0, and requires
 * valid_rows + writable_capacity <= B. For entry i, base is
 * table_base_position + i * B, independent of occupancy, and its writable
 * interval is [base + valid_rows, base + valid_rows + writable_capacity).
 * The provider rejects every multiplication or addition overflow.
 *
 * Every page that execution may mutate is transaction-exclusive: it cannot
 * alias the published table, a cache entry, or another transaction. This makes
 * failed or aborted KV writes discardable. At commit, every interior page is
 * full and sealed; only the final page may retain request-private writable
 * capacity. A multi-page cold prefill therefore stages multiple exclusive
 * pages in one transaction, fills/seals its interior pages, and commits once.
 *
 * Commit publishes the complete table, cursor, and newly produced logits
 * atomically; failure rolls back modified staging pages. Commit and abort both
 * consume the transaction handle, including failure. Failed push/execution
 * operations leave a live but failed transaction on which only abort is valid;
 * the Simple wrapper automatically aborts it. Abort must accept that failed
 * state, drop all staged references, and preserve published table/cursor. Any
 * failed transaction invalidates request logits until a later successful
 * logits-producing commit.
 */
int64_t slang_ggml_page_table_begin(int64_t request_handle,
                                    int64_t pool_handle,
                                    int64_t table_base_position,
                                    int64_t expected_pages);
int64_t slang_ggml_page_table_push(int64_t transaction_handle,
                                   int64_t page_handle,
                                   int64_t valid_rows,
                                   int64_t writable_capacity);

/* token_start indexes request-owned token storage. Boundary recomputation names
 * both the source token index and its absolute position. Logits remain owned by
 * the request across interleaving; failure invalidates sampling until a later
 * successful logits-producing commit. Page and request namespaces must match.
 * slang_ggml_request_sample may read only logits published by that commit.
 */
int64_t slang_ggml_page_prefill(int64_t transaction_handle,
                                int64_t start_position,
                                int64_t token_start,
                                int64_t token_count);
int64_t slang_ggml_page_decode(int64_t transaction_handle,
                               int64_t token,
                               int64_t position);
int64_t slang_ggml_page_boundary_logits(int64_t transaction_handle,
                                        int64_t boundary_token_index,
                                        int64_t boundary_position);
int64_t slang_ggml_page_table_commit(int64_t transaction_handle);
int64_t slang_ggml_page_table_abort(int64_t transaction_handle);

/* Request cancel/close aborts its transaction, releases its table mappings,
 * and drains page borrows before returning. Pool destruction returns busy while
 * any page/table/transaction reference exists. Model/backend destruction also
 * returns busy until all page pools have been destroyed.
 */

/* Physical tensor bytes, not serialized snapshot bytes. */
int64_t slang_ggml_page_allocated_bytes(int64_t pool_handle);
int64_t slang_ggml_page_bytes(int64_t pool_handle);

#endif
