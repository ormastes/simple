#include "slang_paged_kv_provider.h"
#include "provider_fixture.h"

#include <assert.h>
#include <stdint.h>

static int64_t kv(int64_t token, int64_t position) {
    return token * 1000 + position;
}

static void set_tokens(int64_t request, int64_t first, int64_t count) {
    for (int64_t i = 0; i < count; ++i)
        assert(fixture_request_set_token(request, i, first + i) == 0);
}

int main(void) {
    assert(slang_ggml_page_abi_version() == SLANG_PHYSICAL_PAGE_ABI_V1);
    int64_t execution_namespace = slang_ggml_page_execution_namespace();
    assert(execution_namespace > 0);
    assert(slang_ggml_page_pool_create(execution_namespace + 1, 4, 8, 256) < 0);
    assert(slang_ggml_page_pool_create(execution_namespace, 4, 8, 255) < 0);

    int64_t pool = slang_ggml_page_pool_create(execution_namespace, 4, 8, 256);
    assert(pool > 0);
    assert(slang_ggml_page_bytes(pool) == 32);
    assert(slang_ggml_page_allocated_bytes(pool) == 0);

    int64_t request_a = fixture_request_create(execution_namespace, 16);
    assert(request_a > 0);
    set_tokens(request_a, 10, 6);
    int64_t page_a = slang_ggml_page_reserve(pool);
    int64_t page_b = slang_ggml_page_reserve(pool);
    assert(page_a > 0 && page_b > 0 && page_a != page_b);
    assert(slang_ggml_page_allocated_bytes(pool) == 64);

    int64_t other_pool = slang_ggml_page_pool_create(
        execution_namespace, 4, 1, 32);
    int64_t other_page = slang_ggml_page_reserve(other_pool);
    assert(other_pool > 0 && other_page > 0 && other_page != page_a);
    assert(slang_ggml_page_release(other_pool, page_a) < 0);
    assert(slang_ggml_page_release(other_pool, other_page) == 0);
    assert(slang_ggml_page_pool_destroy(other_pool) == 0);

    int64_t txn = slang_ggml_page_table_begin(request_a, pool, 0, 2);
    assert(txn > 0);
    assert(slang_ggml_page_table_begin(request_a, pool, 0, 2) < 0);
    assert(slang_ggml_page_table_push(txn, page_a, 0, 4) == 0);
    assert(slang_ggml_page_table_push(txn, page_b, 0, 4) == 0);
    assert(slang_ggml_page_prefill(txn, 0, 0, 6) == 0);

    int64_t escape_request = fixture_request_create(execution_namespace, 8);
    assert(escape_request > 0);
    set_tokens(escape_request, 10, 4);
    int64_t escape_txn = slang_ggml_page_table_begin(escape_request, pool, 0, 1);
    assert(escape_txn > 0);
    assert(slang_ggml_page_table_push(escape_txn, page_a, 4, 0) < 0);
    assert(slang_ggml_page_table_abort(escape_txn) == 0);
    assert(fixture_request_close(escape_request) == 0);

    int64_t unpublished_copy = slang_ggml_page_reserve(pool);
    assert(unpublished_copy > 0);
    assert(slang_ggml_page_copy_tail(pool, page_a, unpublished_copy, 4) < 0);
    assert(slang_ggml_page_release(pool, unpublished_copy) == 0);
    assert(slang_ggml_page_table_commit(txn) == 0);
    assert(fixture_request_cursor(request_a) == 6);
    assert(fixture_request_sample(request_a) == kv(15, 5));
    assert(fixture_page_valid_rows(pool, page_a) == 4);
    assert(fixture_page_valid_rows(pool, page_b) == 2);
    assert(fixture_page_row(pool, page_a, 3) == kv(13, 3));
    assert(fixture_page_row(pool, page_b, 1) == kv(15, 5));
    assert(slang_ggml_page_release(pool, page_a) < 0);

    /* Reconstruct boundary logits without mutating shared pages. */
    assert(slang_ggml_page_seal(pool, page_b) == 0);
    int64_t boundary_request = fixture_request_create(execution_namespace, 16);
    assert(boundary_request > 0);
    set_tokens(boundary_request, 10, 6);
    txn = slang_ggml_page_table_begin(boundary_request, pool, 0, 2);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_b, 2, 0) == 0);
    assert(slang_ggml_page_boundary_logits(txn, 0, 0) == 0);
    assert(slang_ggml_page_table_commit(txn) < 0);
    assert(fixture_request_sample(boundary_request) < 0);
    txn = slang_ggml_page_table_begin(boundary_request, pool, 0, 2);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_b, 2, 0) == 0);
    assert(slang_ggml_page_boundary_logits(txn, 5, 5) == 0);
    assert(slang_ggml_page_table_commit(txn) == 0);
    assert(fixture_request_sample(boundary_request) == kv(15, 5));
    assert(fixture_request_close(boundary_request) == 0);

    /* Partial-tail COW preserves the first request and appends privately. */
    int64_t request_b = fixture_request_create(execution_namespace, 16);
    assert(request_b > 0);
    set_tokens(request_b, 10, 8);
    int64_t page_c = slang_ggml_page_reserve(pool);
    assert(page_c > 0);
    assert(slang_ggml_page_copy_tail(pool, page_b, page_c, 2) == 0);
    txn = slang_ggml_page_table_begin(request_b, pool, 0, 2);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_c, 2, 2) == 0);
    assert(slang_ggml_page_decode(txn, 16, 6) == 0);
    assert(slang_ggml_page_table_commit(txn) == 0);
    assert(fixture_request_cursor(request_b) == 7);
    assert(fixture_request_sample(request_b) == kv(16, 6));
    assert(fixture_request_sample(request_a) == kv(15, 5));
    assert(fixture_page_valid_rows(pool, page_b) == 2);

    /* A failed mutation rolls back its exclusive page and invalidates logits. */
    assert(slang_ggml_page_seal(pool, page_c) == 0);
    int64_t page_d = slang_ggml_page_reserve(pool);
    assert(page_d > 0);
    assert(slang_ggml_page_copy_tail(pool, page_c, page_d, 3) == 0);
    txn = slang_ggml_page_table_begin(request_b, pool, 0, 2);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_d, 3, 1) == 0);
    assert(fixture_fail_next_prefill() == 0);
    assert(slang_ggml_page_prefill(txn, 7, 7, 1) < 0);
    assert(fixture_request_sample(request_b) < 0);
    assert(slang_ggml_page_decode(txn, 17, 7) < 0);
    assert(slang_ggml_page_table_abort(txn) == 0);
    assert(fixture_page_valid_rows(pool, page_d) == 3);
    assert(fixture_page_row(pool, page_d, 3) < 0);
    assert(fixture_page_is_sealed(pool, page_d) == 0);
    assert(fixture_request_cursor(request_b) == 7);
    assert(fixture_request_sample(request_b) < 0);

    txn = slang_ggml_page_table_begin(request_b, pool, 0, 2);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_d, 3, 1) == 0);
    assert(slang_ggml_page_decode(txn, 17, 7) == 0);
    assert(slang_ggml_page_table_commit(txn) == 0);
    assert(fixture_request_cursor(request_b) == 8);
    assert(fixture_request_sample(request_b) == kv(17, 7));

    /* Commit failure consumes the transaction and restores staged KV. */
    int64_t page_e = slang_ggml_page_reserve(pool);
    assert(page_e > 0);
    txn = slang_ggml_page_table_begin(request_b, pool, 0, 3);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_d, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_e, 0, 4) == 0);
    assert(slang_ggml_page_decode(txn, 18, 8) == 0);
    assert(fixture_fail_next_commit() == 0);
    assert(slang_ggml_page_table_commit(txn) < 0);
    assert(slang_ggml_page_table_abort(txn) < 0);
    assert(fixture_page_valid_rows(pool, page_e) == 0);
    assert(fixture_request_cursor(request_b) == 8);
    assert(fixture_request_sample(request_b) < 0);

    txn = slang_ggml_page_table_begin(request_b, pool, 0, 3);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_a, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_d, 4, 0) == 0);
    assert(slang_ggml_page_table_push(txn, page_e, 0, 4) == 0);
    assert(slang_ggml_page_decode(txn, 18, 8) == 0);
    assert(slang_ggml_page_table_commit(txn) == 0);
    assert(fixture_request_cursor(request_b) == 9);
    assert(fixture_request_sample(request_b) == kv(18, 8));

    /* Copy failure never changes the source and poisoned destinations release. */
    int64_t page_f = slang_ggml_page_reserve(pool);
    assert(page_f > 0);
    assert(fixture_fail_next_copy() == 0);
    assert(slang_ggml_page_copy_tail(pool, page_d, page_f, 4) < 0);
    assert(fixture_page_row(pool, page_d, 3) == kv(17, 7));
    assert(slang_ggml_page_release(pool, page_f) == 0);

    /* Cancellation drains an outstanding transaction and its borrow. */
    int64_t request_c = fixture_request_create(execution_namespace, 4);
    int64_t page_g = slang_ggml_page_reserve(pool);
    assert(request_c > 0 && page_g > 0);
    assert(fixture_request_set_token(request_c, 0, 20) == 0);
    txn = slang_ggml_page_table_begin(request_c, pool, 16, 1);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_g, 0, 4) == 0);
    assert(fixture_request_cancel(request_c) == 0);
    assert(slang_ggml_page_table_abort(txn) < 0);
    assert(slang_ggml_page_release(pool, page_g) == 0);

    /* Gap writes, negative tokens, and position overflow become abort-only. */
    int64_t request_d = fixture_request_create(execution_namespace, 4);
    int64_t page_h = slang_ggml_page_reserve(pool);
    assert(request_d > 0 && page_h > 0);
    assert(fixture_request_set_token(request_d, 0, 21) == 0);
    txn = slang_ggml_page_table_begin(request_d, pool, 0, 1);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_h, 0, 4) == 0);
    assert(slang_ggml_page_decode(txn, 21, 3) < 0);
    assert(fixture_request_sample(request_d) < 0);
    assert(slang_ggml_page_table_abort(txn) == 0);
    assert(fixture_page_valid_rows(pool, page_h) == 0);

    txn = slang_ggml_page_table_begin(request_d, pool, 0, 1);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_h, 0, 4) == 0);
    assert(slang_ggml_page_decode(txn, -1, 0) < 0);
    assert(slang_ggml_page_table_abort(txn) == 0);

    txn = slang_ggml_page_table_begin(request_d, pool, INT64_MAX - 2, 1);
    assert(txn > 0);
    assert(slang_ggml_page_table_push(txn, page_h, 0, 4) < 0);
    assert(slang_ggml_page_table_abort(txn) == 0);
    assert(fixture_request_close(request_d) == 0);
    assert(slang_ggml_page_release(pool, page_h) == 0);

    /* Stale page generations never resolve. */
    page_h = slang_ggml_page_reserve(pool);
    assert(page_h > 0);
    int64_t stale_page = page_h;
    assert(slang_ggml_page_release(pool, page_h) == 0);
    page_h = slang_ggml_page_reserve(pool);
    assert(page_h > 0 && page_h != stale_page);
    assert(slang_ggml_page_release(pool, stale_page) < 0);
    assert(slang_ggml_page_release(pool, page_h) == 0);

    assert(slang_ggml_page_pool_destroy(pool) < 0);
    assert(fixture_request_close(request_a) == 0);
    assert(fixture_request_close(request_b) == 0);
    assert(slang_ggml_page_release(pool, page_a) == 0);
    assert(slang_ggml_page_release(pool, page_b) == 0);
    assert(slang_ggml_page_release(pool, page_c) == 0);
    assert(slang_ggml_page_release(pool, page_d) == 0);
    assert(slang_ggml_page_release(pool, page_e) == 0);
    assert(slang_ggml_page_allocated_bytes(pool) == 0);
    assert(slang_ggml_page_pool_destroy(pool) == 0);
    assert(slang_ggml_page_pool_destroy(pool) < 0);

    int64_t recreated_pool = slang_ggml_page_pool_create(
        execution_namespace, 4, 1, 32);
    int64_t recreated_page = slang_ggml_page_reserve(recreated_pool);
    assert(recreated_pool > 0 && recreated_page > 0 && recreated_page != page_a);
    assert(slang_ggml_page_release(recreated_pool, page_a) < 0);
    assert(slang_ggml_page_release(recreated_pool, recreated_page) == 0);
    assert(slang_ggml_page_pool_destroy(recreated_pool) == 0);
    return 0;
}
