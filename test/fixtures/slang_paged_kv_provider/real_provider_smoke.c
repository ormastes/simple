/* Requirements: REQ-001 REQ-004 REQ-005 REQ-009 REQ-010 REQ-011 REQ-012 REQ-013 REQ-014 REQ-015 */
#include "slang_paged_kv_provider.h"
#include "llama.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

int64_t slang_ggml_backend_init(void);
int64_t slang_ggml_capabilities(void);
int64_t slang_ggml_str_reset(void);
int64_t slang_ggml_str_push(int64_t byte);
int64_t slang_ggml_model_load(int64_t n_gpu_layers);
int64_t slang_ggml_request_configure(int64_t entries);
int64_t slang_ggml_request_create(int64_t n_ctx);
int64_t slang_ggml_request_close(int64_t request);
int64_t slang_ggml_request_cancel(int64_t request);
int64_t slang_ggml_request_str_reset(int64_t request);
int64_t slang_ggml_request_str_push(int64_t request, int64_t byte);
int64_t slang_ggml_request_tokenize(int64_t request, int64_t add_bos);
int64_t slang_ggml_request_token_at(int64_t request, int64_t index);
int64_t slang_ggml_request_eval_prompt(int64_t request);
int64_t slang_ggml_request_sample(int64_t request);
int64_t slang_ggml_vocab_size(void);
int64_t slang_ggml_request_logit_bits(int64_t request, int64_t index);
int64_t slang_ggml_free(void);

static void push_global(const char *value) {
    assert(slang_ggml_str_reset() == 0);
    while (*value) assert(slang_ggml_str_push((unsigned char)*value++) > 0);
}

static void push_request(int64_t request, const char *value) {
    assert(slang_ggml_request_str_reset(request) == 0);
    while (*value) assert(slang_ggml_request_str_push(request, (unsigned char)*value++) > 0);
}

static void decode_reference(struct llama_context *context, const llama_token *tokens, int32_t count, int32_t start) {
    struct llama_batch batch = llama_batch_init(count, 0, 1);
    assert(batch.token && batch.pos && batch.n_seq_id && batch.seq_id && batch.logits);
    batch.n_tokens = count;
    for (int32_t i = 0; i < count; ++i) {
        batch.token[i] = tokens[i];
        batch.pos[i] = start + i;
        batch.n_seq_id[i] = 1;
        batch.seq_id[i][0] = 0;
        batch.logits[i] = i + 1 == count;
    }
    assert(llama_decode(context, batch) == 0);
    llama_batch_free(batch);
}

static void assert_logit_close(int64_t index, uint32_t actual_bits, uint32_t expected_bits) {
    union { uint32_t bits; float value; } actual = { actual_bits };
    union { uint32_t bits; float value; } expected = { expected_bits };
    float tolerance = SLANG_PHYSICAL_LOGIT_REL_TOLERANCE * fmaxf(1.0f, fabsf(expected.value));
    if (!isfinite(actual.value) || !isfinite(expected.value) ||
        fabsf(actual.value - expected.value) > tolerance) {
        fprintf(stderr,
                "logit mismatch index=%lld actual=%g expected=%g abs_error=%g tolerance=%g\n",
                (long long)index, actual.value, expected.value,
                fabsf(actual.value - expected.value), tolerance);
        assert(0 && "physical logits exceed declared tolerance");
    }
}

int main(int argc, char **argv) {
    const uint32_t page_tokens = 4;
    const uint32_t page_capacity = 16;
    const uint32_t provider_context_tokens = page_tokens * page_capacity;

    assert(argc == 2);
    assert(slang_ggml_backend_init() == 0);
    push_global(argv[1]);
    assert(slang_ggml_model_load(0) == 0);
    assert((slang_ggml_capabilities() & SLANG_CAP_PHYSICAL_LIGHTWEIGHT_REQUESTS) != 0);
    assert(slang_ggml_request_configure(2) == 2);
    int64_t execution_namespace = slang_ggml_page_execution_namespace();
    assert(execution_namespace > 0);
    int64_t pool = slang_ggml_page_pool_create(
        execution_namespace, page_tokens, page_capacity, 64 * 1024 * 1024);
    assert(pool > 0 && slang_ggml_page_bytes(pool) > 0);
    int64_t request_a = slang_ggml_page_request_create(pool, 32);
    int64_t request_b = slang_ggml_page_request_create(pool, 32);
    assert(request_a > 0 && request_b > 0);
    push_request(request_a, "Hello world, this is a multi page cache bridge test.");
    push_request(request_b, "Hello world, this is a multi page cache bridge test.");
    int64_t tokens_a = slang_ggml_request_tokenize(request_a, 1);
    int64_t tokens_b = slang_ggml_request_tokenize(request_b, 1);
    assert(tokens_a == tokens_b && tokens_a > 4 && tokens_a <= 24);
    assert(slang_ggml_request_eval_prompt(request_a) < 0);
    int64_t vocabulary = slang_ggml_vocab_size();
    assert(vocabulary > 0);
    struct llama_model_params model_params = llama_model_default_params();
    model_params.n_gpu_layers = 0;
    struct llama_model *reference_model = llama_model_load_from_file(argv[1], model_params);
    assert(reference_model != NULL);
    struct llama_context_params context_params = llama_context_default_params();
    /* Logit parity requires the same execution profile as the physical pool. */
    context_params.n_ctx = provider_context_tokens;
    context_params.n_batch = provider_context_tokens;
    context_params.n_ubatch = provider_context_tokens;
    context_params.n_seq_max = 1;
    context_params.type_k = GGML_TYPE_F32;
    context_params.type_v = GGML_TYPE_F32;
    context_params.flash_attn_type = LLAMA_FLASH_ATTN_TYPE_DISABLED;
    context_params.offload_kqv = false;
    struct llama_context *reference_context = llama_init_from_model(reference_model, context_params);
    assert(reference_context != NULL);
    llama_token *reference_tokens = malloc((size_t)tokens_a * sizeof(*reference_tokens));
    assert(reference_tokens != NULL);
    for (int64_t i = 0; i < tokens_a; ++i) {
        int64_t token = slang_ggml_request_token_at(request_a, i);
        assert(token >= 0 && token <= INT32_MAX);
        reference_tokens[i] = (llama_token)token;
    }
    decode_reference(reference_context, reference_tokens, (int32_t)tokens_a, 0);
    const float *reference_logits = llama_get_logits_ith(reference_context, -1);
    assert(reference_logits != NULL);
    uint32_t *reference = malloc((size_t)vocabulary * sizeof(*reference));
    assert(reference != NULL);
    for (int64_t i = 0; i < vocabulary; ++i) {
        assert(isfinite(reference_logits[i]));
        memcpy(&reference[i], &reference_logits[i], sizeof(reference[i]));
    }

    int64_t page_count = (tokens_a + 3) / 4;
    int64_t pages_a[8] = {0};
    assert(page_count >= 2 && page_count <= 8);
    int64_t transaction = slang_ggml_page_table_begin(request_a, pool, 0, page_count);
    assert(transaction > 0);
    for (int64_t i = 0; i < page_count; ++i) {
        pages_a[i] = slang_ggml_page_reserve(pool);
        int64_t rows = tokens_a - i * 4;
        if (rows > 4) rows = 4;
        assert(pages_a[i] > 0);
        assert(slang_ggml_page_table_push(transaction, pages_a[i], 0, rows) == 0);
    }
    assert(slang_ggml_page_prefill(transaction, 0, 0, tokens_a) == 0);
    assert(slang_ggml_page_table_commit(transaction) == 0);
    for (int64_t i = 0; i < vocabulary; ++i) {
        int64_t bits = slang_ggml_request_logit_bits(request_a, i);
        assert(bits >= 0 && bits <= UINT32_MAX);
        assert_logit_close(i, (uint32_t)bits, reference[i]);
    }
    int64_t sample_a = slang_ggml_request_sample(request_a);
    assert(sample_a >= 0);

    int64_t page_b = slang_ggml_page_reserve(pool);
    assert(page_b > 0);
    int64_t final_rows = tokens_a - (page_count - 1) * 4;
    int64_t copied_rows = final_rows - 1;
    if (copied_rows > 0)
        assert(slang_ggml_page_copy_tail(pool, pages_a[page_count - 1], page_b, copied_rows) == 0);
    transaction = slang_ggml_page_table_begin(request_b, pool, 0, page_count);
    assert(transaction > 0);
    for (int64_t i = 0; i + 1 < page_count; ++i)
        assert(slang_ggml_page_table_push(transaction, pages_a[i], 4, 0) == 0);
    assert(slang_ggml_page_table_push(transaction, page_b, copied_rows, 1) == 0);
    assert(slang_ggml_page_boundary_logits(transaction, tokens_a - 1, tokens_a - 1) == 0);
    assert(slang_ggml_page_table_commit(transaction) == 0);
    for (int64_t i = 0; i < vocabulary; ++i) {
        int64_t bits = slang_ggml_request_logit_bits(request_b, i);
        assert(bits >= 0 && bits <= UINT32_MAX);
        assert_logit_close(i, (uint32_t)bits, reference[i]);
    }
    assert(slang_ggml_request_sample(request_b) == sample_a);

    llama_token next_token = (llama_token)sample_a;
    decode_reference(reference_context, &next_token, 1, (int32_t)tokens_a);
    reference_logits = llama_get_logits_ith(reference_context, -1);
    assert(reference_logits != NULL);
    for (int64_t i = 0; i < vocabulary; ++i) {
        assert(isfinite(reference_logits[i]));
        memcpy(&reference[i], &reference_logits[i], sizeof(reference[i]));
    }
    int64_t old_page_b = page_b;
    int64_t extra_full_page = 0;
    int64_t decode_page_count = page_count;
    page_b = slang_ggml_page_reserve(pool);
    assert(page_b > 0);
    if (final_rows < 4) {
        assert(slang_ggml_page_copy_tail(pool, old_page_b, page_b, final_rows) == 0);
    } else {
        extra_full_page = old_page_b;
        ++decode_page_count;
    }
    transaction = slang_ggml_page_table_begin(request_b, pool, 0, decode_page_count);
    assert(transaction > 0);
    for (int64_t i = 0; i + 1 < page_count; ++i)
        assert(slang_ggml_page_table_push(transaction, pages_a[i], 4, 0) == 0);
    if (extra_full_page > 0)
        assert(slang_ggml_page_table_push(transaction, extra_full_page, 4, 0) == 0);
    assert(slang_ggml_page_table_push(transaction, page_b, final_rows < 4 ? final_rows : 0, 1) == 0);
    assert(slang_ggml_page_decode(transaction, sample_a, tokens_a) == 0);
    assert(slang_ggml_page_table_commit(transaction) == 0);
    if (extra_full_page == 0)
        assert(slang_ggml_page_release(pool, old_page_b) == 0);
    for (int64_t i = 0; i < vocabulary; ++i) {
        int64_t bits = slang_ggml_request_logit_bits(request_b, i);
        assert(bits >= 0 && bits <= UINT32_MAX);
        assert_logit_close(i, (uint32_t)bits, reference[i]);
    }

    int64_t poisoned_page = slang_ggml_page_reserve(pool);
    int64_t published_final_rows = final_rows < 4 ? final_rows + 1 : 1;
    int64_t poison_page_count = decode_page_count;
    int published_tail_full = final_rows < 4 && published_final_rows == 4;
    assert(poisoned_page > 0);
    if (published_tail_full) {
        ++poison_page_count;
    } else {
        assert(slang_ggml_page_copy_tail(pool, page_b, poisoned_page, published_final_rows) == 0);
    }
    transaction = slang_ggml_page_table_begin(request_b, pool, 0, poison_page_count);
    assert(transaction > 0);
    for (int64_t i = 0; i + 1 < page_count; ++i)
        assert(slang_ggml_page_table_push(transaction, pages_a[i], 4, 0) == 0);
    if (extra_full_page > 0)
        assert(slang_ggml_page_table_push(transaction, extra_full_page, 4, 0) == 0);
    if (published_tail_full)
        assert(slang_ggml_page_table_push(transaction, page_b, 4, 0) == 0);
    assert(slang_ggml_page_table_push(transaction, poisoned_page,
                                      published_tail_full ? 0 : published_final_rows, 1) == 0);
    assert(slang_ggml_page_decode(transaction, sample_a, tokens_a + 1) == 0);
    assert(slang_ggml_page_decode(transaction, sample_a, -1) < 0);
    assert(slang_ggml_request_sample(request_b) < 0);
    assert(slang_ggml_page_table_abort(transaction) == 0);
    assert(slang_ggml_page_release(pool, poisoned_page) == 0);

    int64_t sealed_copy = slang_ggml_page_reserve(pool);
    assert(sealed_copy > 0);
    assert(slang_ggml_page_copy_tail(pool, pages_a[0], sealed_copy, 4) == 0);
    assert(slang_ggml_page_seal(pool, sealed_copy) == 0);
    assert(slang_ggml_page_seal(pool, sealed_copy) < 0);
    transaction = slang_ggml_page_table_begin(request_b, pool, 0, 1);
    assert(transaction > 0);
    assert(slang_ggml_page_table_push(transaction, sealed_copy, 4, 0) == 0);
    assert(slang_ggml_page_table_abort(transaction) == 0);
    assert(slang_ggml_page_release(pool, sealed_copy) == 0);

    int64_t page_c = slang_ggml_page_reserve(pool);
    assert(page_c > 0);
    transaction = slang_ggml_page_table_begin(request_b, pool, 0, 1);
    assert(transaction > 0);
    assert(slang_ggml_page_table_push(transaction, page_c, 1, 1) < 0);
    assert(slang_ggml_request_sample(request_b) < 0);
    assert(slang_ggml_page_table_abort(transaction) == 0);

    assert(slang_ggml_request_close(request_a) == 0);
    assert(slang_ggml_request_close(request_b) == 0);
    assert(slang_ggml_request_close(request_b) < 0);
    for (int64_t i = 0; i < page_count; ++i)
        assert(slang_ggml_page_release(pool, pages_a[i]) == 0);
    assert(slang_ggml_page_release(pool, page_b) == 0);
    if (extra_full_page > 0)
        assert(slang_ggml_page_release(pool, extra_full_page) == 0);
    assert(slang_ggml_page_release(pool, page_c) == 0);
    assert(slang_ggml_page_release(pool, page_c) < 0);
    int64_t cancelled_request = slang_ggml_page_request_create(pool, 32);
    int64_t cancelled_page = slang_ggml_page_reserve(pool);
    assert(cancelled_request > 0 && cancelled_page > 0);
    transaction = slang_ggml_page_table_begin(cancelled_request, pool, 0, 1);
    assert(transaction > 0);
    assert(slang_ggml_page_table_push(transaction, cancelled_page, 0, 1) == 0);
    assert(slang_ggml_request_cancel(cancelled_request) == 0);
    assert(slang_ggml_page_table_abort(transaction) < 0);
    assert(slang_ggml_page_release(pool, cancelled_page) == 0);
    assert(slang_ggml_page_allocated_bytes(pool) == 0);
    assert(slang_ggml_page_pool_destroy(pool) == 0);
    assert(slang_ggml_free() == 0);
    llama_free(reference_context);
    llama_model_free(reference_model);
    free(reference_tokens);
    free(reference);
    puts("STATUS: PASS real Slang paged provider");
    return 0;
}
