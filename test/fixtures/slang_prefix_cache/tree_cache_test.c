/* Contract test for the radix (tree) prefix-cache modes of slang_ggml_shim.c
 * against the mock llama.cpp in this directory. The mock keeps one length per
 * sequence id, so this checks what the shim asks of llama.cpp: shared prefixes
 * go through llama_memory_seq_cp (counted, never re-decoded), only the suffix
 * is decoded, positions stay consecutive per sequence, eviction frees ids. */
#include <assert.h>
#include <stdint.h>
int64_t slang_ggml_backend_init(void);
int64_t slang_ggml_str_reset(void);
int64_t slang_ggml_str_push(int64_t);
int64_t slang_ggml_model_load(int64_t);
int64_t slang_ggml_free(void);
int64_t slang_ggml_capabilities(void);
int64_t slang_ggml_prefix_cache_configure(int64_t, int64_t);
int64_t slang_ggml_prefix_cache_mode_configure(int64_t, int64_t);
int64_t slang_ggml_prefix_hits(void);
int64_t slang_ggml_prefix_tokens_reused(void);
int64_t slang_ggml_prefix_tokens_prefilled(void);
int64_t slang_ggml_prefix_evictions(void);
int64_t slang_ggml_prefix_resident_entries(void);
int64_t slang_ggml_tree_mode(void);
int64_t slang_ggml_tree_nodes(void);
int64_t slang_ggml_tree_cached_tokens(void);
int64_t slang_ggml_tree_shared_tokens(void);
int64_t slang_ggml_request_create(int64_t);
int64_t slang_ggml_request_close(int64_t);
int64_t slang_ggml_request_str_reset(int64_t);
int64_t slang_ggml_request_str_push(int64_t, int64_t);
int64_t slang_ggml_request_tokenize(int64_t, int64_t);
int64_t slang_ggml_request_prefix_prepare(int64_t);
int64_t slang_ggml_request_eval_prompt(int64_t);
int64_t slang_ggml_request_eval(int64_t, int64_t);
int64_t slang_ggml_request_sample(int64_t);
int64_t mock_llama_decoded_tokens(void);
int64_t mock_llama_seq_cp_tokens(void);
int64_t mock_llama_bad_positions(void);
void mock_llama_set_n_ubatch(uint32_t);

#define BUSY (-9)

static void text(int64_t h, const char *s) {
    assert(slang_ggml_request_str_reset(h) == 0);
    while (*s) assert(slang_ggml_request_str_push(h, (unsigned char)*s++) > 0);
}

/* Tokens are 10+byte (no bos), so a generated token 10+c re-tokenizes to itself. */
static void begin(int64_t h, const char *s, int64_t expected_reuse) {
    text(h, s);
    assert(slang_ggml_request_tokenize(h, 0) > 0);
    assert(slang_ggml_request_prefix_prepare(h) == expected_reuse);
    assert(slang_ggml_request_eval_prompt(h) > 0);
}

/* The mock sampler always answers end-of-generation, which ends the request. */
static void finish(int64_t h) { assert(slang_ggml_request_sample(h) == 2); }

int main(void) {
    slang_ggml_backend_init();
    slang_ggml_str_reset();
    for (const char *m = "model"; *m; m++) slang_ggml_str_push((unsigned char)*m);
    assert(slang_ggml_model_load(0) == 0);
    assert(slang_ggml_capabilities() == 31);
    assert(slang_ggml_prefix_cache_mode_configure(4, 0) < 0);
    assert(slang_ggml_prefix_cache_mode_configure(2, -1) < 0);
    assert(slang_ggml_tree_mode() == 0);
    /* Mode 2 = every matched token (the micro-batch is 1 in the mock). */
    assert(slang_ggml_prefix_cache_mode_configure(2, 0) == 2);
    assert(slang_ggml_tree_mode() == 2);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);

    int64_t h = slang_ggml_request_create(64);
    assert(h > 0);
    assert(slang_ggml_prefix_cache_mode_configure(0, 0) < 0);   /* fixed while a request is open */

    begin(h, "abcdefgh", 0);                       /* cold */
    finish(h);
    assert(slang_ggml_tree_nodes() == 1);
    assert(slang_ggml_prefix_resident_entries() == 1);
    assert(mock_llama_decoded_tokens() == 8);
    assert(mock_llama_seq_cp_tokens() == 0);

    begin(h, "abcdefXY", 6);                       /* branch: shares 6, decodes 2 */
    finish(h);
    assert(mock_llama_decoded_tokens() == 10);
    assert(mock_llama_seq_cp_tokens() == 6);
    assert(slang_ggml_tree_nodes() == 3);
    assert(slang_ggml_prefix_resident_entries() == 2);
    assert(slang_ggml_tree_cached_tokens() == 10);
    assert(slang_ggml_tree_shared_tokens() == 6);
    assert(slang_ggml_prefix_hits() == 1);
    assert(slang_ggml_prefix_tokens_reused() == 6);
    assert(slang_ggml_prefix_tokens_prefilled() == 10);

    begin(h, "abcdefgh", 7);                       /* exact repeat recomputes the last token */
    finish(h);
    assert(mock_llama_decoded_tokens() == 11);
    assert(slang_ggml_prefix_resident_entries() == 2);

    begin(h, "abcdefgh", 7);                       /* decoded tokens extend the cached path */
    assert(slang_ggml_request_eval(h, 10 + 'Q') == 0);
    assert(slang_ggml_request_eval(h, 10 + 'R') == 0);
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 3);
    begin(h, "abcdefghQRZ", 10);
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 4);

    /* Serialised per model: a second request cannot start while one holds the context. */
    int64_t h2 = slang_ggml_request_create(64);
    assert(h2 > 0);
    text(h, "abcdefgh");
    assert(slang_ggml_request_tokenize(h, 0) > 0);
    assert(slang_ggml_request_prefix_prepare(h) == 7);
    text(h2, "zzz");
    assert(slang_ggml_request_tokenize(h2, 0) > 0);
    assert(slang_ggml_request_prefix_prepare(h2) == BUSY);
    assert(slang_ggml_request_eval_prompt(h) > 0);
    finish(h);
    begin(h2, "zzz", 0);
    finish(h2);

    /* Shrinking the entry bound evicts LRU unpinned terminals and frees their ids. */
    int64_t terminals = slang_ggml_prefix_resident_entries();
    int64_t evictions = slang_ggml_prefix_evictions();
    assert(slang_ggml_prefix_cache_configure(2, 1024) == 2);
    assert(slang_ggml_prefix_resident_entries() == 2);
    assert(slang_ggml_prefix_evictions() == evictions + (terminals - 2));
    begin(h2, "qqqq", 0);
    finish(h2);
    assert(slang_ggml_prefix_resident_entries() == 2);
    assert(mock_llama_bad_positions() == 0);
    assert(slang_ggml_request_close(h) == 0);
    assert(slang_ggml_request_close(h2) == 0);

    /* Exact modes (1, 3) reuse whole micro-batches only: 6 shared tokens, n_ubatch 4. */
    assert(slang_ggml_prefix_cache_mode_configure(3, 0) == 3);
    mock_llama_set_n_ubatch(4);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    h = slang_ggml_request_create(64);
    assert(h > 0);
    begin(h, "abcdefgh", 0);
    finish(h);
    begin(h, "abcdefXY", 4);
    finish(h);
    assert(mock_llama_bad_positions() == 0);
    assert(slang_ggml_request_close(h) == 0);
    assert(slang_ggml_free() == 0);
    assert(slang_ggml_tree_nodes() == 0);
    return 0;
}
