/* Contract test for the radix (tree) prefix-cache modes of slang_ggml_shim.c
 * against the mock llama.cpp in this directory. The mock keeps one length per
 * sequence id and honours kv_unified, so this checks what the shim asks of
 * llama.cpp: shared prefixes go through llama_memory_seq_cp (counted, never
 * re-decoded), only the suffix is decoded, positions stay consecutive per
 * sequence, partial seq_cp is never issued on non-unified KV (the mock aborts),
 * eviction frees ids, and reuse never exceeds the owner's exact span. */
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
int64_t slang_ggml_prefix_misses(void);
int64_t slang_ggml_prefix_tokens_reused(void);
int64_t slang_ggml_prefix_tokens_prefilled(void);
int64_t slang_ggml_prefix_evictions(void);
int64_t slang_ggml_prefix_resident_entries(void);
int64_t slang_ggml_prefix_restore_failures(void);
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
int64_t slang_ggml_request_token_at(int64_t, int64_t);
int64_t slang_ggml_request_embed_eval(int64_t);
int64_t slang_ggml_request_rerank_tokenize(int64_t, int64_t);
int64_t slang_ggml_request_tokens_set(int64_t, const uint8_t *, int64_t);
int64_t mock_llama_memory_clears(void);
int64_t mock_llama_decode_calls(void);
int64_t mock_llama_decoded_tokens(void);
int64_t mock_llama_seq_cp_tokens(void);
int64_t mock_llama_bad_positions(void);
int64_t mock_llama_stale_leaks(void);
int64_t mock_llama_restore_calls(void);
int64_t mock_llama_short_first_decodes(void);
void mock_llama_set_n_ubatch(uint32_t);
void mock_llama_fail_decode_once(void);
void mock_llama_fail_restore_once(void);
void mock_llama_fail_seq_cp_once(void);
int mock_llama_last_kv_unified(void);

#define BUSY (-9)

static void text(int64_t h, const char *s) {
    assert(slang_ggml_request_str_reset(h) == 0);
    while (*s) assert(slang_ggml_request_str_push(h, (unsigned char)*s++) > 0);
}

/* Tokens are 10+byte (no bos), so a generated token 10+c re-tokenizes to itself. */
static int64_t prepare(int64_t h, const char *s) {
    text(h, s);
    assert(slang_ggml_request_tokenize(h, 0) > 0);
    return slang_ggml_request_prefix_prepare(h);
}
static void begin(int64_t h, const char *s, int64_t expected_reuse) {
    assert(prepare(h, s) == expected_reuse);
    assert(slang_ggml_request_eval_prompt(h) > 0);
}

/* The mock sampler always answers end-of-generation, which ends the request. */
static void finish(int64_t h) { assert(slang_ggml_request_sample(h) == 2); }

static void reload(int64_t n_gpu_layers) {
    slang_ggml_str_reset();
    for (const char *m = "model"; *m; m++) slang_ggml_str_push((unsigned char)*m);
    assert(slang_ggml_model_load(n_gpu_layers) == 0);
}

int main(void) {
    slang_ggml_backend_init();
    reload(0);
    assert(slang_ggml_capabilities() == (31 | 256 | 512));
    assert(slang_ggml_prefix_cache_mode_configure(5, 0) < 0);
    assert(slang_ggml_prefix_cache_mode_configure(2, -1) < 0);
    assert(slang_ggml_tree_mode() == 0);

    /* ---- mode 2: every matched token (the micro-batch is 1 in the mock) ---- */
    assert(slang_ggml_prefix_cache_mode_configure(2, 0) == 2);
    assert(slang_ggml_tree_mode() == 2);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    int64_t h = slang_ggml_request_create(64);
    assert(h > 0);
    assert(mock_llama_last_kv_unified() == 1);                  /* mode 2: unified KV */
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
    /* cold 8 + branch suffix 2 + exact repeat (only the last token) 1 */
    assert(mock_llama_decoded_tokens() == 11);
    assert(slang_ggml_prefix_resident_entries() == 2);

    /* Restore failure: seq_cp that leaves the new sequence short is detected,
     * counted, and the request prefills everything. */
    int64_t failures = slang_ggml_prefix_restore_failures();
    mock_llama_fail_seq_cp_once();
    begin(h, "abcdefgh", 0);
    finish(h);
    assert(slang_ggml_prefix_restore_failures() == failures + 1);

    /* The embedding entries are refused on a tree request: embed_eval would
     * clear the shared tree context, and rerank_tokenize / tokens_set would
     * overwrite the token path a held lease pins. Nothing is decoded, cleared
     * or overwritten, and the request then finishes normally. */
    begin(h, "abcdefgh", 7);
    int64_t clears = mock_llama_memory_clears();
    int64_t decodes = mock_llama_decode_calls();
    const uint8_t raw_ids[8] = {1, 0, 0, 0, 2, 0, 0, 0};
    assert(slang_ggml_request_embed_eval(h) == -8);
    assert(slang_ggml_request_rerank_tokenize(h, 2) == -8);
    assert(slang_ggml_request_tokens_set(h, raw_ids, 8) == -8);
    assert(mock_llama_memory_clears() == clears);
    assert(mock_llama_decode_calls() == decodes);
    assert(slang_ggml_request_token_at(h, 0) == 10 + 'a');
    assert(slang_ggml_request_token_at(h, 7) == 10 + 'h');
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 2);

    begin(h, "abcdefgh", 7);                       /* decoded tokens extend the cached path */
    assert(slang_ggml_request_eval(h, 10 + 'Q') == 0);
    assert(slang_ggml_request_eval(h, 10 + 'R') == 0);
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 3);
    begin(h, "abcdefghQRZ", 10);
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 4);

    /* Serialised per model: a second request cannot start while one holds the
     * context, and refuses a capacity change under the active request. */
    int64_t h2 = slang_ggml_request_create(64);
    assert(h2 > 0);
    assert(prepare(h, "abcdefgh") == 7);
    assert(prepare(h2, "zzz") == BUSY);
    assert(slang_ggml_prefix_cache_configure(2, 1024) == BUSY);
    assert(slang_ggml_request_eval_prompt(h) > 0);
    finish(h);
    begin(h2, "zzz", 0);
    finish(h2);

    /* Abandoned request (closed without finishing) releases the context. */
    assert(prepare(h, "abcdefgh") == 7);
    assert(prepare(h2, "zzz") == BUSY);
    assert(slang_ggml_request_close(h) == 0);
    h = slang_ggml_request_create(64);
    assert(h > 0);
    begin(h2, "zzzz", 3);
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

    /* "No KV slot" on a unified KV evicts an unpinned terminal and retries. */
    evictions = slang_ggml_prefix_evictions();
    assert(prepare(h, "failcase") == 0);
    mock_llama_fail_decode_once();
    assert(slang_ggml_request_eval_prompt(h) > 0);
    finish(h);
    assert(slang_ggml_prefix_evictions() > evictions);

    /* Pinned owner survives: with only the pinned owner resident, a "no slot"
     * result finds nothing to evict, fails the request, and keeps the owner. */
    assert(slang_ggml_prefix_cache_configure(1, 1024) == 1);
    begin(h, "pinowner", 0);
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 1);
    assert(prepare(h, "pinownerX") == 8);
    mock_llama_fail_decode_once();
    assert(slang_ggml_request_eval_prompt(h) < 0);
    assert(slang_ggml_prefix_resident_entries() >= 1);
    begin(h, "pinowner", 7);                       /* the owner is still there */
    finish(h);

    /* Capacity 0 keeps nothing, and a request still completes. */
    assert(slang_ggml_prefix_cache_configure(0, 0) == 0);
    assert(slang_ggml_prefix_resident_entries() == 0);
    begin(h, "nothing", 0);
    finish(h);
    assert(slang_ggml_prefix_resident_entries() == 0);
    assert(slang_ggml_tree_nodes() == 0);
    assert(mock_llama_bad_positions() == 0);
    assert(slang_ggml_request_close(h) == 0);
    assert(slang_ggml_request_close(h2) == 0);

    /* ---- exact modes (1 and 3): reuse stops at the owner's exact span ---- */
    mock_llama_set_n_ubatch(4);
    for (int mode = 1; mode <= 3; mode += 2) {
        assert(slang_ggml_prefix_cache_mode_configure(mode, 0) == mode);
        assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
        h = slang_ggml_request_create(64);
        assert(h > 0);
        assert(mock_llama_last_kv_unified() == (mode == 3 ? 0 : 1));   /* mode 3 is per-sequence streams */
        begin(h, "abcdefgh", 0);
        finish(h);
        begin(h, "abcdefXY", 4);                   /* 6 shared tokens, whole micro-batches: 4 */
        finish(h);
        /* Owner: 10-token prompt, 6 generated tokens (k..p). Its exact span is
         * (10-1)/4*4 = 8: cells 8..15 came from partial chunks and generation. */
        begin(h, "ABCDEFGHIJ", 0);
        for (const char *g = "klmnop"; *g; g++)
            assert(slang_ggml_request_eval(h, 10 + (unsigned char)*g) == 0);
        finish(h);
        /* A follow-up that matches all 16 owner cells may reuse only 8. */
        begin(h, "ABCDEFGHIJklmnopXY", 8);
        finish(h);
        assert(mock_llama_bad_positions() == 0);
        assert(slang_ggml_request_close(h) == 0);
    }

    /* Mode 2 has no exact cap: the same follow-up reuses all 16 matched cells. */
    assert(slang_ggml_prefix_cache_mode_configure(2, 0) == 2);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    h = slang_ggml_request_create(64);
    begin(h, "ABCDEFGHIJ", 0);
    for (const char *g = "klmnop"; *g; g++)
        assert(slang_ggml_request_eval(h, 10 + (unsigned char)*g) == 0);
    finish(h);
    begin(h, "ABCDEFGHIJklmnopXY", 16);
    finish(h);
    assert(slang_ggml_request_close(h) == 0);

    /* Mode 3 stale cells (C2 of slang_tree_kv_gemma_branching_digest_differs_on_vulkan_2026-11-22.md):
     * a stream carries the K/V cells of whatever ran on it before. A reused
     * stream must reach the decode with nothing past its own frontier, whether
     * the request is a warm hit on a longer owner or a cold request on a stream
     * freed by an earlier long one. The warm prefix goes through host memory
     * (state_seq get/set), not a whole-stream copy. */
    /* Default mode 3 reuses the prefix in place (no host restore), while still
     * zeroing recycled streams on cold allocs. Use a 16-cell owner so there is
     * a real tail past the 8-token reused frontier. */
    assert(slang_ggml_prefix_cache_mode_configure(3, 0) == 3);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    h = slang_ggml_request_create(64);
    begin(h, "0123456789", 0);
    for (const char *g = "klmnop"; *g; g++)
        assert(slang_ggml_request_eval(h, 10 + (unsigned char)*g) == 0);
    finish(h);
    int64_t restores = mock_llama_restore_calls();
    begin(h, "01234567xy", 8);
    finish(h);
    assert(mock_llama_restore_calls() == restores);
    assert(slang_ggml_request_close(h) == 0);
    /* Mode 4 = mode 3 plus the host restore (zero stale tail on warm hits). */
    assert(slang_ggml_prefix_cache_mode_configure(4, 0) == 4);
    assert(slang_ggml_tree_mode() == 3);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    h = slang_ggml_request_create(64);
    begin(h, "0123456789", 0);
    for (const char *g = "klmnop"; *g; g++)
        assert(slang_ggml_request_eval(h, 10 + (unsigned char)*g) == 0);
    finish(h);                                             /* owner stream holds 16 cells */
    int64_t leaks = mock_llama_stale_leaks();
    restores = mock_llama_restore_calls();
    begin(h, "01234567xy", 8);                             /* shares 8 of the owner's 16 */
    finish(h);
    assert(mock_llama_restore_calls() == restores + 1);
    assert(mock_llama_stale_leaks() == leaks);             /* the owner's tail did not follow */
    assert(slang_ggml_request_close(h) == 0);

    /* Mode 4 direct eval (without calling prefix_prepare first) must also run
     * the deferred host restore instead of silently reusing in place. */
    h = slang_ggml_request_create(64);
    leaks = mock_llama_stale_leaks();
    restores = mock_llama_restore_calls();
    text(h, "01234567ab");
    assert(slang_ggml_request_tokenize(h, 0) == 10);
    assert(slang_ggml_request_eval_prompt(h) == 10);
    finish(h);
    assert(mock_llama_restore_calls() == restores + 1);
    assert(mock_llama_stale_leaks() == leaks);
    assert(slang_ggml_request_close(h) == 0);

    /* A restore that fails is a MISS: nothing reused, the failure counted,
     * hits/reused rolled back and misses incremented, stream re-zeroed, and
     * the request still completes. */
    h = slang_ggml_request_create(64);
    int64_t rfail = slang_ggml_prefix_restore_failures();
    int64_t hits_before = slang_ggml_prefix_hits();
    int64_t misses_before = slang_ggml_prefix_misses();
    int64_t reused_before = slang_ggml_prefix_tokens_reused();
    leaks = mock_llama_stale_leaks();
    mock_llama_fail_restore_once();
    begin(h, "01234567zz", 0);
    finish(h);
    assert(slang_ggml_prefix_restore_failures() == rfail + 1);
    assert(slang_ggml_prefix_hits() == hits_before);
    assert(slang_ggml_prefix_misses() == misses_before + 1);
    assert(slang_ggml_prefix_tokens_reused() == reused_before);
    assert(mock_llama_stale_leaks() == leaks);
    assert(slang_ggml_request_close(h) == 0);

    /* Mode 4 direct eval with a failing restore must also roll back to cold eval. */
    h = slang_ggml_request_create(64);
    rfail = slang_ggml_prefix_restore_failures();
    hits_before = slang_ggml_prefix_hits();
    misses_before = slang_ggml_prefix_misses();
    reused_before = slang_ggml_prefix_tokens_reused();
    leaks = mock_llama_stale_leaks();
    mock_llama_fail_restore_once();
    text(h, "01234567ww");
    assert(slang_ggml_request_tokenize(h, 0) == 10);
    assert(slang_ggml_request_eval_prompt(h) == 10);
    finish(h);
    assert(slang_ggml_prefix_restore_failures() == rfail + 1);
    assert(slang_ggml_prefix_hits() == hits_before);
    assert(slang_ggml_prefix_misses() == misses_before + 1);
    assert(slang_ggml_prefix_tokens_reused() == reused_before);
    assert(mock_llama_stale_leaks() == leaks);
    assert(slang_ggml_request_close(h) == 0);
    assert(slang_ggml_prefix_cache_configure(1, 1024) == 1);
    h = slang_ggml_request_create(64);
    begin(h, "QRSTUVWXYZ", 0);
    for (const char *g = "klmnop"; *g; g++)
        assert(slang_ggml_request_eval(h, 10 + (unsigned char)*g) == 0);
    finish(h);
    begin(h, "zzzz", 0);                                   /* evicts the long terminal, frees its stream */
    finish(h);
    leaks = mock_llama_stale_leaks();
    begin(h, "yyyyyyyy", 0);                               /* cold, takes the freed stream */
    finish(h);
    assert(mock_llama_stale_leaks() == leaks);
    assert(mock_llama_bad_positions() == 0);
    assert(slang_ggml_request_close(h) == 0);

    /* Mode 3 decode failure fails fast (no eviction cannot help a per-sequence
     * stream), releases the context and the sequence id. */
    assert(slang_ggml_prefix_cache_mode_configure(3, 0) == 3);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    h = slang_ggml_request_create(64);
    h2 = slang_ggml_request_create(64);
    begin(h, "streamone", 0);
    finish(h);
    begin(h, "otherxxxx", 0);                              /* a second, UNPINNED terminal */
    finish(h);
    evictions = slang_ggml_prefix_evictions();
    assert(prepare(h, "streamtwo") == 4);                  /* pins "streamone" only */
    mock_llama_fail_decode_once();
    /* A pre-fix shim evicts "otherxxxx", retries and succeeds; mode 3 must fail. */
    assert(slang_ggml_request_eval_prompt(h) < 0);
    assert(slang_ggml_prefix_evictions() == evictions);   /* nothing wiped */
    begin(h2, "otherxxxx", 8);                             /* released (no BUSY) and the unpinned terminal survived */
    finish(h2);
    begin(h2, "streamone", 8);
    finish(h2);
    assert(slang_ggml_request_close(h) == 0);
    assert(slang_ggml_request_close(h2) == 0);

    /* free resets the mode and the tree. */
    assert(slang_ggml_free() == 0);
    assert(slang_ggml_tree_mode() == 0);
    assert(slang_ggml_tree_nodes() == 0);

    /* ---- first micro-batch (CUDA workaround) on the persistent context ---- */
    reload(-1);                                    /* layers requested on the GPU */
    mock_llama_set_n_ubatch(4);
    assert(slang_ggml_prefix_cache_mode_configure(3, 0) == 3);
    assert(slang_ggml_prefix_cache_configure(4, 1024) == 4);
    h = slang_ggml_request_create(64);
    /* A first decode that fails must not mark the context warm: the next, short
     * prompt still gets the full-micro-batch warm-up. */
    assert(prepare(h, "abcdefghij") == 0);
    mock_llama_fail_decode_once();
    assert(slang_ggml_request_eval_prompt(h) < 0);
    int64_t short_before = mock_llama_short_first_decodes();
    begin(h, "ab", 0);                             /* shorter than one micro-batch */
    finish(h);
    assert(mock_llama_short_first_decodes() == short_before);
    assert(slang_ggml_request_close(h) == 0);
    assert(slang_ggml_free() == 0);
    assert(mock_llama_bad_positions() == 0);
    return 0;
}
