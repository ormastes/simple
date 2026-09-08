#include <assert.h>
#include <stdint.h>
int64_t slang_ggml_str_reset(void);
int64_t slang_ggml_str_push(int64_t);
int64_t slang_ggml_backend_init(void);
int64_t slang_ggml_model_load(int64_t);
int64_t slang_ggml_ctx_create(int64_t);
int64_t slang_ggml_tokenize(int64_t);
int64_t slang_ggml_prefix_prepare(void);
int64_t slang_ggml_eval_prompt(void);
int64_t slang_ggml_prefix_hits(void);
int64_t slang_ggml_prefix_misses(void);
int64_t slang_ggml_prefix_tokens_reused(void);
int64_t slang_ggml_prefix_tokens_prefilled(void);
int64_t slang_ggml_prefix_cache_configure(int64_t, int64_t);
int64_t slang_ggml_prefix_admissions(void);
int64_t slang_ggml_prefix_evictions(void);
int64_t slang_ggml_prefix_resident_entries(void);
int64_t slang_ggml_prefix_resident_bytes(void);
int64_t slang_ggml_prefix_rejected_bytes(void);
int64_t slang_ggml_prefix_restore_failures(void);
int64_t slang_ggml_capabilities(void);
int64_t slang_ggml_free(void);
void mock_llama_fail_restore_once(void);
void mock_llama_fail_remove_once(void);
void mock_llama_fail_serialize_once(void);
void mock_llama_fail_decode_once(void);
static void text(const char *s) { slang_ggml_str_reset(); while (*s) slang_ggml_str_push((unsigned char)*s++); }
static void prefill(const char *s, int64_t expected_start) {
    text(s);
    assert(slang_ggml_tokenize(1) > 0);
    assert(slang_ggml_prefix_prepare() == expected_start);
    assert(slang_ggml_eval_prompt() > 0);
}
int main(void) {
    slang_ggml_backend_init(); text("model"); assert(slang_ggml_model_load(0) == 0);
    assert(slang_ggml_ctx_create(64) == 0); assert(slang_ggml_capabilities() == 15);
    assert(slang_ggml_prefix_cache_configure(2, 1024) == 2);
    assert(slang_ggml_prefix_cache_configure(9, 1024) < 0);
    prefill("abc", 0);
    prefill("xyz", 0);
    assert(slang_ggml_prefix_resident_entries() == 2);
    assert(slang_ggml_prefix_resident_bytes() == 48);
    prefill("abcQ", 3);
    assert(slang_ggml_prefix_evictions() == 1);
    prefill("xyz", 0);
    prefill("abcQZ", 4);
    prefill("abcQZ", 5);
    assert(slang_ggml_prefix_hits() == 3);
    assert(slang_ggml_prefix_misses() == 3);
    assert(slang_ggml_prefix_tokens_reused() == 12);
    assert(slang_ggml_prefix_tokens_prefilled() == 17);
    assert(slang_ggml_prefix_admissions() == 5);
    assert(slang_ggml_prefix_evictions() == 3);
    assert(slang_ggml_prefix_resident_entries() == 2);
    assert(slang_ggml_prefix_restore_failures() == 0);
    assert(slang_ggml_prefix_cache_configure(2, 4) == 2);
    assert(slang_ggml_prefix_resident_entries() == 0);
    assert(slang_ggml_prefix_evictions() == 5);
    prefill("z", 0);
    assert(slang_ggml_prefix_rejected_bytes() == 16);
    assert(slang_ggml_prefix_resident_entries() == 0);

    assert(slang_ggml_prefix_cache_configure(2, 1024) == 2);
    int64_t admissions = slang_ggml_prefix_admissions();
    mock_llama_fail_serialize_once();
    prefill("ser", 0);
    assert(slang_ggml_prefix_admissions() == admissions);
    assert(slang_ggml_prefix_resident_entries() == 0);

    prefill("abc", 0);
    mock_llama_fail_restore_once();
    prefill("abcX", 0);
    assert(slang_ggml_prefix_restore_failures() == 1);
    assert(slang_ggml_prefix_resident_entries() == 1);

    mock_llama_fail_remove_once();
    prefill("abcXY", 0);
    assert(slang_ggml_prefix_restore_failures() == 2);
    assert(slang_ggml_prefix_resident_entries() == 1);

    text("abcXYZ");
    assert(slang_ggml_tokenize(1) == 7);
    assert(slang_ggml_prefix_prepare() == 5);
    mock_llama_fail_decode_once();
    assert(slang_ggml_eval_prompt() < 0);
    prefill("isolated", 0);

    admissions = slang_ggml_prefix_admissions();
    assert(slang_ggml_prefix_cache_configure(0, 1024) == 0);
    prefill("disabled", 0);
    assert(slang_ggml_prefix_admissions() == admissions);
    assert(slang_ggml_prefix_resident_entries() == 0);
    assert(slang_ggml_free() == 0);
    assert(slang_ggml_prefix_hits() == 0);
    assert(slang_ggml_prefix_resident_bytes() == 0);
    return 0;
}
