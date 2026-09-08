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
int64_t slang_ggml_capabilities(void);
int64_t slang_ggml_free(void);
static void text(const char *s) { slang_ggml_str_reset(); while (*s) slang_ggml_str_push((unsigned char)*s++); }
int main(void) {
    slang_ggml_backend_init(); text("model"); assert(slang_ggml_model_load(0) == 0);
    assert(slang_ggml_ctx_create(64) == 0); assert(slang_ggml_capabilities() == 7);
    text("abc"); assert(slang_ggml_tokenize(1) == 4); assert(slang_ggml_prefix_prepare() == 0); assert(slang_ggml_eval_prompt() == 4);
    text("abcdef"); assert(slang_ggml_tokenize(1) == 7); assert(slang_ggml_prefix_prepare() == 3); assert(slang_ggml_eval_prompt() == 7);
    assert(slang_ggml_prefix_hits() == 1); assert(slang_ggml_prefix_misses() == 1);
    assert(slang_ggml_prefix_tokens_reused() == 3); assert(slang_ggml_prefix_tokens_prefilled() == 8);
    text("xyz"); assert(slang_ggml_tokenize(1) == 4); assert(slang_ggml_prefix_prepare() == 0); assert(slang_ggml_eval_prompt() == 4);
    assert(slang_ggml_prefix_hits() == 1); assert(slang_ggml_prefix_misses() == 2);
    assert(slang_ggml_prefix_tokens_prefilled() == 12); assert(slang_ggml_free() == 0);
    return 0;
}
