#include "llama.h"
#include <stdlib.h>
#include <string.h>
struct llama_model { int live; };
struct llama_context { uint32_t n_ctx; int64_t n_tokens; int64_t decodes; };
struct llama_sampler { int live; };
struct llama_vocab { int live; };
static struct llama_vocab vocab = {1};
static int corrupt_restore_once;
static int short_decode_once;
static int64_t restore_calls;
static int64_t short_first_decodes;
static int64_t decode_calls;
static uint32_t n_ubatch = 1;
static int fail_restore_once = 0;
static int fail_remove_once = 0;
static int fail_serialize_once = 0;
static int fail_decode_once = 0;
void mock_llama_fail_restore_once(void) { fail_restore_once = 1; }
void mock_llama_fail_remove_once(void) { fail_remove_once = 1; }
void mock_llama_fail_serialize_once(void) { fail_serialize_once = 1; }
void mock_llama_fail_decode_once(void) { fail_decode_once = 1; }
void llama_backend_init(void) {}
struct llama_model_params llama_model_default_params(void) { return (struct llama_model_params){0}; }
struct llama_model * llama_model_load_from_file(const char *p, struct llama_model_params x) { (void)x; return p && *p ? calloc(1, sizeof(struct llama_model)) : NULL; }
struct llama_context_params llama_context_default_params(void) { return (struct llama_context_params){0}; }
struct llama_context * llama_init_from_model(struct llama_model *m, struct llama_context_params p) { if (!m) return NULL; struct llama_context *c = calloc(1, sizeof(*c)); c->n_ctx = p.n_ctx; return c; }
struct llama_sampler_chain_params llama_sampler_chain_default_params(void) { return (struct llama_sampler_chain_params){0}; }
struct llama_sampler * llama_sampler_chain_init(struct llama_sampler_chain_params p) { (void)p; return calloc(1, sizeof(struct llama_sampler)); }
struct llama_sampler * llama_sampler_init_greedy(void) { return calloc(1, sizeof(struct llama_sampler)); }
void llama_sampler_chain_add(struct llama_sampler *a, struct llama_sampler *b) { (void)a; free(b); }
void llama_sampler_free(struct llama_sampler *s) { free(s); }
void llama_free(struct llama_context *c) { free(c); }
void llama_model_free(struct llama_model *m) { free(m); }
uint32_t llama_n_ctx(const struct llama_context *c) { return c->n_ctx; }
const struct llama_vocab * llama_model_get_vocab(const struct llama_model *m) { (void)m; return &vocab; }
int32_t llama_vocab_n_tokens(const struct llama_vocab *v) { (void)v; return 8; }
float * llama_get_logits_ith(struct llama_context *ctx, int32_t i) {
    static float logits[8];
    (void)ctx; (void)i;
    return logits;
}
int32_t llama_tokenize(const struct llama_vocab *v, const char *s, int32_t n, llama_token *out, int32_t cap, bool bos, bool special) { (void)v; (void)special; int32_t total = n + (bos ? 1 : 0); if (total > cap) return -total; int32_t j = 0; if (bos) out[j++] = 1; for (int32_t i = 0; i < n; i++) out[j++] = 10 + (unsigned char)s[i]; return total; }
bool llama_vocab_is_eog(const struct llama_vocab *v, llama_token t) { (void)v; return t == 2; }
int32_t llama_token_to_piece(const struct llama_vocab *v, llama_token t, char *out, int32_t cap, int32_t l, bool s) { (void)v; (void)l; (void)s; if (cap < 1) return -1; out[0] = (char)t; return 1; }
llama_memory_t llama_get_memory(const struct llama_context *c) { return (void *)c; }
void llama_memory_clear(llama_memory_t m, bool data) { (void)data; ((struct llama_context *)m)->n_tokens = 0; }
bool llama_memory_seq_rm(llama_memory_t m, llama_seq_id id, llama_pos p0, llama_pos p1) { (void)id; (void)p1; if (fail_remove_once) { fail_remove_once = 0; return false; } if (((struct llama_context *)m)->n_tokens > p0) ((struct llama_context *)m)->n_tokens = p0; return true; }
size_t llama_state_seq_get_size(struct llama_context *c, llama_seq_id id) { (void)c; (void)id; return sizeof(int64_t); }
size_t llama_state_seq_get_data(struct llama_context *c, uint8_t *d, size_t n, llama_seq_id id) { (void)id; if (fail_serialize_once) { fail_serialize_once = 0; return 0; } if (n < sizeof(c->n_tokens)) return 0; memcpy(d, &c->n_tokens, sizeof(c->n_tokens)); return sizeof(c->n_tokens); }
size_t llama_state_seq_set_data(struct llama_context *c, const uint8_t *d, size_t n, llama_seq_id id) { (void)id; restore_calls++; if (corrupt_restore_once) { corrupt_restore_once = 0; if (n < sizeof(c->n_tokens)) return 0; memcpy(&c->n_tokens, d, sizeof(c->n_tokens)); c->n_tokens -= 2; return sizeof(c->n_tokens); } if (fail_restore_once) { fail_restore_once = 0; return 0; } if (n < sizeof(c->n_tokens)) return 0; memcpy(&c->n_tokens, d, sizeof(c->n_tokens)); return sizeof(c->n_tokens); }
struct llama_batch llama_batch_get_one(llama_token *t, int32_t n) { return (struct llama_batch){t, n}; }
int32_t llama_decode(struct llama_context *c, struct llama_batch b) { if (fail_decode_once) { fail_decode_once = 0; return 1; } decode_calls++; if (c->decodes++ == 0 && (uint32_t)b.n_tokens < n_ubatch) short_first_decodes++; if (short_decode_once) { short_decode_once = 0; c->n_tokens -= 1; } c->n_tokens += b.n_tokens; return c->n_tokens > c->n_ctx ? 1 : 0; }
llama_token llama_sampler_sample(struct llama_sampler *s, struct llama_context *c, int32_t i) { (void)s; (void)c; (void)i; return 2; }
/* Fault injection for the fail-closed restore checks. */
void mock_llama_corrupt_restore_once(void) { corrupt_restore_once = 1; }
void mock_llama_short_decode_once(void) { short_decode_once = 1; }
int64_t mock_llama_restore_calls(void) { return restore_calls; }
void mock_llama_set_n_ubatch(uint32_t n) { n_ubatch = n; }
int64_t mock_llama_short_first_decodes(void) { return short_first_decodes; }
int64_t mock_llama_decode_calls(void) { return decode_calls; }
uint32_t llama_n_ubatch(const struct llama_context *c) { (void)c; return n_ubatch; }
static int gpu_offload = 1;
void mock_llama_set_gpu_offload(int on) { gpu_offload = on; }
bool llama_supports_gpu_offload(void) { return gpu_offload != 0; }
const char * llama_model_chat_template(const struct llama_model *m, const char *name) { (void)m; (void)name; return NULL; }
int32_t llama_chat_apply_template(const char *t, const struct llama_chat_message *msgs, size_t n, bool add, char *buf, int32_t len) { (void)t; (void)msgs; (void)n; (void)add; (void)buf; (void)len; return -1; }
llama_pos llama_memory_seq_pos_min(llama_memory_t m, llama_seq_id id) { (void)id; return ((struct llama_context *)m)->n_tokens > 0 ? 0 : -1; }
llama_pos llama_memory_seq_pos_max(llama_memory_t m, llama_seq_id id) { (void)id; return (llama_pos)((struct llama_context *)m)->n_tokens - 1; }
