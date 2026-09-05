/* slang ggml backend shim — int64-only ABI for the Simple dynamic SFFI.
 *
 * WHY THIS FILE EXISTS
 * --------------------
 * slang is the vLLM/SGLang replacement for Simple. Like vLLM, it owns the
 * model lifecycle, the scheduler, the KV/context budget and the OpenAI API in
 * its own language, and drives someone else's kernels for the tensor math.
 * vLLM drives cuBLAS/FlashAttention; slang drives ggml. This file is that
 * boundary and nothing more: it holds no policy, runs no loop of its own, and
 * makes no decision slang could have made.
 *
 * The decode loop stays in Simple (src/lib/gc_async_mut/slang/worker/). Each
 * step is one `slang_ggml_eval` call, so KV positions, stop conditions, token
 * budgets and streaming are slang's, not ggml's.
 *
 * ponytail: ggml supplies dequant + attention + tokenizer kernels that pure
 * Simple does not have yet. Ceiling: single model, single context, greedy
 * sampling. Upgrade path: slang master plan A4 (paged KV) and A5 (scheduler +
 * continuous batching) replace this backend with pure-Simple kernels behind
 * the same `SlangBackend` seam in
 * src/lib/gc_async_mut/slang/model_executor/backend.spl.
 *
 * ABI RULE: every exported entry takes and returns int64 only. The Simple side
 * reaches C through `spl_wffi_call_i64`, which marshals nothing but integers,
 * so strings cross as byte pushes into the buffers below rather than as
 * pointers. That is deliberate — a pointer-passing ABI would put lifetime
 * decisions on the Simple side of a boundary that cannot express them.
 *
 * Built by scripts/build/build-slang-ggml-shim.shs, never by the main runtime
 * link: it needs llama.h, which is an external SDK header and is not vendored.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "llama.h"

#define SLANG_STR_CAP  (1 << 20)   /* 1 MiB of prompt is far past any real use */
#define SLANG_OUT_CAP  4096
#define SLANG_TOK_CAP  (1 << 18)

/* Error codes. Negative so a caller can test `< 0` without a sentinel table. */
#define SLANG_ERR_NO_MODEL     (-1)
#define SLANG_ERR_NO_CTX       (-2)
#define SLANG_ERR_LOAD_FAILED  (-3)
#define SLANG_ERR_OVERFLOW     (-4)
#define SLANG_ERR_TOKENIZE     (-5)
#define SLANG_ERR_DECODE       (-6)
#define SLANG_ERR_ALREADY      (-7)

static char    g_str[SLANG_STR_CAP];
static int64_t g_str_len = 0;

static char    g_out[SLANG_OUT_CAP];
static int64_t g_out_len = 0;

static llama_token g_tok[SLANG_TOK_CAP];
static int64_t     g_tok_len = 0;

static struct llama_model   *g_model = NULL;
static struct llama_context *g_ctx   = NULL;
static struct llama_sampler *g_smpl  = NULL;

/* ---- input string buffer -------------------------------------------- */

int64_t slang_ggml_str_reset(void) { g_str_len = 0; g_str[0] = '\0'; return 0; }

int64_t slang_ggml_str_push(int64_t byte) {
    if (g_str_len >= SLANG_STR_CAP - 1) return SLANG_ERR_OVERFLOW;
    g_str[g_str_len++] = (char)(byte & 0xFF);
    g_str[g_str_len] = '\0';
    return g_str_len;
}

/* ---- output byte buffer --------------------------------------------- */

int64_t slang_ggml_out_len(void) { return g_out_len; }

int64_t slang_ggml_out_byte(int64_t i) {
    if (i < 0 || i >= g_out_len) return SLANG_ERR_OVERFLOW;
    return (int64_t)(unsigned char)g_out[i];
}

/* ---- lifecycle ------------------------------------------------------- */

int64_t slang_ggml_backend_init(void) {
    llama_backend_init();
    return 0;
}

/* Loads the model whose path is in the string buffer. n_gpu_layers < 0 means
 * "offload everything"; 0 keeps the model on the CPU. */
int64_t slang_ggml_model_load(int64_t n_gpu_layers) {
    if (g_model != NULL) return SLANG_ERR_ALREADY;
    if (g_str_len == 0) return SLANG_ERR_LOAD_FAILED;
    struct llama_model_params mp = llama_model_default_params();
    mp.n_gpu_layers = (n_gpu_layers < 0) ? 999 : (int32_t)n_gpu_layers;
    g_model = llama_model_load_from_file(g_str, mp);
    return (g_model == NULL) ? SLANG_ERR_LOAD_FAILED : 0;
}

int64_t slang_ggml_ctx_create(int64_t n_ctx) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    if (g_ctx != NULL) return SLANG_ERR_ALREADY;
    struct llama_context_params cp = llama_context_default_params();
    cp.n_ctx   = (uint32_t)(n_ctx > 0 ? n_ctx : 4096);
    cp.n_batch = cp.n_ctx;
    g_ctx = llama_init_from_model(g_model, cp);
    if (g_ctx == NULL) return SLANG_ERR_NO_CTX;
    struct llama_sampler_chain_params sp = llama_sampler_chain_default_params();
    g_smpl = llama_sampler_chain_init(sp);
    llama_sampler_chain_add(g_smpl, llama_sampler_init_greedy());
    return 0;
}

/* Frees in reverse construction order and resets every handle, so a caller
 * that stops and restarts a model in one process leaks nothing. */
int64_t slang_ggml_free(void) {
    if (g_smpl)  { llama_sampler_free(g_smpl); g_smpl = NULL; }
    if (g_ctx)   { llama_free(g_ctx);          g_ctx = NULL; }
    if (g_model) { llama_model_free(g_model);  g_model = NULL; }
    g_tok_len = 0; g_out_len = 0; g_str_len = 0;
    return 0;
}

/* ---- vocab / tokenizer ---------------------------------------------- */

int64_t slang_ggml_n_ctx(void) {
    return (g_ctx == NULL) ? SLANG_ERR_NO_CTX : (int64_t)llama_n_ctx(g_ctx);
}

/* Tokenizes the string buffer. Returns the token count, which the caller reads
 * back one id at a time via slang_ggml_token_at. */
int64_t slang_ggml_tokenize(int64_t add_bos) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(g_model);
    int32_t n = llama_tokenize(vocab, g_str, (int32_t)g_str_len,
                               g_tok, SLANG_TOK_CAP, add_bos != 0, true);
    if (n < 0) return SLANG_ERR_TOKENIZE;
    g_tok_len = n;
    return g_tok_len;
}

int64_t slang_ggml_token_at(int64_t i) {
    if (i < 0 || i >= g_tok_len) return SLANG_ERR_OVERFLOW;
    return (int64_t)g_tok[i];
}

int64_t slang_ggml_is_eog(int64_t token) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(g_model);
    return llama_vocab_is_eog(vocab, (llama_token)token) ? 1 : 0;
}

/* Renders one token into the output buffer. Returns its byte length. */
int64_t slang_ggml_piece(int64_t token) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(g_model);
    int32_t n = llama_token_to_piece(vocab, (llama_token)token,
                                     g_out, SLANG_OUT_CAP, 0, true);
    if (n < 0) return SLANG_ERR_OVERFLOW;
    g_out_len = n;
    return g_out_len;
}

/* ---- decode ---------------------------------------------------------- */

/* Drops everything the context remembers, so the next prompt starts at
 * position zero. slang calls this before each prefill: without it a second
 * request in the same process appends to the first request's KV cache, the
 * positions run on until n_ctx and decode fails -- and, before that, the model
 * answers the new prompt while still attending to the old one. Residency means
 * reusing the WEIGHTS across requests, never the conversation state. */
int64_t slang_ggml_kv_clear(void) {
    if (g_ctx == NULL) return SLANG_ERR_NO_CTX;
    llama_memory_clear(llama_get_memory(g_ctx), true);
    return 0;
}

/* Prefill: submits the whole tokenized prompt as one batch. This is the only
 * place ggml sees more than a single token, and it is a batching detail, not a
 * scheduling decision — slang still chose what to prefill and when. */
int64_t slang_ggml_eval_prompt(void) {
    if (g_ctx == NULL) return SLANG_ERR_NO_CTX;
    if (g_tok_len == 0) return SLANG_ERR_TOKENIZE;
    struct llama_batch batch = llama_batch_get_one(g_tok, (int32_t)g_tok_len);
    if (llama_decode(g_ctx, batch) != 0) return SLANG_ERR_DECODE;
    return g_tok_len;
}

/* One decode step. slang's worker calls this in its own loop, which is what
 * keeps the generation loop on the Simple side of the boundary. */
int64_t slang_ggml_eval(int64_t token) {
    if (g_ctx == NULL) return SLANG_ERR_NO_CTX;
    llama_token t = (llama_token)token;
    struct llama_batch batch = llama_batch_get_one(&t, 1);
    if (llama_decode(g_ctx, batch) != 0) return SLANG_ERR_DECODE;
    return 0;
}

int64_t slang_ggml_sample(void) {
    if (g_ctx == NULL || g_smpl == NULL) return SLANG_ERR_NO_CTX;
    return (int64_t)llama_sampler_sample(g_smpl, g_ctx, -1);
}
