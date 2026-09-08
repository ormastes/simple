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
#define SLANG_PREFIX_CACHE_MAX_ENTRIES 8
#define SLANG_PREFIX_CACHE_DEFAULT_ENTRIES 4
#define SLANG_PREFIX_CACHE_DEFAULT_BYTES ((size_t)2 * 1024 * 1024 * 1024)
#define SLANG_REQUEST_MAX_ENTRIES 8
#define SLANG_REQUEST_DEFAULT_ENTRIES 4
#define SLANG_REQUEST_MAX_GENERATION ((uint64_t)(INT64_MAX - SLANG_REQUEST_MAX_ENTRIES) / SLANG_REQUEST_MAX_ENTRIES)

/* Error codes. Negative so a caller can test `< 0` without a sentinel table. */
#define SLANG_ERR_NO_MODEL     (-1)
#define SLANG_ERR_NO_CTX       (-2)
#define SLANG_ERR_LOAD_FAILED  (-3)
#define SLANG_ERR_OVERFLOW     (-4)
#define SLANG_ERR_TOKENIZE     (-5)
#define SLANG_ERR_DECODE       (-6)
#define SLANG_ERR_ALREADY      (-7)
#define SLANG_ERR_INVALID      (-8)
#define SLANG_ERR_BUSY         (-9)
#define SLANG_ERR_CANCELLED   (-10)
#define SLANG_ERR_EXHAUSTED   (-11)

struct slang_prefix_entry {
    llama_token *tokens;
    int64_t token_count;
    uint8_t *state;
    size_t state_size;
    size_t retained_bytes;
    uint64_t last_used;
    int64_t pins;
    int unavailable;
};

struct slang_request {
    struct llama_context *ctx;
    struct llama_sampler *smpl;
    char *str;
    char *out;
    llama_token *tok;
    int64_t str_len;
    int64_t out_len;
    int64_t tok_len;
    int64_t eval_start;
    int64_t selected_prefix;
    int64_t lease_slot;
    uint64_t generation;
    uint64_t model_generation;
    int active;
    int cancelled;
};

static struct slang_prefix_entry g_prefix[SLANG_PREFIX_CACHE_MAX_ENTRIES];
static int64_t     g_prefix_capacity = SLANG_PREFIX_CACHE_DEFAULT_ENTRIES;
static size_t      g_prefix_byte_limit = SLANG_PREFIX_CACHE_DEFAULT_BYTES;
static size_t      g_prefix_resident_bytes = 0;
static int64_t     g_prefix_resident_entries = 0;
static uint64_t    g_prefix_clock = 0;
static int64_t     g_prefix_hits = 0;
static int64_t     g_prefix_misses = 0;
static int64_t     g_prefix_tokens_reused = 0;
static int64_t     g_prefix_tokens_prefilled = 0;
static int64_t     g_prefix_admissions = 0;
static int64_t     g_prefix_evictions = 0;
static int64_t     g_prefix_rejected_bytes = 0;
static int64_t     g_prefix_restore_failures = 0;

static struct llama_model   *g_model = NULL;
static struct slang_request g_requests[SLANG_REQUEST_MAX_ENTRIES];
static int64_t g_request_capacity = SLANG_REQUEST_DEFAULT_ENTRIES;
static int64_t g_request_count = 0;
static int64_t g_compat_handle = 0;
static uint64_t g_model_generation = 0;
static char g_load_str[SLANG_STR_CAP];
static int64_t g_load_str_len = 0;

static int64_t slang_request_handle(int64_t slot, uint64_t generation) {
    if (generation == 0 || generation > SLANG_REQUEST_MAX_GENERATION)
        return SLANG_ERR_EXHAUSTED;
    return (int64_t)(generation * SLANG_REQUEST_MAX_ENTRIES + (uint64_t)slot + 1);
}

static struct slang_request *slang_request_get(int64_t handle) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)(handle - 1);
    int64_t slot = (int64_t)(raw % SLANG_REQUEST_MAX_ENTRIES);
    uint64_t generation = raw / SLANG_REQUEST_MAX_ENTRIES;
    struct slang_request *request = &g_requests[slot];
    if (!request->active || generation == 0 || request->generation != generation ||
        request->model_generation != g_model_generation)
        return NULL;
    return request;
}

static struct slang_request *slang_compat_request(void) {
    return slang_request_get(g_compat_handle);
}

/* ---- input string buffer -------------------------------------------- */

int64_t slang_ggml_request_str_reset(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    request->str_len = 0;
    request->str[0] = '\0';
    return 0;
}

int64_t slang_ggml_str_reset(void) {
    struct slang_request *request = slang_compat_request();
    if (request != NULL) return slang_ggml_request_str_reset(g_compat_handle);
    g_load_str_len = 0;
    g_load_str[0] = '\0';
    return 0;
}

int64_t slang_ggml_request_str_push(int64_t handle, int64_t byte) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->str_len >= SLANG_STR_CAP - 1) return SLANG_ERR_OVERFLOW;
    request->str[request->str_len++] = (char)(byte & 0xFF);
    request->str[request->str_len] = '\0';
    return request->str_len;
}

int64_t slang_ggml_str_push(int64_t byte) {
    struct slang_request *request = slang_compat_request();
    if (request != NULL) return slang_ggml_request_str_push(g_compat_handle, byte);
    if (g_load_str_len >= SLANG_STR_CAP - 1) return SLANG_ERR_OVERFLOW;
    g_load_str[g_load_str_len++] = (char)(byte & 0xFF);
    g_load_str[g_load_str_len] = '\0';
    return g_load_str_len;
}

/* ---- output byte buffer --------------------------------------------- */

int64_t slang_ggml_request_out_len(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    return request == NULL ? SLANG_ERR_INVALID : request->out_len;
}

int64_t slang_ggml_out_len(void) {
    return slang_ggml_request_out_len(g_compat_handle);
}

int64_t slang_ggml_request_out_byte(int64_t handle, int64_t i) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (i < 0 || i >= request->out_len) return SLANG_ERR_OVERFLOW;
    return (int64_t)(unsigned char)request->out[i];
}

int64_t slang_ggml_out_byte(int64_t i) {
    return slang_ggml_request_out_byte(g_compat_handle, i);
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
    if (g_load_str_len == 0) return SLANG_ERR_LOAD_FAILED;
    struct llama_model_params mp = llama_model_default_params();
    mp.n_gpu_layers = (n_gpu_layers < 0) ? 999 : (int32_t)n_gpu_layers;
    g_model = llama_model_load_from_file(g_load_str, mp);
    if (g_model == NULL) return SLANG_ERR_LOAD_FAILED;
    if (g_model_generation == UINT64_MAX) {
        llama_model_free(g_model);
        g_model = NULL;
        return SLANG_ERR_EXHAUSTED;
    }
    g_model_generation++;
    return 0;
}

int64_t slang_ggml_request_configure(int64_t entries) {
    if (entries < 1 || entries > SLANG_REQUEST_MAX_ENTRIES)
        return SLANG_ERR_OVERFLOW;
    if (g_request_count > entries) return SLANG_ERR_BUSY;
    g_request_capacity = entries;
    return entries;
}

int64_t slang_ggml_request_create(int64_t n_ctx) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    if (g_request_count >= g_request_capacity) return SLANG_ERR_BUSY;
    int64_t slot = -1;
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; i++) {
        if (!g_requests[i].active) { slot = i; break; }
    }
    if (slot < 0) return SLANG_ERR_BUSY;
    struct slang_request *old = &g_requests[slot];
    if (old->generation >= SLANG_REQUEST_MAX_GENERATION)
        return SLANG_ERR_EXHAUSTED;

    struct llama_context_params cp = llama_context_default_params();
    cp.n_ctx   = (uint32_t)(n_ctx > 0 ? n_ctx : 4096);
    cp.n_batch = cp.n_ctx;
    struct llama_context *ctx = llama_init_from_model(g_model, cp);
    if (ctx == NULL) return SLANG_ERR_NO_CTX;
    struct llama_sampler_chain_params sp = llama_sampler_chain_default_params();
    struct llama_sampler *smpl = llama_sampler_chain_init(sp);
    struct llama_sampler *greedy = llama_sampler_init_greedy();
    char *str = (char *)malloc(SLANG_STR_CAP);
    char *out = (char *)malloc(SLANG_OUT_CAP);
    llama_token *tok = (llama_token *)malloc((size_t)SLANG_TOK_CAP * sizeof(llama_token));
    if (smpl == NULL || greedy == NULL || str == NULL || out == NULL || tok == NULL) {
        if (greedy) llama_sampler_free(greedy);
        if (smpl) llama_sampler_free(smpl);
        llama_free(ctx);
        free(str); free(out); free(tok);
        return SLANG_ERR_NO_CTX;
    }
    llama_sampler_chain_add(smpl, greedy);
    uint64_t generation = old->generation == 0 ? 1 : old->generation;
    memset(old, 0, sizeof(*old));
    old->ctx = ctx; old->smpl = smpl;
    old->str = str; old->out = out; old->tok = tok;
    old->eval_start = 0; old->selected_prefix = -1; old->lease_slot = -1;
    old->generation = generation; old->model_generation = g_model_generation;
    old->active = 1;
    g_request_count++;
    return slang_request_handle(slot, generation);
}

int64_t slang_ggml_ctx_create(int64_t n_ctx) {
    if (slang_compat_request() != NULL) return SLANG_ERR_ALREADY;
    int64_t handle = slang_ggml_request_create(n_ctx);
    if (handle < 0) return handle;
    g_compat_handle = handle;
    return 0;
}

/* Capability bits are stable at the ABI boundary. Bit 0 is resident weights,
 * bit 1 is request isolation, bit 2 is serial exact-prefix restore, and bit 3
 * is bounded serial multi-entry prefix retention, and bit 4 is generation-
 * checked independent request ownership under one serial executor. */
int64_t slang_ggml_capabilities(void) { return 1 | 2 | 4 | 8 | 16; }

static int slang_prefix_drop(int64_t slot, int count_eviction) {
    struct slang_prefix_entry *entry = &g_prefix[slot];
    if (entry->tokens == NULL && entry->state == NULL) return 1;
    if (entry->pins > 0) return 0;
    if (g_prefix_resident_bytes >= entry->retained_bytes)
        g_prefix_resident_bytes -= entry->retained_bytes;
    else
        g_prefix_resident_bytes = 0;
    free(entry->tokens);
    free(entry->state);
    memset(entry, 0, sizeof(*entry));
    if (g_prefix_resident_entries > 0) g_prefix_resident_entries--;
    if (count_eviction) g_prefix_evictions++;
    return 1;
}

static int64_t slang_prefix_lru_slot(void) {
    int64_t selected = -1;
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++) {
        if (g_prefix[i].state == NULL || g_prefix[i].pins > 0) continue;
        if (selected < 0 || g_prefix[i].last_used < g_prefix[selected].last_used)
            selected = i;
    }
    return selected;
}

static void slang_prefix_clear_all(int count_eviction) {
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++)
        slang_prefix_drop(i, count_eviction);
}

int64_t slang_ggml_prefix_cache_configure(int64_t entries, int64_t bytes) {
    if (entries < 0 || entries > SLANG_PREFIX_CACHE_MAX_ENTRIES || bytes < 0)
        return SLANG_ERR_OVERFLOW;
    if ((uint64_t)bytes > (uint64_t)SIZE_MAX) return SLANG_ERR_OVERFLOW;
    int64_t pinned_entries = 0;
    size_t pinned_bytes = 0;
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++) {
        if (g_prefix[i].state != NULL && g_prefix[i].pins > 0) {
            pinned_entries++;
            if (g_prefix[i].retained_bytes > SIZE_MAX - pinned_bytes)
                return SLANG_ERR_OVERFLOW;
            pinned_bytes += g_prefix[i].retained_bytes;
        }
    }
    if (pinned_entries > entries || pinned_bytes > (size_t)bytes)
        return SLANG_ERR_BUSY;
    g_prefix_capacity = entries;
    g_prefix_byte_limit = (size_t)bytes;
    while (g_prefix_resident_entries > g_prefix_capacity ||
           g_prefix_resident_bytes > g_prefix_byte_limit) {
        int64_t slot = slang_prefix_lru_slot();
        if (slot < 0) return SLANG_ERR_BUSY;
        slang_prefix_drop(slot, 1);
    }
    return g_prefix_capacity;
}

static void slang_request_release_lease(struct slang_request *request) {
    if (request->lease_slot < 0) return;
    struct slang_prefix_entry *entry = &g_prefix[request->lease_slot];
    if (entry->pins > 0) entry->pins--;
    int64_t slot = request->lease_slot;
    request->lease_slot = -1;
    request->selected_prefix = -1;
    if (entry->unavailable && entry->pins == 0) slang_prefix_drop(slot, 0);
}

int64_t slang_ggml_request_close(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    slang_request_release_lease(request);
    if (request->smpl) llama_sampler_free(request->smpl);
    if (request->ctx) llama_free(request->ctx);
    free(request->str); free(request->out); free(request->tok);
    uint64_t next_generation = request->generation < SLANG_REQUEST_MAX_GENERATION
        ? request->generation + 1 : SLANG_REQUEST_MAX_GENERATION;
    memset(request, 0, sizeof(*request));
    request->generation = next_generation;
    request->selected_prefix = -1;
    request->lease_slot = -1;
    if (g_request_count > 0) g_request_count--;
    if (g_compat_handle == handle) g_compat_handle = 0;
    return 0;
}

int64_t slang_ggml_request_cancel(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    request->cancelled = 1;
    return slang_ggml_request_close(handle);
}

/* Frees in reverse construction order and resets every handle, so a caller
 * that stops and restarts a model in one process leaks nothing. */
int64_t slang_ggml_free(void) {
    int compat_active = slang_compat_request() != NULL;
    if (g_request_count > (compat_active ? 1 : 0)) return SLANG_ERR_BUSY;
    if (compat_active) slang_ggml_request_close(g_compat_handle);
    if (g_model) { llama_model_free(g_model);  g_model = NULL; }
    slang_prefix_clear_all(0);
    g_prefix_capacity = SLANG_PREFIX_CACHE_DEFAULT_ENTRIES;
    g_prefix_byte_limit = SLANG_PREFIX_CACHE_DEFAULT_BYTES;
    g_prefix_clock = 0;
    g_prefix_hits = 0; g_prefix_misses = 0;
    g_prefix_tokens_reused = 0; g_prefix_tokens_prefilled = 0;
    g_prefix_admissions = 0; g_prefix_evictions = 0;
    g_prefix_rejected_bytes = 0; g_prefix_restore_failures = 0;
    g_request_capacity = SLANG_REQUEST_DEFAULT_ENTRIES;
    g_compat_handle = 0; g_load_str_len = 0; g_load_str[0] = '\0';
    return 0;
}

/* ---- vocab / tokenizer ---------------------------------------------- */

int64_t slang_ggml_request_n_ctx(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    return request == NULL ? SLANG_ERR_INVALID : (int64_t)llama_n_ctx(request->ctx);
}

int64_t slang_ggml_n_ctx(void) {
    return slang_ggml_request_n_ctx(g_compat_handle);
}

/* Tokenizes the string buffer. Returns the token count, which the caller reads
 * back one id at a time via slang_ggml_token_at. */
int64_t slang_ggml_request_tokenize(int64_t handle, int64_t add_bos) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(g_model);
    int32_t n = llama_tokenize(vocab, request->str, (int32_t)request->str_len,
                               request->tok, SLANG_TOK_CAP, add_bos != 0, true);
    if (n < 0) return SLANG_ERR_TOKENIZE;
    request->tok_len = n;
    return request->tok_len;
}

int64_t slang_ggml_tokenize(int64_t add_bos) {
    return slang_ggml_request_tokenize(g_compat_handle, add_bos);
}

int64_t slang_ggml_request_token_at(int64_t handle, int64_t i) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (i < 0 || i >= request->tok_len) return SLANG_ERR_OVERFLOW;
    return (int64_t)request->tok[i];
}

int64_t slang_ggml_token_at(int64_t i) {
    return slang_ggml_request_token_at(g_compat_handle, i);
}

int64_t slang_ggml_is_eog(int64_t token) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(g_model);
    return llama_vocab_is_eog(vocab, (llama_token)token) ? 1 : 0;
}

/* Renders one token into the output buffer. Returns its byte length. */
int64_t slang_ggml_request_piece(int64_t handle, int64_t token) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(g_model);
    int32_t n = llama_token_to_piece(vocab, (llama_token)token,
                                     request->out, SLANG_OUT_CAP, 0, true);
    if (n < 0) {
        slang_request_release_lease(request);
        return SLANG_ERR_OVERFLOW;
    }
    request->out_len = n;
    return request->out_len;
}

int64_t slang_ggml_piece(int64_t token) {
    return slang_ggml_request_piece(g_compat_handle, token);
}

/* ---- decode ---------------------------------------------------------- */

/* Drops everything the context remembers, so the next prompt starts at
 * position zero. slang calls this before each prefill: without it a second
 * request in the same process appends to the first request's KV cache, the
 * positions run on until n_ctx and decode fails -- and, before that, the model
 * answers the new prompt while still attending to the old one. Residency means
 * reusing the WEIGHTS across requests, never the conversation state. */
int64_t slang_ggml_request_kv_clear(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    slang_request_release_lease(request);
    llama_memory_clear(llama_get_memory(request->ctx), true);
    request->eval_start = 0;
    return 0;
}

int64_t slang_ggml_kv_clear(void) {
    return slang_ggml_request_kv_clear(g_compat_handle);
}

/* Selects the longest cacheable prefix owned by this serial context. The
 * snapshot is restored only after exact token comparison. One trailing token
 * is recomputed so the backend produces fresh boundary logits. */
int64_t slang_ggml_request_prefix_prepare(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    slang_request_release_lease(request);
    request->eval_start = 0;
    request->selected_prefix = -1;
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++) {
        struct slang_prefix_entry *entry = &g_prefix[i];
        if (entry->state == NULL || entry->unavailable || entry->token_count <= 1 ||
            request->tok_len < entry->token_count) continue;
        if (memcmp(request->tok, entry->tokens,
                   (size_t)entry->token_count * sizeof(llama_token)) != 0)
            continue;
        if (request->selected_prefix < 0 ||
            entry->token_count > g_prefix[request->selected_prefix].token_count)
            request->selected_prefix = i;
    }
    if (request->selected_prefix >= 0) {
        struct slang_prefix_entry *entry = &g_prefix[request->selected_prefix];
        entry->pins++;
        request->lease_slot = request->selected_prefix;
        llama_memory_clear(llama_get_memory(request->ctx), true);
        if (llama_state_seq_set_data(request->ctx, entry->state,
                                     entry->state_size, 0) ==
            entry->state_size) {
            request->eval_start = entry->token_count - 1;
            if (llama_memory_seq_rm(llama_get_memory(request->ctx), 0,
                                    (llama_pos)request->eval_start, -1)) {
                entry->last_used = ++g_prefix_clock;
                g_prefix_hits++;
                g_prefix_tokens_reused += request->eval_start;
                return request->eval_start;
            }
        }
        g_prefix_restore_failures++;
        entry->unavailable = 1;
        slang_request_release_lease(request);
    }
    llama_memory_clear(llama_get_memory(request->ctx), true);
    g_prefix_misses++;
    return 0;
}

int64_t slang_ggml_prefix_prepare(void) {
    return slang_ggml_request_prefix_prepare(g_compat_handle);
}

int64_t slang_ggml_prefix_hits(void) { return g_prefix_hits; }
int64_t slang_ggml_prefix_misses(void) { return g_prefix_misses; }
int64_t slang_ggml_prefix_tokens_reused(void) { return g_prefix_tokens_reused; }
int64_t slang_ggml_prefix_tokens_prefilled(void) { return g_prefix_tokens_prefilled; }
int64_t slang_ggml_prefix_admissions(void) { return g_prefix_admissions; }
int64_t slang_ggml_prefix_evictions(void) { return g_prefix_evictions; }
int64_t slang_ggml_prefix_resident_entries(void) { return g_prefix_resident_entries; }
int64_t slang_ggml_prefix_resident_bytes(void) { return (int64_t)g_prefix_resident_bytes; }
int64_t slang_ggml_prefix_rejected_bytes(void) { return g_prefix_rejected_bytes; }
int64_t slang_ggml_prefix_restore_failures(void) { return g_prefix_restore_failures; }

static int64_t slang_prefix_exact_slot(struct slang_request *request) {
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++) {
        struct slang_prefix_entry *entry = &g_prefix[i];
        if (entry->state != NULL && !entry->unavailable &&
            entry->token_count == request->tok_len &&
            memcmp(entry->tokens, request->tok,
                   (size_t)request->tok_len * sizeof(llama_token)) == 0)
            return i;
    }
    return -1;
}

static void slang_prefix_admit(struct slang_request *request) {
    if (g_prefix_capacity == 0 || g_prefix_byte_limit == 0) return;
    int64_t exact = slang_prefix_exact_slot(request);
    if (exact >= 0) {
        g_prefix[exact].last_used = ++g_prefix_clock;
        return;
    }
    size_t state_size = llama_state_seq_get_size(request->ctx, 0);
    if (state_size == 0 || request->tok_len <= 0) return;
    size_t token_bytes = (size_t)request->tok_len * sizeof(llama_token);
    if (state_size > SIZE_MAX - token_bytes) {
        g_prefix_rejected_bytes = INT64_MAX;
        return;
    }
    size_t candidate_bytes = state_size + token_bytes;
    if (candidate_bytes > g_prefix_byte_limit) {
        if (candidate_bytes > (size_t)(INT64_MAX - g_prefix_rejected_bytes))
            g_prefix_rejected_bytes = INT64_MAX;
        else
            g_prefix_rejected_bytes += (int64_t)candidate_bytes;
        return;
    }
    while (g_prefix_resident_entries >= g_prefix_capacity ||
           g_prefix_resident_bytes > g_prefix_byte_limit - candidate_bytes) {
        int64_t victim = slang_prefix_lru_slot();
        if (victim < 0) return;
        slang_prefix_drop(victim, 1);
    }
    int64_t slot = -1;
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++) {
        if (g_prefix[i].state == NULL) { slot = i; break; }
    }
    if (slot < 0) return;
    uint8_t *state = (uint8_t *)malloc(state_size);
    llama_token *tokens = (llama_token *)malloc(token_bytes);
    if (state == NULL || tokens == NULL ||
        llama_state_seq_get_data(request->ctx, state, state_size, 0) != state_size) {
        free(state);
        free(tokens);
        return;
    }
    memcpy(tokens, request->tok, token_bytes);
    g_prefix[slot].tokens = tokens;
    g_prefix[slot].token_count = request->tok_len;
    g_prefix[slot].state = state;
    g_prefix[slot].state_size = state_size;
    g_prefix[slot].retained_bytes = candidate_bytes;
    g_prefix[slot].last_used = ++g_prefix_clock;
    g_prefix_resident_bytes += candidate_bytes;
    g_prefix_resident_entries++;
    g_prefix_admissions++;
}

/* Prefill: submits the whole tokenized prompt as one batch. This is the only
 * place ggml sees more than a single token, and it is a batching detail, not a
 * scheduling decision — slang still chose what to prefill and when. */
int64_t slang_ggml_request_eval_prompt(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    if (request->tok_len == 0) return SLANG_ERR_TOKENIZE;
    if (request->eval_start < 0 || request->eval_start > request->tok_len)
        return SLANG_ERR_DECODE;
    int64_t suffix_len = request->tok_len - request->eval_start;
    if (suffix_len > 0) {
        struct llama_batch batch = llama_batch_get_one(
            request->tok + request->eval_start, (int32_t)suffix_len);
        if (llama_decode(request->ctx, batch) != 0) {
            slang_request_release_lease(request);
            return SLANG_ERR_DECODE;
        }
        g_prefix_tokens_prefilled += suffix_len;
    }
    slang_prefix_admit(request);
    request->eval_start = request->tok_len;
    return request->tok_len;
}

int64_t slang_ggml_eval_prompt(void) {
    int64_t result = slang_ggml_request_eval_prompt(g_compat_handle);
    struct slang_request *request = slang_compat_request();
    if (result >= 0 && request != NULL) slang_request_release_lease(request);
    return result;
}

/* One decode step. slang's worker calls this in its own loop, which is what
 * keeps the generation loop on the Simple side of the boundary. */
int64_t slang_ggml_request_eval(int64_t handle, int64_t token) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    llama_token t = (llama_token)token;
    struct llama_batch batch = llama_batch_get_one(&t, 1);
    if (llama_decode(request->ctx, batch) != 0) {
        slang_request_release_lease(request);
        return SLANG_ERR_DECODE;
    }
    return 0;
}

int64_t slang_ggml_eval(int64_t token) {
    return slang_ggml_request_eval(g_compat_handle, token);
}

int64_t slang_ggml_request_sample(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    int64_t token = (int64_t)llama_sampler_sample(request->smpl, request->ctx, -1);
    if (slang_ggml_is_eog(token) == 1) slang_request_release_lease(request);
    return token;
}

int64_t slang_ggml_sample(void) {
    return slang_ggml_request_sample(g_compat_handle);
}
