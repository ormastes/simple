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

#if defined(__has_include)
#  if __has_include("llama-slang-paged.h")
#    include "llama-slang-paged.h"
#    define SLANG_HAS_EXTERNAL_PAGED_PROVIDER 1
#  endif
#endif
#ifndef SLANG_HAS_EXTERNAL_PAGED_PROVIDER
#  define SLANG_HAS_EXTERNAL_PAGED_PROVIDER 0
#endif

#define SLANG_STR_CAP  (1 << 20)   /* 1 MiB of prompt is far past any real use */
#define SLANG_OUT_CAP  4096
#define SLANG_TOK_CAP  (1 << 18)
#define SLANG_PREFIX_CACHE_MAX_ENTRIES 8
#define SLANG_PREFIX_CACHE_DEFAULT_ENTRIES 4
#define SLANG_PREFIX_CACHE_DEFAULT_BYTES ((size_t)2 * 1024 * 1024 * 1024)
#define SLANG_REQUEST_MAX_ENTRIES 8
#define SLANG_REQUEST_DEFAULT_ENTRIES 4
#define SLANG_REQUEST_MAX_GENERATION ((uint64_t)(INT64_MAX - SLANG_REQUEST_MAX_ENTRIES) / SLANG_REQUEST_MAX_ENTRIES)
#define SLANG_PHYSICAL_PAGE_ABI_V1 1
#define SLANG_CAP_PHYSICAL_PAGED_KV 32
#define SLANG_CAP_PHYSICAL_LIGHTWEIGHT_REQUESTS 64

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
    int legacy_logits_valid;
    int physical_only;
    int64_t context_limit;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    float *paged_logits;
    int paged_logits_valid;
#endif
};

#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
enum slang_page_state {
    SLANG_PAGE_FREE = 0,
    SLANG_PAGE_WRITABLE = 1,
    SLANG_PAGE_SEALED = 2,
};

struct slang_physical_page {
    int64_t handle;
    int64_t occupied;
    enum slang_page_state state;
};

struct slang_physical_transaction {
    int64_t handle;
    int64_t request_handle;
    int64_t *page_slots;
    int64_t *initial_rows;
    int64_t *initial_states;
    int64_t *additional_rows;
    int64_t count;
    int64_t capacity;
    int active;
};

struct slang_physical_pool {
    struct llama_context *ctx;
    struct slang_physical_page *pages;
    struct slang_physical_transaction transactions[SLANG_REQUEST_MAX_ENTRIES];
    int64_t request_handles[SLANG_REQUEST_MAX_ENTRIES];
    int64_t handle;
    int64_t execution_namespace;
    int64_t page_tokens;
    int64_t page_capacity;
    int64_t page_bytes;
    int64_t allocated_pages;
    uint64_t generation;
    int active;
};

static struct slang_physical_pool g_physical_pool;
static uint64_t g_physical_pool_generation = 1;
#endif

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

#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
static int slang_checked_mul_size(size_t a, size_t b, size_t *result) {
    if (a != 0 && b > SIZE_MAX / a) return 0;
    *result = a * b;
    return 1;
}

static int slang_checked_add_size(size_t a, size_t b, size_t *result) {
    if (b > SIZE_MAX - a) return 0;
    *result = a + b;
    return 1;
}

static int64_t slang_physical_namespace(void) {
    if (g_model == NULL || g_model_generation == 0) return SLANG_ERR_NO_MODEL;
    uint64_t value = UINT64_C(1469598103934665603);
#define SLANG_MIX(part) do { value ^= (uint64_t)(part); value *= UINT64_C(1099511628211); } while (0)
    SLANG_MIX(g_model_generation);
    SLANG_MIX(llama_model_size(g_model));
    SLANG_MIX(llama_model_n_layer(g_model));
    SLANG_MIX(llama_model_n_head(g_model));
    SLANG_MIX(llama_model_n_head_kv(g_model));
    SLANG_MIX(llama_model_n_embd(g_model));
#undef SLANG_MIX
    value &= (uint64_t)INT64_MAX;
    return value == 0 ? 1 : (int64_t)value;
}

static struct slang_physical_pool *slang_physical_pool_get(int64_t handle) {
    return g_physical_pool.active && handle > 0 && handle == g_physical_pool.handle ? &g_physical_pool : NULL;
}

static int64_t slang_request_slot(const struct slang_request *request) {
    return request == NULL ? -1 : (int64_t)(request - g_requests);
}

static int64_t slang_physical_page_slot(struct slang_physical_pool *pool, int64_t handle) {
    if (pool == NULL || handle <= 0) return -1;
    for (int64_t i = 0; i < pool->page_capacity; ++i)
        if (pool->pages[i].state != SLANG_PAGE_FREE && pool->pages[i].handle == handle) return i;
    return -1;
}

static struct slang_physical_transaction *slang_physical_transaction_get(int64_t handle) {
    if (!g_physical_pool.active || handle <= 0) return NULL;
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; ++i) {
        struct slang_physical_transaction *transaction = &g_physical_pool.transactions[i];
        if (transaction->active && transaction->handle == handle) return transaction;
    }
    return NULL;
}

static void slang_physical_transaction_clear(struct slang_physical_transaction *transaction, int committed) {
    if (transaction == NULL || !transaction->active) return;
    for (int64_t i = 0; i < transaction->count; ++i) {
        int64_t slot = transaction->page_slots[i];
        if (slot < 0 || slot >= g_physical_pool.page_capacity) continue;
        struct slang_physical_page *page = &g_physical_pool.pages[slot];
        if (transaction->initial_states[i] == SLANG_PAGE_WRITABLE) {
            page->state = committed ? SLANG_PAGE_SEALED : SLANG_PAGE_WRITABLE;
            page->occupied = committed ? transaction->initial_rows[i] + transaction->additional_rows[i]
                                       : transaction->initial_rows[i];
        }
    }
    free(transaction->page_slots);
    free(transaction->initial_rows);
    free(transaction->initial_states);
    free(transaction->additional_rows);
    memset(transaction, 0, sizeof(*transaction));
}

static void slang_physical_request_detach(int64_t request_handle) {
    if (!g_physical_pool.active) return;
    struct slang_request *request = slang_request_get(request_handle);
    int64_t slot = slang_request_slot(request);
    if (slot < 0) return;
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; ++i) {
        struct slang_physical_transaction *transaction = &g_physical_pool.transactions[i];
        if (transaction->active && transaction->request_handle == request_handle) {
            llama_slang_paged_abort(g_physical_pool.ctx, transaction->handle);
            slang_physical_transaction_clear(transaction, 0);
        }
    }
    if (g_physical_pool.request_handles[slot] > 0) {
        llama_slang_paged_request_close(g_physical_pool.ctx, g_physical_pool.request_handles[slot]);
        g_physical_pool.request_handles[slot] = 0;
    }
    if (request != NULL) {
        free(request->paged_logits);
        request->paged_logits = NULL;
        request->paged_logits_valid = 0;
    }
}
#endif

static struct slang_request *slang_compat_request(void) {
    return slang_request_get(g_compat_handle);
}

/* ---- input string buffer -------------------------------------------- */

int64_t slang_ggml_request_str_reset(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
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

static int64_t slang_request_create_impl(int64_t n_ctx, int physical_only) {
    if (g_model == NULL) return SLANG_ERR_NO_MODEL;
    if (n_ctx <= 0 || n_ctx > INT32_MAX) return SLANG_ERR_INVALID;
    if (g_request_count >= g_request_capacity) return SLANG_ERR_BUSY;
    int64_t slot = -1;
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; i++) {
        if (!g_requests[i].active) { slot = i; break; }
    }
    if (slot < 0) return SLANG_ERR_BUSY;
    struct slang_request *old = &g_requests[slot];
    if (old->generation >= SLANG_REQUEST_MAX_GENERATION)
        return SLANG_ERR_EXHAUSTED;

    struct llama_context *ctx = NULL;
    struct llama_sampler *smpl = NULL;
    struct llama_sampler *greedy = NULL;
    if (!physical_only) {
        struct llama_context_params cp = llama_context_default_params();
        cp.n_ctx = (uint32_t)n_ctx;
        cp.n_batch = cp.n_ctx;
        ctx = llama_init_from_model(g_model, cp);
        if (ctx == NULL) return SLANG_ERR_NO_CTX;
        struct llama_sampler_chain_params sp = llama_sampler_chain_default_params();
        smpl = llama_sampler_chain_init(sp);
        greedy = llama_sampler_init_greedy();
    }
    char *str = (char *)malloc(SLANG_STR_CAP);
    char *out = (char *)malloc(SLANG_OUT_CAP);
    llama_token *tok = (llama_token *)malloc((size_t)SLANG_TOK_CAP * sizeof(llama_token));
    if ((!physical_only && (smpl == NULL || greedy == NULL)) || str == NULL || out == NULL || tok == NULL) {
        if (greedy) llama_sampler_free(greedy);
        if (smpl) llama_sampler_free(smpl);
        llama_free(ctx);
        free(str); free(out); free(tok);
        return SLANG_ERR_NO_CTX;
    }
    if (!physical_only) llama_sampler_chain_add(smpl, greedy);
    uint64_t generation = old->generation == 0 ? 1 : old->generation;
    memset(old, 0, sizeof(*old));
    old->ctx = ctx; old->smpl = smpl;
    old->str = str; old->out = out; old->tok = tok;
    old->eval_start = 0; old->selected_prefix = -1; old->lease_slot = -1;
    old->physical_only = physical_only;
    old->context_limit = n_ctx;
    old->generation = generation; old->model_generation = g_model_generation;
    old->active = 1;
    g_request_count++;
    return slang_request_handle(slot, generation);
}

int64_t slang_ggml_request_create(int64_t n_ctx) {
    return slang_request_create_impl(n_ctx > 0 ? n_ctx : 4096, 0);
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
 * checked independent request ownership under one serial executor. Bit 5 is
 * advertised only when this shim was compiled against the complete external
 * paged-request API. */
int64_t slang_ggml_capabilities(void) {
    return 1 | 2 | 4 | 8 | 16 |
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
        SLANG_CAP_PHYSICAL_PAGED_KV | SLANG_CAP_PHYSICAL_LIGHTWEIGHT_REQUESTS;
#else
        0;
#endif
}

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
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    slang_physical_request_detach(handle);
#endif
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
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    if (g_physical_pool.active) return SLANG_ERR_BUSY;
#endif
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
    return request == NULL ? SLANG_ERR_INVALID : request->context_limit;
}

int64_t slang_ggml_n_ctx(void) {
    return slang_ggml_request_n_ctx(g_compat_handle);
}

/* Tokenizes the string buffer. Returns the token count, which the caller reads
 * back one id at a time via slang_ggml_token_at. */
int64_t slang_ggml_request_tokenize(int64_t handle, int64_t add_bos) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
    request->legacy_logits_valid = 0;
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
    if (request->ctx == NULL) return SLANG_ERR_INVALID;
    slang_request_release_lease(request);
    llama_memory_clear(llama_get_memory(request->ctx), true);
    request->eval_start = 0;
    request->legacy_logits_valid = 0;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
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
    if (request->ctx == NULL) return SLANG_ERR_INVALID;
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
    if (request->ctx == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
    request->legacy_logits_valid = 0;
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
    request->legacy_logits_valid = 1;
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
    if (request->ctx == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
    request->legacy_logits_valid = 0;
    llama_token t = (llama_token)token;
    struct llama_batch batch = llama_batch_get_one(&t, 1);
    if (llama_decode(request->ctx, batch) != 0) {
        slang_request_release_lease(request);
        return SLANG_ERR_DECODE;
    }
    request->legacy_logits_valid = 1;
    return 0;
}

int64_t slang_ggml_eval(int64_t token) {
    return slang_ggml_request_eval(g_compat_handle, token);
}

int64_t slang_ggml_request_sample(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    if (request->paged_logits_valid && request->paged_logits != NULL) {
        int32_t count = llama_vocab_n_tokens(llama_model_get_vocab(g_model));
        if (count <= 0) return SLANG_ERR_DECODE;
        int32_t best = 0;
        for (int32_t i = 1; i < count; ++i)
            if (request->paged_logits[i] > request->paged_logits[best]) best = i;
        if (slang_ggml_is_eog(best) == 1) slang_request_release_lease(request);
        return best;
    }
    int64_t request_slot = slang_request_slot(request);
    if (g_physical_pool.active && request_slot >= 0 &&
        g_physical_pool.request_handles[request_slot] > 0)
        return SLANG_ERR_DECODE;
#endif
    if (!request->legacy_logits_valid) return SLANG_ERR_DECODE;
    int64_t token = (int64_t)llama_sampler_sample(request->smpl, request->ctx, -1);
    if (slang_ggml_is_eog(token) == 1) slang_request_release_lease(request);
    return token;
}

int64_t slang_ggml_vocab_size(void) {
    return g_model == NULL ? SLANG_ERR_NO_MODEL :
        (int64_t)llama_vocab_n_tokens(llama_model_get_vocab(g_model));
}

int64_t slang_ggml_request_logit_bits(int64_t handle, int64_t index) {
    struct slang_request *request = slang_request_get(handle);
    int64_t count = slang_ggml_vocab_size();
    if (request == NULL || index < 0 || index >= count) return SLANG_ERR_INVALID;
    const float *logits = NULL;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    if (request->paged_logits_valid && request->paged_logits != NULL) {
        logits = request->paged_logits;
    } else {
        int64_t request_slot = slang_request_slot(request);
        if (g_physical_pool.active && request_slot >= 0 &&
            g_physical_pool.request_handles[request_slot] > 0)
            return SLANG_ERR_DECODE;
    }
#endif
    if (logits == NULL) {
        if (!request->legacy_logits_valid) return SLANG_ERR_DECODE;
        logits = llama_get_logits_ith(request->ctx, -1);
    }
    if (logits == NULL) return SLANG_ERR_DECODE;
    uint32_t bits = 0;
    memcpy(&bits, &logits[index], sizeof(bits));
    return (int64_t)bits;
}

int64_t slang_ggml_sample(void) {
    return slang_ggml_request_sample(g_compat_handle);
}

#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
/* ---- external physical-page provider ------------------------------- */

int64_t slang_ggml_page_abi_version(void) {
    return SLANG_PHYSICAL_PAGE_ABI_V1;
}

int64_t slang_ggml_page_execution_namespace(void) {
    return slang_physical_namespace();
}

int64_t slang_ggml_page_pool_create(int64_t execution_namespace,
                                    int64_t page_tokens,
                                    int64_t page_capacity,
                                    int64_t byte_limit) {
    if (g_physical_pool.active) return SLANG_ERR_BUSY;
    if (g_model == NULL || execution_namespace <= 0 || execution_namespace != slang_physical_namespace() ||
        page_tokens <= 0 || page_tokens > INT32_MAX || page_capacity <= 0 || page_capacity > INT32_MAX ||
        byte_limit <= 0) return SLANG_ERR_INVALID;

    int32_t n_vocab = llama_vocab_n_tokens(llama_model_get_vocab(g_model));
    if (n_vocab <= 0 || llama_slang_paged_abi_version() != LLAMA_SLANG_PAGED_PROVIDER_ABI_VERSION)
        return SLANG_ERR_INVALID;

    size_t logits_bytes = 0;
    size_t descriptor_bytes = 0;
    size_t metadata_bytes = 0;
    if (!slang_checked_mul_size((size_t)page_capacity, 1024, &descriptor_bytes) ||
        !slang_checked_mul_size((size_t)g_request_capacity, (size_t)page_capacity, &metadata_bytes) ||
        !slang_checked_mul_size(metadata_bytes, 1024, &metadata_bytes) ||
        metadata_bytes > SIZE_MAX - 1024 * 1024 ||
        !slang_checked_mul_size((size_t)g_request_capacity, (size_t)n_vocab, &logits_bytes) ||
        !slang_checked_mul_size(logits_bytes, 2 * sizeof(float), &logits_bytes))
        return SLANG_ERR_OVERFLOW;
    metadata_bytes += 1024 * 1024;

    uint64_t n_ctx = (uint64_t)page_tokens * (uint64_t)page_capacity;
    if (n_ctx == 0 || n_ctx > INT32_MAX) return SLANG_ERR_OVERFLOW;
    struct llama_context_params cp = llama_context_default_params();
    cp.n_ctx = (uint32_t)n_ctx;
    cp.n_batch = (uint32_t)n_ctx;
    cp.n_ubatch = (uint32_t)n_ctx;
    cp.n_seq_max = 1;
    cp.type_k = GGML_TYPE_F32;
    cp.type_v = GGML_TYPE_F32;
    cp.flash_attn_type = LLAMA_FLASH_ATTN_TYPE_DISABLED;
    cp.offload_kqv = false;

    struct llama_slang_paged_provider_params provider = {
        LLAMA_SLANG_PAGED_PROVIDER_ABI_VERSION,
        (uint32_t)page_tokens,
        (uint32_t)page_capacity,
        (uint32_t)g_request_capacity,
        (uint32_t)page_capacity,
        (size_t)byte_limit,
        descriptor_bytes,
        metadata_bytes,
        logits_bytes,
    };
    struct llama_context *ctx = llama_init_from_model_slang_paged_external(g_model, cp, provider);
    if (ctx == NULL) return SLANG_ERR_NO_CTX;
    size_t page_bytes = llama_slang_paged_page_bytes(ctx);
    size_t admitted_bytes = 0;
    if (page_bytes == 0 || page_bytes > INT64_MAX ||
        !slang_checked_mul_size(page_bytes, (size_t)page_capacity, &admitted_bytes) ||
        admitted_bytes > (size_t)byte_limit) {
        llama_free(ctx);
        return SLANG_ERR_OVERFLOW;
    }
    struct slang_physical_page *pages = calloc((size_t)page_capacity, sizeof(*pages));
    if (pages == NULL) {
        llama_free(ctx);
        return SLANG_ERR_NO_CTX;
    }
    if (g_physical_pool_generation == 0 || g_physical_pool_generation > (uint64_t)INT64_MAX) {
        free(pages);
        llama_free(ctx);
        return SLANG_ERR_EXHAUSTED;
    }
    memset(&g_physical_pool, 0, sizeof(g_physical_pool));
    g_physical_pool.ctx = ctx;
    g_physical_pool.pages = pages;
    g_physical_pool.handle = (int64_t)g_physical_pool_generation;
    g_physical_pool.execution_namespace = execution_namespace;
    g_physical_pool.page_tokens = page_tokens;
    g_physical_pool.page_capacity = page_capacity;
    g_physical_pool.page_bytes = (int64_t)page_bytes;
    g_physical_pool.generation = g_physical_pool_generation;
    g_physical_pool.active = 1;
    return g_physical_pool.handle;
}

int64_t slang_ggml_page_pool_destroy(int64_t pool_handle) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    if (pool == NULL) return SLANG_ERR_INVALID;
    if (pool->allocated_pages != 0) return SLANG_ERR_BUSY;
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; ++i)
        if (pool->transactions[i].active) return SLANG_ERR_BUSY;
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; ++i) {
        if (pool->request_handles[i] > 0 && llama_slang_paged_request_close(pool->ctx, pool->request_handles[i]) != 0)
            return SLANG_ERR_BUSY;
        pool->request_handles[i] = 0;
        free(g_requests[i].paged_logits);
        g_requests[i].paged_logits = NULL;
        g_requests[i].paged_logits_valid = 0;
    }
    llama_free(pool->ctx);
    free(pool->pages);
    memset(pool, 0, sizeof(*pool));
    if (g_physical_pool_generation <= (uint64_t)INT64_MAX) ++g_physical_pool_generation;
    return 0;
}

int64_t slang_ggml_page_request_create(int64_t pool_handle, int64_t n_ctx) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    if (pool == NULL || n_ctx <= 0 || n_ctx > pool->page_tokens * pool->page_capacity)
        return SLANG_ERR_INVALID;
    return slang_request_create_impl(n_ctx, 1);
}

int64_t slang_ggml_page_reserve(int64_t pool_handle) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    if (pool == NULL) return SLANG_ERR_INVALID;
    int64_t slot = -1;
    for (int64_t i = 0; i < pool->page_capacity; ++i)
        if (pool->pages[i].state == SLANG_PAGE_FREE) { slot = i; break; }
    if (slot < 0) return SLANG_ERR_BUSY;
    int64_t handle = llama_slang_paged_page_reserve(pool->ctx);
    if (handle <= 0) return SLANG_ERR_BUSY;
    pool->pages[slot].handle = handle;
    pool->pages[slot].occupied = 0;
    pool->pages[slot].state = SLANG_PAGE_WRITABLE;
    ++pool->allocated_pages;
    return handle;
}

int64_t slang_ggml_page_release(int64_t pool_handle, int64_t page_handle) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    int64_t slot = slang_physical_page_slot(pool, page_handle);
    if (slot < 0 || llama_slang_paged_page_release(pool->ctx, page_handle) != 0) return SLANG_ERR_INVALID;
    memset(&pool->pages[slot], 0, sizeof(pool->pages[slot]));
    --pool->allocated_pages;
    return 0;
}

int64_t slang_ggml_page_seal(int64_t pool_handle, int64_t page_handle) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    int64_t slot = slang_physical_page_slot(pool, page_handle);
    if (slot < 0 || pool->pages[slot].state != SLANG_PAGE_WRITABLE ||
        llama_slang_paged_page_seal(pool->ctx, page_handle) != 0)
        return SLANG_ERR_INVALID;
    pool->pages[slot].state = SLANG_PAGE_SEALED;
    return 0;
}

int64_t slang_ggml_page_copy_tail(int64_t pool_handle,
                                  int64_t source_page,
                                  int64_t destination_page,
                                  int64_t valid_rows) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    int64_t source = slang_physical_page_slot(pool, source_page);
    int64_t destination = slang_physical_page_slot(pool, destination_page);
    if (source < 0 || destination < 0 || source == destination || valid_rows <= 0 ||
        valid_rows > pool->page_tokens || pool->pages[source].state != SLANG_PAGE_SEALED ||
        pool->pages[destination].state != SLANG_PAGE_WRITABLE || pool->pages[destination].occupied != 0 ||
        valid_rows > UINT32_MAX ||
        llama_slang_paged_page_copy_tail(pool->ctx, source_page, destination_page, (uint32_t)valid_rows) != 0)
        return SLANG_ERR_INVALID;
    pool->pages[destination].occupied = valid_rows;
    return 0;
}

int64_t slang_ggml_page_table_begin(int64_t request_handle,
                                    int64_t pool_handle,
                                    int64_t table_base_position,
                                    int64_t expected_pages) {
    struct slang_request *request = slang_request_get(request_handle);
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    int64_t request_slot = slang_request_slot(request);
    if (request == NULL || pool == NULL || request_slot < 0 || table_base_position < 0 ||
        expected_pages <= 0 || expected_pages > pool->page_capacity || expected_pages > UINT32_MAX)
        return SLANG_ERR_INVALID;
    struct slang_physical_transaction *transaction = &pool->transactions[request_slot];
    if (transaction->active) return SLANG_ERR_BUSY;
    if (request->paged_logits == NULL) {
        int32_t n_vocab = llama_vocab_n_tokens(llama_model_get_vocab(g_model));
        if (n_vocab <= 0 || (size_t)n_vocab > SIZE_MAX / sizeof(float)) return SLANG_ERR_OVERFLOW;
        request->paged_logits = malloc((size_t)n_vocab * sizeof(float));
        if (request->paged_logits == NULL) return SLANG_ERR_NO_CTX;
    }
    if (pool->request_handles[request_slot] == 0) {
        pool->request_handles[request_slot] = llama_slang_paged_request_open(pool->ctx);
        if (pool->request_handles[request_slot] <= 0) return SLANG_ERR_BUSY;
    }
    int64_t *page_slots = malloc((size_t)expected_pages * sizeof(int64_t));
    int64_t *initial_rows = malloc((size_t)expected_pages * sizeof(int64_t));
    int64_t *initial_states = malloc((size_t)expected_pages * sizeof(int64_t));
    int64_t *additional_rows = malloc((size_t)expected_pages * sizeof(int64_t));
    if (page_slots == NULL || initial_rows == NULL || initial_states == NULL || additional_rows == NULL) {
        free(page_slots); free(initial_rows); free(initial_states); free(additional_rows);
        return SLANG_ERR_NO_CTX;
    }
    int64_t handle = llama_slang_paged_table_begin(pool->ctx, pool->request_handles[request_slot],
                                                   table_base_position, (uint32_t)expected_pages);
    if (handle <= 0) {
        free(page_slots); free(initial_rows); free(initial_states); free(additional_rows);
        return SLANG_ERR_BUSY;
    }
    memset(transaction, 0, sizeof(*transaction));
    transaction->handle = handle;
    transaction->request_handle = request_handle;
    transaction->page_slots = page_slots;
    transaction->initial_rows = initial_rows;
    transaction->initial_states = initial_states;
    transaction->additional_rows = additional_rows;
    transaction->capacity = expected_pages;
    transaction->active = 1;
    request->paged_logits_valid = 0;
    return handle;
}

static void slang_physical_poison_transaction(struct slang_physical_transaction *transaction) {
    if (transaction == NULL || !transaction->active) return;
    (void)llama_slang_paged_fail(g_physical_pool.ctx, transaction->handle);
    struct slang_request *request = slang_request_get(transaction->request_handle);
    if (request != NULL) request->paged_logits_valid = 0;
}

int64_t slang_ggml_page_table_push(int64_t transaction_handle,
                                   int64_t page_handle,
                                   int64_t valid_rows,
                                   int64_t writable_capacity) {
    struct slang_physical_transaction *transaction = slang_physical_transaction_get(transaction_handle);
    int64_t slot = slang_physical_page_slot(&g_physical_pool, page_handle);
    if (transaction == NULL) return SLANG_ERR_INVALID;
    if (slot < 0 || transaction->count >= transaction->capacity || valid_rows < 0 ||
        writable_capacity < 0 || valid_rows > UINT32_MAX || writable_capacity > UINT32_MAX ||
        valid_rows != g_physical_pool.pages[slot].occupied ||
        (g_physical_pool.pages[slot].state == SLANG_PAGE_SEALED && writable_capacity != 0) ||
        valid_rows + writable_capacity > g_physical_pool.page_tokens) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_INVALID;
    }
    if (llama_slang_paged_table_push(g_physical_pool.ctx, transaction_handle, page_handle,
                                     (uint32_t)valid_rows, (uint32_t)writable_capacity) != 0)
        return SLANG_ERR_INVALID;
    transaction->page_slots[transaction->count] = slot;
    transaction->initial_rows[transaction->count] = valid_rows;
    transaction->initial_states[transaction->count] = g_physical_pool.pages[slot].state;
    transaction->additional_rows[transaction->count] = writable_capacity;
    ++transaction->count;
    return 0;
}

static int64_t slang_physical_decode_tokens(struct slang_physical_transaction *transaction,
                                            const llama_token *tokens,
                                            int64_t start_position,
                                            int64_t token_count) {
    if (transaction == NULL) return SLANG_ERR_INVALID;
    int64_t admitted_tokens = 0;
    for (int64_t i = 0; i < transaction->count; ++i) {
        if (transaction->additional_rows[i] > INT64_MAX - admitted_tokens) {
            slang_physical_poison_transaction(transaction);
            return SLANG_ERR_OVERFLOW;
        }
        admitted_tokens += transaction->additional_rows[i];
    }
    if (tokens == NULL || start_position < 0 || token_count <= 0 || token_count > INT32_MAX ||
        token_count > admitted_tokens) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_INVALID;
    }
    struct slang_request *request = slang_request_get(transaction->request_handle);
    if (request == NULL || start_position > INT32_MAX || token_count - 1 > INT32_MAX - start_position) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_INVALID;
    }
    size_t count = (size_t)token_count;
    size_t pointer_bytes, scalar_bytes, total_bytes;
    if (!slang_checked_mul_size(count, sizeof(llama_seq_id *), &pointer_bytes) ||
        !slang_checked_mul_size(count, sizeof(llama_token) + sizeof(llama_pos) +
                                      sizeof(int32_t) + sizeof(llama_seq_id) + sizeof(int8_t), &scalar_bytes) ||
        !slang_checked_add_size(pointer_bytes, scalar_bytes, &total_bytes)) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_OVERFLOW;
    }
    unsigned char *storage = calloc(1, total_bytes);
    if (storage == NULL) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_NO_CTX;
    }
    struct llama_batch batch = {0};
    batch.seq_id = (llama_seq_id **)storage;
    unsigned char *cursor = storage + pointer_bytes;
    batch.token = (llama_token *)cursor; cursor += count * sizeof(llama_token);
    batch.pos = (llama_pos *)cursor; cursor += count * sizeof(llama_pos);
    batch.n_seq_id = (int32_t *)cursor; cursor += count * sizeof(int32_t);
    llama_seq_id *sequence_ids = (llama_seq_id *)cursor; cursor += count * sizeof(llama_seq_id);
    batch.logits = (int8_t *)cursor;
    batch.n_tokens = (int32_t)token_count;
    for (int32_t i = 0; i < batch.n_tokens; ++i) {
        batch.token[i] = tokens[i];
        batch.pos[i] = (llama_pos)(start_position + i);
        batch.n_seq_id[i] = 1;
        batch.seq_id[i] = &sequence_ids[i];
        batch.seq_id[i][0] = 0;
        batch.logits[i] = i + 1 == batch.n_tokens;
    }
    request->paged_logits_valid = 0;
    int32_t result = llama_slang_paged_decode(g_physical_pool.ctx, transaction->handle, batch);
    free(storage);
    return result == 0 ? 0 : SLANG_ERR_DECODE;
}

int64_t slang_ggml_page_prefill(int64_t transaction_handle,
                                int64_t start_position,
                                int64_t token_start,
                                int64_t token_count) {
    struct slang_physical_transaction *transaction = slang_physical_transaction_get(transaction_handle);
    struct slang_request *request = transaction ? slang_request_get(transaction->request_handle) : NULL;
    if (request == NULL || token_start < 0 || token_count <= 0 || token_start > request->tok_len ||
        token_count > request->tok_len - token_start) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_INVALID;
    }
    return slang_physical_decode_tokens(transaction, request->tok + token_start, start_position, token_count);
}

int64_t slang_ggml_page_decode(int64_t transaction_handle, int64_t token, int64_t position) {
    struct slang_physical_transaction *transaction = slang_physical_transaction_get(transaction_handle);
    if (transaction == NULL) return SLANG_ERR_INVALID;
    if (token < 0 || token > INT32_MAX) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_INVALID;
    }
    llama_token value = (llama_token)token;
    return slang_physical_decode_tokens(transaction, &value, position, 1);
}

int64_t slang_ggml_page_boundary_logits(int64_t transaction_handle,
                                        int64_t boundary_token_index,
                                        int64_t boundary_position) {
    struct slang_physical_transaction *transaction = slang_physical_transaction_get(transaction_handle);
    struct slang_request *request = transaction ? slang_request_get(transaction->request_handle) : NULL;
    if (request == NULL || boundary_token_index < 0 || boundary_token_index >= request->tok_len) {
        slang_physical_poison_transaction(transaction);
        return SLANG_ERR_INVALID;
    }
    return slang_physical_decode_tokens(transaction, request->tok + boundary_token_index, boundary_position, 1);
}

int64_t slang_ggml_page_table_commit(int64_t transaction_handle) {
    struct slang_physical_transaction *transaction = slang_physical_transaction_get(transaction_handle);
    if (transaction == NULL) return SLANG_ERR_INVALID;
    struct slang_request *request = slang_request_get(transaction->request_handle);
    int64_t request_slot = slang_request_slot(request);
    size_t n_vocab = (size_t)llama_vocab_n_tokens(llama_model_get_vocab(g_model));
    int32_t result = request != NULL && request_slot >= 0 && request->paged_logits != NULL ?
        llama_slang_paged_commit_and_copy(g_physical_pool.ctx, transaction_handle,
                                          request->paged_logits, n_vocab) : -1;
    if (result == 0) request->paged_logits_valid = 1;
    slang_physical_transaction_clear(transaction, result == 0);
    return result == 0 ? 0 : SLANG_ERR_DECODE;
}

int64_t slang_ggml_page_table_abort(int64_t transaction_handle) {
    struct slang_physical_transaction *transaction = slang_physical_transaction_get(transaction_handle);
    if (transaction == NULL) return SLANG_ERR_INVALID;
    int32_t result = llama_slang_paged_abort(g_physical_pool.ctx, transaction_handle);
    if (result == 0) slang_physical_transaction_clear(transaction, 0);
    return result == 0 ? 0 : SLANG_ERR_INVALID;
}

int64_t slang_ggml_page_allocated_bytes(int64_t pool_handle) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    if (pool == NULL || pool->allocated_pages > INT64_MAX / pool->page_bytes) return SLANG_ERR_INVALID;
    return pool->allocated_pages * pool->page_bytes;
}

int64_t slang_ggml_page_bytes(int64_t pool_handle) {
    struct slang_physical_pool *pool = slang_physical_pool_get(pool_handle);
    return pool == NULL ? SLANG_ERR_INVALID : pool->page_bytes;
}
#endif
