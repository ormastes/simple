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

/* One lock for the state every request shares: the request slot table, the
 * compat handle, the prefix cache and the model pointer. Each request owns its
 * llama_context, sampler and buffers, so llama_decode and sampling run OUTSIDE
 * the lock and two requests decode concurrently. Entry points take the lock;
 * `_locked` helpers require it. Not recursive. */
#if defined(_WIN32)
#  include <windows.h>
static SRWLOCK g_state_lock = SRWLOCK_INIT;
#  define SLANG_LOCK()   AcquireSRWLockExclusive(&g_state_lock)
#  define SLANG_UNLOCK() ReleaseSRWLockExclusive(&g_state_lock)
#else
#  include <pthread.h>
static pthread_mutex_t g_state_lock = PTHREAD_MUTEX_INITIALIZER;
#  define SLANG_LOCK()   pthread_mutex_lock(&g_state_lock)
#  define SLANG_UNLOCK() pthread_mutex_unlock(&g_state_lock)
#endif

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
/* Bit 128: the mtmd group at the end of this file; set only when built with
 * -DSLANG_WITH_MTMD, so a text-only build never advertises it. */
#ifdef SLANG_WITH_MTMD
#  define SLANG_CAP_MTMD 128
#else
#  define SLANG_CAP_MTMD 0
#endif

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
    /* Provenance of the snapshot: it is restored only into a request built
     * from the same model load and with the same context size. */
    uint64_t model_generation;
    int64_t context_limit;
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
    /* Set once this context has decoded a full micro-batch; see
     * slang_request_warm. */
    int warm;
    int physical_only;
    int64_t context_limit;
    /* Tree prefix-cache mode: ctx is the shared persistent context, seq is this
     * requests sequence id (-1 none), path = prompt + decoded tokens,
     * tree_owner = pinned terminal the prefix was copied from (-1 none). */
    int tree;
    int seq;
    int tree_owner;
    llama_token *path;
    int64_t path_len;
    int64_t path_cap;
    /* The model this request decodes: g_model (model_handle 0) or a handle
     * from slang_ggml_model_open. Embedding output is valid after embed_eval. */
    struct llama_model *model;
    int64_t model_handle;
    int64_t embed_tokens;
    int embed_valid;
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
static int g_model_offloaded = 0;
static char g_load_str[SLANG_STR_CAP];
static int64_t g_load_str_len = 0;
static int g_matched_cpu_context = 0;
static int32_t g_context_threads = 0;

/* Bit 256: bulk byte I/O (str_push_bytes / out_into). Bit 512: model handles
 * (model_open / request_create_for), the embeddings group, token input and
 * per-request sampler configuration. */
#define SLANG_CAP_BULK_IO 256
#define SLANG_CAP_MODEL_HANDLES 512
#define SLANG_MODEL_MAX_HANDLES 4
#define SLANG_MODEL_MAX_GENERATION ((uint64_t)(INT64_MAX - SLANG_MODEL_MAX_HANDLES) / SLANG_MODEL_MAX_HANDLES)

/* Models loaded beside g_model, so a chat model and an embedding model (or an
 * LLM and its vocoder) are resident together. Guarded by g_state_lock. */
struct slang_model_slot {
    struct llama_model *model;
    char *path;
    uint64_t generation;
    int64_t requests;
    /* Owners holding the handle: every model_open (including one that found the
     * path already open) takes one, every model_close gives one back, and the
     * model is freed only by the last. Concurrent per-request owners of one
     * model therefore never close it from under each other. */
    int64_t opens;
    int offloaded;
};
static struct slang_model_slot g_model_slots[SLANG_MODEL_MAX_HANDLES];
static uint64_t g_model_slot_generation = 0;

static struct slang_model_slot *slang_model_slot_get(int64_t handle) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)(handle - 1);
    struct slang_model_slot *slot = &g_model_slots[raw % SLANG_MODEL_MAX_HANDLES];
    uint64_t generation = raw / SLANG_MODEL_MAX_HANDLES;
    if (slot->model == NULL || generation == 0 || slot->generation != generation)
        return NULL;
    return slot;
}

/* A request stays valid only while the model it was built on is loaded. */
static int slang_request_model_live(const struct slang_request *request) {
    if (request->model_handle == 0)
        return request->model_generation == g_model_generation;
    struct slang_model_slot *slot = slang_model_slot_get(request->model_handle);
    return slot != NULL && slot->model == request->model;
}

static int slang_request_offloaded(const struct slang_request *request) {
    if (request->model_handle == 0) return g_model_offloaded;
    struct slang_model_slot *slot = slang_model_slot_get(request->model_handle);
    return slot != NULL && slot->offloaded;
}

static int64_t slang_request_handle(int64_t slot, uint64_t generation) {
    if (generation == 0 || generation > SLANG_REQUEST_MAX_GENERATION)
        return SLANG_ERR_EXHAUSTED;
    return (int64_t)(generation * SLANG_REQUEST_MAX_ENTRIES + (uint64_t)slot + 1);
}

/* Guard shared by the entry points that decode on a live, uncancelled context. */
static int64_t slang_request_decodable(const struct slang_request *request) {
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->ctx == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    return 0;
}

static struct slang_request *slang_request_get(int64_t handle) {
    if (handle <= 0) return NULL;
    uint64_t raw = (uint64_t)(handle - 1);
    int64_t slot = (int64_t)(raw % SLANG_REQUEST_MAX_ENTRIES);
    uint64_t generation = raw / SLANG_REQUEST_MAX_ENTRIES;
    struct slang_request *request = &g_requests[slot];
    if (!request->active || generation == 0 || request->generation != generation ||
        !slang_request_model_live(request))
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

/* ---- chat template --------------------------------------------------- */

/* Reads "<decimal byte count>:" at *at and returns the count, or -1. */
static int64_t slang_chat_frame_len(const char *s, int64_t len, int64_t *at) {
    int64_t i = *at, n = 0, digits = 0;
    while (i < len && s[i] >= '0' && s[i] <= '9') {
        n = n * 10 + (s[i] - '0');
        if (n > len) return -1;
        i++; digits++;
    }
    if (digits == 0 || i >= len || s[i] != ':' || n > len - (i + 1)) return -1;
    *at = i + 1;
    return n;
}

/* Replaces the request string buffer, which must hold the chat as frames
 * "<role bytes>:<role><content bytes>:<content>" (one pair per message, in
 * order), with the prompt the MODEL's own chat template renders for it,
 * ending in the assistant generation prefix. Returns 1 when the GGUF template
 * was applied and 2 when llama.cpp does not recognise it (or the model carries
 * none) and ChatML was used instead. */
int64_t slang_ggml_request_chat_render(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->model == NULL) return SLANG_ERR_NO_MODEL;
    const char *src = request->str;
    int64_t len = request->str_len;
    int64_t fields = 0;
    for (int64_t at = 0; at < len; fields++) {
        int64_t n = slang_chat_frame_len(src, len, &at);
        if (n < 0) return SLANG_ERR_INVALID;
        at += n;
    }
    if (fields == 0 || (fields % 2) != 0) return SLANG_ERR_INVALID;
    size_t count = (size_t)(fields / 2);
    struct llama_chat_message *messages =
        (struct llama_chat_message *)calloc(count, sizeof(*messages));
    char *work = (char *)malloc((size_t)len + (size_t)fields + 1);
    char *rendered = (char *)malloc(SLANG_STR_CAP);
    int64_t result = SLANG_ERR_OVERFLOW;
    if (messages != NULL && work != NULL && rendered != NULL) {
        char *cursor = work;
        int64_t at = 0;
        for (int64_t field = 0; field < fields; field++) {
            int64_t n = slang_chat_frame_len(src, len, &at);
            memcpy(cursor, src + at, (size_t)n);
            cursor[n] = '\0';
            if ((field % 2) == 0) messages[field / 2].role = cursor;
            else messages[field / 2].content = cursor;
            cursor += n + 1;
            at += n;
        }
        const char *tmpl = llama_model_chat_template(request->model, NULL);
        int32_t n = tmpl == NULL ? -1 :
            llama_chat_apply_template(tmpl, messages, count, true, rendered, SLANG_STR_CAP);
        result = 1;
        if (n < 0) {
            n = llama_chat_apply_template("chatml", messages, count, true, rendered, SLANG_STR_CAP);
            result = 2;
        }
        if (n < 0) {
            result = SLANG_ERR_TOKENIZE;
        } else if (n >= SLANG_STR_CAP) {
            result = SLANG_ERR_OVERFLOW;
        } else {
            memcpy(request->str, rendered, (size_t)n);
            request->str[n] = '\0';
            request->str_len = n;
        }
    }
    free(messages); free(work); free(rendered);
    return result;
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

/* ggml-vulkan reads GGML_VK_DISABLE_FUSION once, when it creates the device, and
 * keeps the device for the process. Tree KV mode 3 gives the cache a 16-stream
 * KV layout; with fusion on, the one-stream cache-off graph runs the fused
 * rms_norm/rope/set_rows kernels while the multi-stream graph does not, so the
 * two paths differ in the last bits. Mode 3 can be configured at any time, so
 * fusion is turned off here, before any device exists. An explicit value from
 * the environment wins. See doc/08_tracking/bug/
 * slang_tree_kv_gemma_branching_digest_differs_on_vulkan_2026-11-22.md (C1). */
static void slang_vulkan_fusion_off(void) {
    if (getenv("GGML_VK_DISABLE_FUSION") != NULL) return;
#if defined(_WIN32)
    _putenv_s("GGML_VK_DISABLE_FUSION", "1");
#else
    setenv("GGML_VK_DISABLE_FUSION", "1", 0);
#endif
}

int64_t slang_ggml_backend_init(void) {
    slang_vulkan_fusion_off();
    llama_backend_init();
    return 0;
}

/* Loads the model whose path is in the string buffer. n_gpu_layers < 0 means
 * "offload everything"; 0 keeps the model on the CPU. */
static int64_t slang_model_load_locked(int64_t n_gpu_layers) {
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
    /* "Offloaded" means layers can really go to a GPU. The engine asks for -1
     * (all layers) on every host, so on a CPU-only llama.cpp the requested
     * count alone armed the CUDA first-micro-batch workaround below: a prefix
     * restore gave back reuse until its suffix was a full n_ubatch (measured
     * 2026-11-14, Windows mingw CPU: 512 of ~990 prompt tokens re-prefilled on
     * an exact repeat; doc/08_tracking/bug/slang_prefix_cache_cpu_offload_misdetect_2026-11-14.md). */
    g_model_offloaded = mp.n_gpu_layers != 0 && llama_supports_gpu_offload();
    return 0;
}

/* Offload evidence: 1 when this llama.cpp build can place layers on a GPU
 * device, and 1 when the resident model was loaded with layers requested there. */
int64_t slang_ggml_gpu_offload_supported(void) { return llama_supports_gpu_offload() ? 1 : 0; }
int64_t slang_ggml_model_offloaded(void) { return g_model_offloaded ? 1 : 0; }

int64_t slang_ggml_model_load(int64_t n_gpu_layers) {
    SLANG_LOCK();
    int64_t result = slang_model_load_locked(n_gpu_layers);
    SLANG_UNLOCK();
    return result;
}

int64_t slang_ggml_request_configure(int64_t entries) {
    if (entries < 1 || entries > SLANG_REQUEST_MAX_ENTRIES)
        return SLANG_ERR_OVERFLOW;
    if (g_request_count > entries) return SLANG_ERR_BUSY;
    g_request_capacity = entries;
    return entries;
}

int64_t slang_ggml_context_profile_configure(int64_t matched_cpu, int64_t threads) {
    if ((matched_cpu != 0 && matched_cpu != 1) || threads < 0 || threads > INT32_MAX)
        return SLANG_ERR_INVALID;
    if (g_request_count != 0) return SLANG_ERR_BUSY;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    if (g_physical_pool.active) return SLANG_ERR_BUSY;
#endif
    g_matched_cpu_context = matched_cpu != 0;
    g_context_threads = (int32_t)threads;
    return 0;
}

static void slang_request_release_lease(struct slang_request *request);
static void slang_prefix_clear_all(int count_eviction);

/* ---- radix (tree) prefix cache: one persistent multi-sequence context -----
 *
 * Mode 1 of slang_ggml_prefix_cache_mode_configure. Instead of one llama_context
 * per request plus whole-state snapshots, every request runs on ONE persistent
 * llama_context created with n_seq_max = SLANG_TREE_MAX_SEQS and kv_unified.
 * A token radix tree maps cached paths to llama sequence ids: each TERMINAL
 * node owns one seq id whose KV holds exactly its full path. A new request
 * matches its longest cached prefix, takes a free seq id, llama_memory_seq_cp's
 * the matched cells from the owner (unified mode only adds the new seq id to
 * the existing cells: shared prefix cells are stored once, no KV bytes copied),
 * decodes only the suffix with its own seq id, and when it finishes its path
 * (prompt plus decoded tokens) is inserted. Eviction of an unpinned terminal is
 * llama_memory_seq_rm of its seq id: cells shared with other seqs survive.
 *
 * Concurrency contract (unchanged from snapshot mode): requests are serialised
 * per model. The shared context has one logits buffer, so exactly one tree
 * request may be between prefix_prepare and its release; a second gets
 * SLANG_ERR_BUSY (g_tree_active). All tree state is guarded by g_state_lock,
 * the lock that already guards the snapshot cache; no new lock is introduced.
 * Decodes run outside the lock, as in snapshot mode. */
#define SLANG_TREE_MAX_SEQS  16
#define SLANG_TREE_MAX_NODES 1024

struct slang_tree_node {
    int used;
    llama_token *tok;      /* edge label */
    int64_t n;
    int64_t start;         /* position of the first edge token */
    int parent, first_child, next_sibling;
    int seq;               /* >= 0: terminal, owns this seq id */
    /* Cells [0, exact_upto) were computed as full aligned micro-batches (prompt
     * length rounded down to n_ubatch); cells past it came from generation or a
     * partial chunk and must not be reused by the exact modes. */
    int64_t exact_upto;
    int64_t pins;
    uint64_t last_used;
};

static struct slang_tree_node g_tree_node[SLANG_TREE_MAX_NODES];
static int g_tree_seq_used[SLANG_TREE_MAX_SEQS];
static int g_tree_seq_dirty[SLANG_TREE_MAX_SEQS];   /* stream may hold stale K/V data */
static int g_tree_mode = 0;
static struct llama_context *g_tree_ctx = NULL;
static int64_t g_tree_limit = 0;      /* per-request context limit of g_tree_ctx */
static int64_t g_tree_cells_cfg = 0;  /* 0 = 4 x the first request's n_ctx */
static int64_t g_tree_cells = 0;
static int64_t g_tree_active = 0;     /* handle of the request on the context */
static int g_tree_warm = 0;           /* the context has run a full micro-batch */

/* Mode 3 keeps the last two seq ids out of circulation: the last is a never-decoded
 * "pristine" stream a request stream is zeroed from (slang_tree_zero_stream), the
 * one before it is the scratch stream slang_tree_flush_stream_copies decodes on. */
#define SLANG_TREE_PRISTINE_SEQ (SLANG_TREE_MAX_SEQS - 1)
#define SLANG_TREE_SCRATCH_SEQ  (SLANG_TREE_MAX_SEQS - 2)
static int slang_tree_usable_seqs(void) {
    return g_tree_mode == 3 ? SLANG_TREE_MAX_SEQS - 2 : SLANG_TREE_MAX_SEQS;
}

static int64_t slang_tree_capacity(void) {
    int64_t room = slang_tree_usable_seqs() - 1;
    return g_prefix_capacity < room ? g_prefix_capacity : room;
}

static void slang_tree_node_init(int i) {
    memset(&g_tree_node[i], 0, sizeof(g_tree_node[i]));
    g_tree_node[i].used = 1;
    g_tree_node[i].parent = -1; g_tree_node[i].first_child = -1;
    g_tree_node[i].next_sibling = -1; g_tree_node[i].seq = -1;
}

static void slang_tree_reset_root(void) {
    memset(g_tree_node, 0, sizeof(g_tree_node));
    slang_tree_node_init(0);
}

static int slang_tree_node_alloc(void) {
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++) {
        if (!g_tree_node[i].used) { slang_tree_node_init(i); return i; }
    }
    return -1;
}

static int slang_tree_free_nodes(void) {
    int free_nodes = 0;
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++) if (!g_tree_node[i].used) free_nodes++;
    return free_nodes;
}

static int64_t slang_tree_terminals(void) {
    int64_t count = 0;
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++)
        if (g_tree_node[i].used && g_tree_node[i].seq >= 0) count++;
    return count;
}

static int64_t slang_tree_node_count(void) {
    int64_t count = 0;
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++) if (g_tree_node[i].used) count++;
    return count;
}

/* Tokens held by the tree: each shared prefix counted once. */
static int64_t slang_tree_cached_tokens(void) {
    int64_t total = 0;
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++)
        if (g_tree_node[i].used) total += g_tree_node[i].n;
    return total;
}

/* Tokens that sharing saved: sum of terminal path lengths minus unique tokens. */
static int64_t slang_tree_shared_tokens(void) {
    int64_t paths = 0;
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++)
        if (g_tree_node[i].used && g_tree_node[i].seq >= 0)
            paths += g_tree_node[i].start + g_tree_node[i].n;
    int64_t shared = paths - slang_tree_cached_tokens();
    return shared > 0 ? shared : 0;
}

static int slang_tree_child_for(int parent, llama_token first) {
    for (int c = g_tree_node[parent].first_child; c >= 0; c = g_tree_node[c].next_sibling)
        if (g_tree_node[c].tok[0] == first) return c;
    return -1;
}

static void slang_tree_unlink(int node) {
    int parent = g_tree_node[node].parent;
    int *link = &g_tree_node[parent].first_child;
    while (*link >= 0 && *link != node) link = &g_tree_node[*link].next_sibling;
    if (*link == node) *link = g_tree_node[node].next_sibling;
}

/* Longest cached prefix of tok[0..len). Returns the matched length and the node
 * whose edge holds the last matched token (root when nothing matched). */
static int64_t slang_tree_match(const llama_token *tok, int64_t len, int *node_out) {
    int cur = 0;
    int64_t pos = 0;
    *node_out = 0;
    while (pos < len) {
        int child = slang_tree_child_for(cur, tok[pos]);
        if (child < 0) break;
        struct slang_tree_node *c = &g_tree_node[child];
        int64_t k = 0;
        while (k < c->n && pos + k < len && c->tok[k] == tok[pos + k]) k++;
        pos += k;
        *node_out = child;
        if (k < c->n) break;
        cur = child;
    }
    return pos;
}

/* Best terminal in the subtree rooted at node, or -1: the one that can supply
 * the most exact cells up to cap, ties broken by recency. */
static int64_t slang_tree_usable(int t, int64_t cap) {
    int64_t e = g_tree_node[t].exact_upto;
    int64_t len = g_tree_node[t].start + g_tree_node[t].n;   /* cells the terminal holds */
    if (len < e) e = len;
    return e < cap ? e : cap;
}
static int slang_tree_find_terminal(int node, int64_t cap) {
    int best = g_tree_node[node].seq >= 0 ? node : -1;
    for (int c = g_tree_node[node].first_child; c >= 0; c = g_tree_node[c].next_sibling) {
        int t = slang_tree_find_terminal(c, cap);
        if (t < 0) continue;
        if (best < 0) { best = t; continue; }
        int64_t ut = slang_tree_usable(t, cap), ub = slang_tree_usable(best, cap);
        if (ut > ub || (ut == ub && g_tree_node[t].last_used > g_tree_node[best].last_used))
            best = t;
    }
    return best;
}

/* find_terminal over the subtree plus the terminals on the way down to it: a
 * shorter cached prompt that is a prefix of this one can hold more exact cells
 * than a longer path whose tail came from generation. */
static int slang_tree_pick_owner(int node, int64_t cap) {
    int best = slang_tree_find_terminal(node, cap);
    for (int a = g_tree_node[node].parent; a > 0; a = g_tree_node[a].parent) {
        if (g_tree_node[a].seq < 0) continue;
        if (best < 0 || slang_tree_usable(a, cap) > slang_tree_usable(best, cap)) best = a;
    }
    return best;
}

/* Splits node's edge at k (0 < k < n): a new non-terminal parent keeps the
 * first k tokens, node keeps its index, seq and pins and the remaining tail. */
static int slang_tree_split(int node, int64_t k) {
    int p = slang_tree_node_alloc();
    if (p < 0) return -1;
    struct slang_tree_node *x = &g_tree_node[node];
    struct slang_tree_node *np = &g_tree_node[p];
    np->tok = (llama_token *)malloc((size_t)k * sizeof(llama_token));
    if (np->tok == NULL) { np->used = 0; return -1; }
    memcpy(np->tok, x->tok, (size_t)k * sizeof(llama_token));
    np->n = k; np->start = x->start;
    np->parent = x->parent;
    np->next_sibling = x->next_sibling;
    int *link = &g_tree_node[x->parent].first_child;
    while (*link >= 0 && *link != node) link = &g_tree_node[*link].next_sibling;
    *link = p;
    memmove(x->tok, x->tok + k, (size_t)(x->n - k) * sizeof(llama_token));
    x->n -= k; x->start += k;
    x->parent = p; x->next_sibling = -1;
    np->first_child = node;
    np->last_used = x->last_used;
    return p;
}

static void slang_tree_free_seq(int seq);

/* Inserts a full path whose KV lives on seq. Returns 1 when seq became a
 * terminal, 0 when the tree was left untouched (duplicate path or no room). */
static int slang_tree_insert(const llama_token *path, int64_t len, int seq, int64_t exact) {
    if (len <= 0 || slang_tree_free_nodes() < 2) return 0;
    int cur = 0;
    int64_t pos = 0;
    while (pos < len) {
        int child = slang_tree_child_for(cur, path[pos]);
        if (child < 0) {
            int leaf = slang_tree_node_alloc();
            if (leaf < 0) return 0;
            struct slang_tree_node *l = &g_tree_node[leaf];
            l->n = len - pos;
            l->tok = (llama_token *)malloc((size_t)l->n * sizeof(llama_token));
            if (l->tok == NULL) { l->used = 0; return 0; }
            memcpy(l->tok, path + pos, (size_t)l->n * sizeof(llama_token));
            l->start = pos; l->parent = cur;
            l->next_sibling = g_tree_node[cur].first_child;
            g_tree_node[cur].first_child = leaf;
            cur = leaf;
            pos = len;
            break;
        }
        struct slang_tree_node *c = &g_tree_node[child];
        int64_t k = 0;
        while (k < c->n && pos + k < len && c->tok[k] == path[pos + k]) k++;
        if (k < c->n) {
            int p = slang_tree_split(child, k);
            if (p < 0) return 0;
            child = p;
        }
        pos += k;
        cur = child;
    }
    if (g_tree_node[cur].seq >= 0) {
        g_tree_node[cur].last_used = ++g_prefix_clock;
        /* Same path already cached. If this run computed more of it as exact
         * aligned micro-batches, its sequence replaces the older one (an
         * exact_upto can only be raised together with the cells it describes). */
        if (exact > g_tree_node[cur].exact_upto && g_tree_node[cur].pins == 0) {
            slang_tree_free_seq(g_tree_node[cur].seq);
            g_tree_node[cur].seq = seq;
            g_tree_node[cur].exact_upto = exact;
            return 1;
        }
        return 0;
    }
    g_tree_node[cur].seq = seq;
    g_tree_node[cur].exact_upto = exact;
    g_tree_node[cur].last_used = ++g_prefix_clock;
    return 1;
}

/* Keeps the tree radix after a terminal is cleared: drops an empty leaf chain,
 * and folds a non-terminal single-child node into that child (the child keeps
 * its index, so a pinned terminal's index is stable). */
static void slang_tree_compact(int node) {
    while (node > 0 && g_tree_node[node].seq < 0 && g_tree_node[node].first_child < 0) {
        int parent = g_tree_node[node].parent;
        slang_tree_unlink(node);
        free(g_tree_node[node].tok);
        memset(&g_tree_node[node], 0, sizeof(g_tree_node[node]));
        node = parent;
    }
    if (node > 0 && g_tree_node[node].seq < 0) {
        int child = g_tree_node[node].first_child;
        if (child >= 0 && g_tree_node[child].next_sibling < 0) {
            struct slang_tree_node *p = &g_tree_node[node];
            struct slang_tree_node *c = &g_tree_node[child];
            llama_token *merged = (llama_token *)malloc((size_t)(p->n + c->n) * sizeof(llama_token));
            if (merged == NULL) return;
            memcpy(merged, p->tok, (size_t)p->n * sizeof(llama_token));
            memcpy(merged + p->n, c->tok, (size_t)c->n * sizeof(llama_token));
            free(c->tok);
            c->tok = merged; c->n += p->n; c->start = p->start;
            c->parent = p->parent; c->next_sibling = p->next_sibling;
            int *link = &g_tree_node[p->parent].first_child;
            while (*link >= 0 && *link != node) link = &g_tree_node[*link].next_sibling;
            *link = child;
            free(p->tok);
            memset(p, 0, sizeof(*p));
        }
    }
}

static int slang_tree_alloc_seq(void) {
    for (int i = 0; i < slang_tree_usable_seqs(); i++)
        if (!g_tree_seq_used[i]) { g_tree_seq_used[i] = 1; return i; }
    return -1;
}

static void slang_tree_free_seq(int seq) {
    if (g_tree_ctx != NULL)
        llama_memory_seq_rm(llama_get_memory(g_tree_ctx), seq, -1, -1);
    if (seq >= 0 && seq < SLANG_TREE_MAX_SEQS) g_tree_seq_used[seq] = 0;
}

/* Evicts the least recently used unpinned terminal. Returns 1 if one went. */
static int slang_tree_evict_lru(void) {
    int victim = -1;
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++) {
        struct slang_tree_node *n = &g_tree_node[i];
        if (!n->used || n->seq < 0 || n->pins > 0) continue;
        if (victim < 0 || n->last_used < g_tree_node[victim].last_used) victim = i;
    }
    if (victim < 0) return 0;
    slang_tree_free_seq(g_tree_node[victim].seq);
    g_tree_node[victim].seq = -1;
    slang_tree_compact(victim);
    g_prefix_evictions++;
    return 1;
}

static void slang_tree_evict_to(int64_t capacity) {
    while (slang_tree_terminals() > capacity && slang_tree_evict_lru()) {}
}

/* Drops the whole tree and its context. Callers guarantee no live request. */
static void slang_tree_destroy(void) {
    for (int i = 1; i < SLANG_TREE_MAX_NODES; i++)
        if (g_tree_node[i].used) free(g_tree_node[i].tok);
    slang_tree_reset_root();
    memset(g_tree_seq_used, 0, sizeof(g_tree_seq_used));
    memset(g_tree_seq_dirty, 0, sizeof(g_tree_seq_dirty));
    if (g_tree_ctx != NULL) { llama_free(g_tree_ctx); g_tree_ctx = NULL; }
    g_tree_limit = 0; g_tree_cells = 0; g_tree_active = 0; g_tree_warm = 0;
}

/* Mode 3, option (b) of slang_tree_kv_gemma_branching_digest_differs_on_vulkan_2026-11-22.md:
 * a stream a request takes may hold K/V cells of an earlier, longer request past
 * the new frontier, and flash attention is not independent of them. A seq_cp from
 * the never-decoded pristine stream replaces the whole destination stream (data
 * and cell table) with zeros. */
static void slang_tree_zero_stream(int seq) {
    if (g_tree_mode != 3 || !g_tree_seq_dirty[seq]) return;
    llama_memory_seq_cp(llama_get_memory(g_tree_ctx), SLANG_TREE_PRISTINE_SEQ, seq, -1, -1);
    g_tree_seq_dirty[seq] = 0;
}

/* llama.cpp queues a cross-stream seq_cp and applies the buffer copy at the next
 * decode, so a state_seq get/set issued right after one would read or write the
 * stream before the copy lands (and the copy would then overwrite the restore).
 * One token decoded on the scratch stream runs the queued copies; the scratch
 * cells are dropped again. Returns 1 on success. */
static int slang_tree_flush_stream_copies(void) {
    if (!g_tree_warm) return 0;   /* the first decode of a context must be a full micro-batch */
    struct llama_batch batch = llama_batch_init(1, 0, 1);
    batch.token[0] = 0;
    batch.pos[0] = 0;
    batch.n_seq_id[0] = 1;
    batch.seq_id[0][0] = SLANG_TREE_SCRATCH_SEQ;
    batch.logits[0] = 0;
    batch.n_tokens = 1;
    int rc = llama_decode(g_tree_ctx, batch);
    llama_batch_free(batch);
    llama_memory_seq_rm(llama_get_memory(g_tree_ctx), SLANG_TREE_SCRATCH_SEQ, -1, -1);
    return rc == 0;
}

/* Mode 3 reuse: copy the owner's stream, drop the tail, serialise the surviving
 * prefix through host memory, zero the stream, and restore only the prefix, so
 * no cell of the owner's tail survives past the reused frontier. Returns 1 when
 * the stream then holds exactly `reuse` cells. */
static int slang_tree_restore_prefix_host(int owner_seq, int seq, int64_t reuse) {
    llama_memory_t memory = llama_get_memory(g_tree_ctx);
    llama_memory_seq_cp(memory, owner_seq, seq, -1, -1);
    llama_memory_seq_rm(memory, seq, (llama_pos)reuse, -1);
    int ok = 0;
    if (!slang_tree_flush_stream_copies()) return 0;
    size_t size = llama_state_seq_get_size(g_tree_ctx, seq);
    uint8_t *blob = size > 0 ? (uint8_t *)malloc(size) : NULL;
    if (blob != NULL && llama_state_seq_get_data(g_tree_ctx, blob, size, seq) == size) {
        slang_tree_zero_stream(seq);
        if (slang_tree_flush_stream_copies())
            ok = llama_state_seq_set_data(g_tree_ctx, blob, size, seq) == size;
        g_tree_seq_dirty[seq] = 1;
    }
    free(blob);
    return ok;
}

static int slang_tree_kv_holds(int seq, int64_t count) {
    llama_memory_t memory = llama_get_memory(g_tree_ctx);
    return llama_memory_seq_pos_min(memory, seq) == 0 &&
           (int64_t)llama_memory_seq_pos_max(memory, seq) == count - 1;
}

/* Ends a tree request: unpins its owner, inserts prompt+decoded path as a new
 * terminal (or frees its seq id when it cannot be kept) and frees the context
 * for the next request. Idempotent. */
static void slang_tree_release_locked(struct slang_request *request) {
    if (request->tree_owner >= 0) {
        struct slang_tree_node *o = &g_tree_node[request->tree_owner];
        if (o->used && o->pins > 0) o->pins--;
        request->tree_owner = -1;
    }
    if (request->seq < 0) return;
    int seq = request->seq;
    int inserted = 0;
    if (g_tree_ctx != NULL && slang_tree_capacity() > 0 && request->path_len > 0 &&
        slang_tree_kv_holds(seq, request->path_len))
    {
        /* Exact modes: only whole aligned micro-batches of the PROMPT are
         * reusable. The last prompt token is decoded alone, so the aligned
         * span is (decoded prompt - 1) rounded down to n_ubatch. */
        /* tok_len is this request's prompt: slang_ggml_request_tokenize releases
         * the previous request state (this function) before it overwrites tok,
         * so tok_len and path agree here. path_len < tok_len means the prefill
         * stopped early; the min below bounds exactness by what was decoded. */
        int64_t exact = INT64_MAX;
        if (g_tree_mode != 2) {
            int64_t ub = (int64_t)llama_n_ubatch(g_tree_ctx);
            int64_t prompt = request->tok_len < request->path_len ? request->tok_len : request->path_len;
            exact = ub > 1 ? (prompt > 0 ? (prompt - 1) / ub * ub : 0) : prompt;
        }
        inserted = slang_tree_insert(request->path, request->path_len, seq, exact);
    }
    if (inserted) {
        g_prefix_admissions++;
        slang_tree_evict_to(slang_tree_capacity());
    } else {
        slang_tree_free_seq(seq);
    }
    request->seq = -1;
    request->path_len = 0;
    g_tree_active = 0;
}

static int slang_tree_path_reserve(struct slang_request *request, int64_t need) {
    if (need <= request->path_cap) return 1;
    int64_t cap = request->path_cap > 0 ? request->path_cap : 256;
    while (cap < need) cap *= 2;
    llama_token *grown = (llama_token *)realloc(request->path, (size_t)cap * sizeof(llama_token));
    if (grown == NULL) return 0;
    request->path = grown; request->path_cap = cap;
    return 1;
}

/* Starts a tree request: longest-prefix match, seq id, shared-cell copy. Returns
 * the number of reused prompt tokens (>= 0) or a negative error. */
static int64_t slang_tree_prepare_locked(struct slang_request *request) {
    int64_t handle = slang_request_handle((int64_t)(request - g_requests), request->generation);
    if (g_tree_active != 0 && g_tree_active != handle) return SLANG_ERR_BUSY;
    slang_tree_release_locked(request);
    request->eval_start = 0;
    request->path_len = 0;
    while (g_tree_cells > 0 &&
           slang_tree_cached_tokens() + request->context_limit > g_tree_cells &&
           slang_tree_evict_lru()) {}
    int seq = slang_tree_alloc_seq();
    if (seq < 0 && slang_tree_evict_lru()) seq = slang_tree_alloc_seq();
    if (seq < 0) return SLANG_ERR_BUSY;
    slang_tree_zero_stream(seq);
    g_tree_seq_dirty[seq] = 1;
    int64_t reuse = 0;
    int node = 0;
    int64_t matched = request->tok_len > 1
        ? slang_tree_match(request->tok, request->tok_len, &node) : 0;
    if (matched > 0) {
        /* At least one trailing token is recomputed so the backend produces
         * fresh boundary logits, as in snapshot mode. */
        reuse = matched < request->tok_len - 1 ? matched : request->tok_len - 1;
        /* Modes 1 and 3 reuse whole micro-batches only: llama.cpp does not keep
         * K/V bit-identical across micro-batch shapes, and a cold prompt
         * decodes full n_ubatch chunks from position 0, so resuming on a chunk
         * boundary reproduces those chunks. Mode 2 reuses every matched token. */
        if (g_tree_mode != 2) {
            int64_t ubatch = (int64_t)llama_n_ubatch(g_tree_ctx);
            if (ubatch > 1) reuse = reuse / ubatch * ubatch;
        }
        int owner = reuse > 0 ? slang_tree_pick_owner(node, reuse) : -1;
        if (owner >= 0) {
            int64_t held = g_tree_node[owner].start + g_tree_node[owner].n;
            if (reuse > held) reuse = held;   /* an ancestor owner holds fewer cells */
        }
        if (owner >= 0 && g_tree_mode != 2 && reuse > g_tree_node[owner].exact_upto) {
            int64_t ub = (int64_t)llama_n_ubatch(g_tree_ctx);
            reuse = g_tree_node[owner].exact_upto;
            if (ub > 1) reuse = reuse / ub * ub;
            if (reuse <= 0) owner = -1;
        }
        if (owner >= 0) {
            llama_memory_t memory = llama_get_memory(g_tree_ctx);
            /* Per-sequence streams (mode 3) only copy whole sequences, and a copy
             * would carry the owner's tail as stale cells: restore the prefix
             * through the host instead. Unified KV just adds the seq id to cells. */
            if (g_tree_mode == 3) {
                slang_tree_restore_prefix_host(g_tree_node[owner].seq, seq, reuse);
            } else {
                llama_memory_seq_cp(memory, g_tree_node[owner].seq, seq, 0, (llama_pos)reuse);
            }
            if (slang_tree_kv_holds(seq, reuse)) {
                g_tree_node[owner].pins++;
                g_tree_node[owner].last_used = ++g_prefix_clock;
                request->tree_owner = owner;
            } else {
                llama_memory_seq_rm(memory, seq, -1, -1);
                slang_tree_zero_stream(seq);   /* the failed restore left cells behind */
                g_prefix_restore_failures++;
                reuse = 0;
            }
        } else {
            reuse = 0;
        }
    }
    if (!slang_tree_path_reserve(request, request->tok_len + 1)) {
        if (request->tree_owner >= 0 && g_tree_node[request->tree_owner].pins > 0)
            g_tree_node[request->tree_owner].pins--;
        request->tree_owner = -1;
        slang_tree_free_seq(seq);
        return SLANG_ERR_NO_CTX;
    }
    memcpy(request->path, request->tok, (size_t)reuse * sizeof(llama_token));
    request->path_len = reuse;
    request->seq = seq;
    request->eval_start = reuse;
    g_tree_active = handle;
    if (reuse > 0) {
        g_prefix_hits++;
        g_prefix_tokens_reused += reuse;
    } else {
        g_prefix_misses++;
    }
    return reuse;
}

/* One decode of n tokens at consecutive positions on the request's seq id,
 * logits only for the last. On "no KV slot" it evicts unpinned terminals and
 * retries. Runs outside the lock like every other decode. */
static int slang_tree_decode(struct slang_request *request, const llama_token *tok, int64_t n) {
    if (n <= 0) return 0;
    if (request->path_len + n > request->context_limit) return -1;
    if (!slang_tree_path_reserve(request, request->path_len + n)) return -1;
    struct llama_batch batch = llama_batch_init((int32_t)n, 0, 1);
    for (int64_t i = 0; i < n; i++) {
        batch.token[i] = tok[i];
        batch.pos[i] = (llama_pos)(request->path_len + i);
        batch.n_seq_id[i] = 1;
        batch.seq_id[i][0] = request->seq;
        batch.logits[i] = i == n - 1;
    }
    batch.n_tokens = (int32_t)n;
    int rc = llama_decode(request->ctx, batch);
    /* Unified KV shares one pool, so evicting another sequence can free a slot.
     * In mode 3 every sequence owns its stream: eviction frees nothing here and
     * would only wipe the cache, so fail fast. */
    while (rc == 1 && g_tree_mode != 3) {
        SLANG_LOCK();
        int evicted = slang_tree_evict_lru();
        SLANG_UNLOCK();
        if (!evicted) break;
        rc = llama_decode(request->ctx, batch);
    }
    llama_batch_free(batch);
    if (rc != 0) return -1;
    memcpy(request->path + request->path_len, tok, (size_t)n * sizeof(llama_token));
    request->path_len += n;
    return 0;
}

/* Tree-mode prefill: decodes only the suffix after the shared prefix. The last
 * prompt token is decoded alone, exactly as the snapshot lane does. */
/* The first decode a context ever runs must be one FULL micro-batch (see
 * slang_request_first_ubatch). The tree context is persistent, so the rule is
 * applied once to its first decode: a throwaway full micro-batch on this
 * request's own (still empty) sequence, then that sequence is cleared. */
static int slang_tree_warm_first(struct slang_request *request, int64_t suffix_len) {
    if (g_tree_warm) return 1;
    int64_t ub = (int64_t)llama_n_ubatch(request->ctx);
    if (suffix_len >= ub) return 1;   /* warm is recorded after the decode succeeds */
    if (!g_model_offloaded || ub <= 0 || ub >= request->context_limit ||
        request->eval_start != 0 || request->tok_len <= 0)
        return 1;
    struct llama_batch batch = llama_batch_init((int32_t)ub, 0, 1);
    for (int64_t i = 0; i < ub; i++) {
        batch.token[i] = request->tok[i % request->tok_len];
        batch.pos[i] = (llama_pos)i;
        batch.n_seq_id[i] = 1;
        batch.seq_id[i][0] = request->seq;
        batch.logits[i] = i == ub - 1;
    }
    batch.n_tokens = (int32_t)ub;
    int rc = llama_decode(request->ctx, batch);
    llama_batch_free(batch);
    llama_memory_seq_rm(llama_get_memory(request->ctx), request->seq, -1, -1);
    if (rc == 0) g_tree_warm = 1;
    return rc == 0;
}

static int64_t slang_tree_eval_prompt(struct slang_request *request) {
    if (request->tok_len > request->context_limit) return SLANG_ERR_OVERFLOW;
    if (request->seq < 0) {
        SLANG_LOCK();
        int64_t prepared = slang_tree_prepare_locked(request);
        SLANG_UNLOCK();
        if (prepared < 0) return prepared;
    }
    if (request->eval_start < 0 || request->eval_start > request->tok_len)
        return SLANG_ERR_DECODE;
    int64_t suffix_len = request->tok_len - request->eval_start;
    if (suffix_len > 0 && !slang_tree_warm_first(request, suffix_len - 1)) {
        slang_request_release_lease(request);
        return SLANG_ERR_DECODE;
    }
    if (suffix_len > 0) {
        int64_t head = suffix_len > 1 ? suffix_len - 1 : suffix_len;
        const llama_token *from = request->tok + request->eval_start;
        if (slang_tree_decode(request, from, head) != 0 ||
            (head < suffix_len &&
             slang_tree_decode(request, request->tok + request->tok_len - 1, 1) != 0)) {
            slang_request_release_lease(request);
            return SLANG_ERR_DECODE;
        }
        if (!g_tree_warm && suffix_len - 1 >= (int64_t)llama_n_ubatch(request->ctx)) g_tree_warm = 1;
    }
    SLANG_LOCK();
    if (suffix_len > 0) g_prefix_tokens_prefilled += suffix_len;
    SLANG_UNLOCK();
    request->eval_start = request->tok_len;
    request->legacy_logits_valid = 1;
    return request->tok_len;
}

/* Configures the prefix-cache mode: 0 = snapshot (default); 1 = radix tree over a
 * unified KV, reusing whole micro-batches; 2 = unified, reusing every matched
 * token; 3 = per-sequence KV streams (not unified), whole micro-batches. All tree
 * modes run on
 * one persistent multi-sequence context. cells is the unified KV size in
 * tokens (0 = 4 x the first request's n_ctx). The capacity bound is the
 * prefix-cache entry count (slang_ggml_prefix_cache_configure), at most
 * SLANG_TREE_MAX_SEQS - 1. Only while no request is open. */
int64_t slang_ggml_prefix_cache_mode_configure(int64_t mode, int64_t cells) {
    if (mode < 0 || mode > 3 || cells < 0 || cells > INT32_MAX)
        return SLANG_ERR_INVALID;
    SLANG_LOCK();
    int64_t result;
    if (g_request_count != 0) {
        result = SLANG_ERR_BUSY;
    } else {
        if (mode != g_tree_mode || cells != g_tree_cells_cfg) {
            slang_tree_destroy();
            if (mode != 0) slang_prefix_clear_all(0);
        }
        g_tree_mode = (int)mode;
        g_tree_cells_cfg = cells;
        result = mode;
    }
    SLANG_UNLOCK();
    return result;
}

/* Statistic getters read state the entry points mutate under g_state_lock. */
#define SLANG_LOCKED_GET(expr) do { SLANG_LOCK(); int64_t v_ = (int64_t)(expr); SLANG_UNLOCK(); return v_; } while (0)
int64_t slang_ggml_tree_mode(void) { SLANG_LOCKED_GET(g_tree_mode); }
int64_t slang_ggml_tree_n_ubatch(void) { SLANG_LOCKED_GET(g_tree_ctx ? llama_n_ubatch(g_tree_ctx) : 0); }
int64_t slang_ggml_tree_nodes(void) { SLANG_LOCKED_GET(slang_tree_node_count()); }
int64_t slang_ggml_tree_cached_tokens(void) { SLANG_LOCKED_GET(slang_tree_cached_tokens()); }
int64_t slang_ggml_tree_shared_tokens(void) { SLANG_LOCKED_GET(slang_tree_shared_tokens()); }

static int64_t slang_request_create_model_locked(struct llama_model *model, int64_t model_handle,
                                                 int64_t n_ctx, int physical_only) {
    if (model == NULL) return SLANG_ERR_NO_MODEL;
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
    /* The tree context is built on the default model; a model-handle request
     * always gets its own context. */
    int tree = g_tree_mode && !physical_only && model_handle == 0;
    if (tree) {
        if (g_tree_ctx == NULL) {
            int64_t cells = g_tree_cells_cfg > 0 ? g_tree_cells_cfg : n_ctx * 4;
            if (cells < n_ctx * 2) cells = n_ctx * 2;
            /* Mode 3 (not unified) splits n_ctx evenly over the sequences. */
            if (g_tree_mode == 3) cells = n_ctx * SLANG_TREE_MAX_SEQS;
            if (cells > INT32_MAX) return SLANG_ERR_INVALID;
            struct llama_context_params tp = llama_context_default_params();
            tp.n_ctx = (uint32_t)cells;
            tp.n_batch = (uint32_t)n_ctx;
            tp.n_seq_max = SLANG_TREE_MAX_SEQS;
            tp.kv_unified = g_tree_mode != 3;
            if (g_context_threads > 0) {
                tp.n_threads = g_context_threads;
                tp.n_threads_batch = g_context_threads;
            }
            g_tree_ctx = llama_init_from_model(g_model, tp);
            if (g_tree_ctx == NULL) return SLANG_ERR_NO_CTX;
            g_tree_limit = n_ctx;
            g_tree_cells = cells;
        } else if (n_ctx > g_tree_limit) {
            return SLANG_ERR_INVALID;
        }
        ctx = g_tree_ctx;
        smpl = llama_sampler_chain_init(llama_sampler_chain_default_params());
        greedy = llama_sampler_init_greedy();
    } else if (!physical_only) {
        struct llama_context_params cp = llama_context_default_params();
        cp.n_ctx = (uint32_t)n_ctx;
        cp.n_batch = cp.n_ctx;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
        if (g_matched_cpu_context) {
            cp.n_ubatch = cp.n_ctx;
            cp.n_seq_max = 1;
            cp.type_k = GGML_TYPE_F32;
            cp.type_v = GGML_TYPE_F32;
            cp.flash_attn_type = LLAMA_FLASH_ATTN_TYPE_DISABLED;
            cp.offload_kqv = false;
        }
        if (g_context_threads > 0) {
            cp.n_threads = g_context_threads;
            cp.n_threads_batch = g_context_threads;
        }
#endif
        ctx = llama_init_from_model(model, cp);
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
        if (!tree) llama_free(ctx);
        free(str); free(out); free(tok);
        return SLANG_ERR_NO_CTX;
    }
    if (!physical_only) llama_sampler_chain_add(smpl, greedy);
    uint64_t generation = old->generation == 0 ? 1 : old->generation;
    memset(old, 0, sizeof(*old));
    old->ctx = ctx; old->smpl = smpl;
    old->str = str; old->out = out; old->tok = tok;
    old->eval_start = 0; old->selected_prefix = -1; old->lease_slot = -1;
    old->tree = tree; old->seq = -1; old->tree_owner = -1;
    old->physical_only = physical_only;
    old->context_limit = n_ctx;
    old->generation = generation; old->model_generation = g_model_generation;
    old->model = model; old->model_handle = model_handle;
    old->active = 1;
    g_request_count++;
    return slang_request_handle(slot, generation);
}

static int64_t slang_request_create_locked(int64_t n_ctx, int physical_only) {
    return slang_request_create_model_locked(g_model, 0, n_ctx, physical_only);
}

static int64_t slang_request_create_impl(int64_t n_ctx, int physical_only) {
    SLANG_LOCK();
    int64_t handle = slang_request_create_locked(n_ctx, physical_only);
    SLANG_UNLOCK();
    return handle;
}

int64_t slang_ggml_request_create(int64_t n_ctx) {
    return slang_request_create_impl(n_ctx > 0 ? n_ctx : 4096, 0);
}

int64_t slang_ggml_ctx_create(int64_t n_ctx) {
    SLANG_LOCK();
    int64_t result = SLANG_ERR_ALREADY;
    if (slang_compat_request() == NULL) {
        result = slang_request_create_locked(n_ctx > 0 ? n_ctx : 4096, 0);
        if (result >= 0) {
            g_compat_handle = result;
            result = 0;
        }
    }
    SLANG_UNLOCK();
    return result;
}

/* Capability bits are stable at the ABI boundary. Bit 0 is resident weights,
 * bit 1 is request isolation, bit 2 is serial exact-prefix restore, and bit 3
 * is bounded serial multi-entry prefix retention, and bit 4 is generation-
 * checked independent request ownership; independent requests may decode
 * concurrently, one thread per request handle (see g_state_lock). Bit 5 is
 * advertised only when this shim was compiled against the complete external
 * paged-request API. */
int64_t slang_ggml_capabilities(void) {
    return 1 | 2 | 4 | 8 | 16 | SLANG_CAP_MTMD | SLANG_CAP_BULK_IO | SLANG_CAP_MODEL_HANDLES |
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

static int64_t slang_prefix_cache_configure_locked(int64_t entries, int64_t bytes) {
    if (entries < 0 || entries > SLANG_PREFIX_CACHE_MAX_ENTRIES || bytes < 0)
        return SLANG_ERR_OVERFLOW;
    if ((uint64_t)bytes > (uint64_t)SIZE_MAX) return SLANG_ERR_OVERFLOW;
    if (g_tree_mode) {
        /* A running request decodes outside the lock on the sequences this
         * would seq_rm: refuse until it releases. */
        if (g_tree_active != 0) return SLANG_ERR_BUSY;
        /* Tree mode bounds terminals (one seq id each), not snapshot bytes. */
        g_prefix_capacity = entries;
        g_prefix_byte_limit = (size_t)bytes;
        slang_tree_evict_to(slang_tree_capacity());
        return g_prefix_capacity;
    }
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

int64_t slang_ggml_prefix_cache_configure(int64_t entries, int64_t bytes) {
    SLANG_LOCK();
    int64_t result = slang_prefix_cache_configure_locked(entries, bytes);
    SLANG_UNLOCK();
    return result;
}

static void slang_request_release_lease_locked(struct slang_request *request) {
    if (request->tree) { slang_tree_release_locked(request); return; }
    if (request->lease_slot < 0) return;
    struct slang_prefix_entry *entry = &g_prefix[request->lease_slot];
    if (entry->pins > 0) entry->pins--;
    int64_t slot = request->lease_slot;
    request->lease_slot = -1;
    request->selected_prefix = -1;
    if (entry->unavailable && entry->pins == 0) slang_prefix_drop(slot, 0);
}

static void slang_request_release_lease(struct slang_request *request) {
    SLANG_LOCK();
    slang_request_release_lease_locked(request);
    SLANG_UNLOCK();
}

static int64_t slang_request_close_locked(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    slang_physical_request_detach(handle);
#endif
    slang_request_release_lease_locked(request);
    struct slang_model_slot *model_slot = slang_model_slot_get(request->model_handle);
    if (model_slot != NULL && model_slot->requests > 0) model_slot->requests--;
    if (request->smpl) llama_sampler_free(request->smpl);
    if (request->ctx && !request->tree) llama_free(request->ctx);
    free(request->str); free(request->out); free(request->tok);
    free(request->path);
    uint64_t next_generation = request->generation < SLANG_REQUEST_MAX_GENERATION
        ? request->generation + 1 : SLANG_REQUEST_MAX_GENERATION;
    memset(request, 0, sizeof(*request));
    request->generation = next_generation;
    request->selected_prefix = -1;
    request->lease_slot = -1;
    request->seq = -1; request->tree_owner = -1;
    if (g_request_count > 0) g_request_count--;
    if (g_compat_handle == handle) g_compat_handle = 0;
    return 0;
}

int64_t slang_ggml_request_close(int64_t handle) {
    SLANG_LOCK();
    int64_t result = slang_request_close_locked(handle);
    SLANG_UNLOCK();
    return result;
}

int64_t slang_ggml_request_cancel(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    request->cancelled = 1;
    return slang_ggml_request_close(handle);
}

/* Frees in reverse construction order and resets every handle, so a caller
 * that stops and restarts a model in one process leaks nothing. */
static int64_t slang_free_locked(void) {
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    if (g_physical_pool.active) return SLANG_ERR_BUSY;
#endif
    int compat_active = slang_compat_request() != NULL;
    if (g_request_count > (compat_active ? 1 : 0)) return SLANG_ERR_BUSY;
    if (compat_active) slang_request_close_locked(g_compat_handle);
    slang_tree_destroy();
    g_tree_mode = 0; g_tree_cells_cfg = 0;
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

int64_t slang_ggml_free(void) {
    SLANG_LOCK();
    int64_t result = slang_free_locked();
    SLANG_UNLOCK();
    return result;
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
    if (request->model == NULL) return SLANG_ERR_NO_MODEL;
    request->embed_valid = 0;
    /* A reused tree request finishes its previous prompt before request->tok
     * is overwritten. */
    if (request->tree) slang_request_release_lease(request);
    const struct llama_vocab *vocab = llama_model_get_vocab(request->model);
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
    if (request->model == NULL) return SLANG_ERR_NO_MODEL;
    const struct llama_vocab *vocab = llama_model_get_vocab(request->model);
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
    /* The tree context is shared: its other sequences must survive. */
    if (!request->tree) llama_memory_clear(llama_get_memory(request->ctx), true);
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

/* True when sequence 0 of the request KV holds exactly positions 0..count-1.
 * A snapshot is only worth keeping, and a restore only worth trusting, when
 * the cells in the KV are the ones the token list says they are. */
static int slang_request_kv_holds(struct slang_request *request, int64_t count) {
    llama_memory_t memory = llama_get_memory(request->ctx);
    if (count <= 0) return llama_memory_seq_pos_max(memory, 0) < 0;
    return llama_memory_seq_pos_min(memory, 0) == 0 &&
           (int64_t)llama_memory_seq_pos_max(memory, 0) == count - 1;
}

/* The first decode a context ever runs must be one FULL micro-batch.
 *
 * Measured 2026-11-12 on llama.cpp b10794, CUDA (GB10), Qwen3-Coder-30B-A3B
 * Q4_K_M, n_ubatch 512: a fresh context whose first micro-batch has certain
 * sizes below n_ubatch (2 of the 206 sizes tried) aborts the process inside
 * llama_decode with "CUDA error: an illegal memory access" (Xid 31, FAULT_PDE
 * VIRT_READ), with or without a prefix restore. The same sizes are harmless
 * once the context has run a full micro-batch. A cold agent prompt is longer
 * than n_ubatch, so its first micro-batch is always full; a prefix restore is
 * what leaves a short suffix as a context's first decode, which is why the
 * abort showed up right after a restore.
 *
 * This is a workaround for a fault below this shim, not a repair of it. A
 * prompt shorter than one micro-batch gets a throwaway full micro-batch first
 * (here), and a restore gives reuse back until its suffix is a full
 * micro-batch (slang_request_prefix_prepare_locked). Returns 0 when the
 * throwaway decode fails; the caller then fails the request, never the
 * process.
 *
 * The rule costs up to one micro-batch of decode, so it applies only where the
 * fault was seen: a context that has not yet run a full micro-batch, on a
 * model with layers offloaded, whose micro-batch is smaller than its context
 * (the matched-CPU profile sets n_ubatch = n_ctx). */
static int64_t slang_request_first_ubatch(struct slang_request *request) {
    if (request->warm || request->tree || !slang_request_offloaded(request)) return 0;
    int64_t ubatch = (int64_t)llama_n_ubatch(request->ctx);
    return ubatch > 0 && ubatch < request->context_limit ? ubatch : 0;
}

static int slang_request_warm(struct slang_request *request) {
    int64_t ubatch = slang_request_first_ubatch(request);
    if (ubatch == 0 || request->tok_len <= 0 || request->tok_len >= ubatch) return 1;
    llama_token *filler = (llama_token *)malloc((size_t)ubatch * sizeof(llama_token));
    if (filler == NULL) return 0;
    for (int64_t i = 0; i < ubatch; i++) filler[i] = request->tok[i % request->tok_len];
    llama_memory_clear(llama_get_memory(request->ctx), true);
    int decoded = llama_decode(request->ctx, llama_batch_get_one(filler, (int32_t)ubatch)) == 0;
    free(filler);
    llama_memory_clear(llama_get_memory(request->ctx), true);
    request->legacy_logits_valid = 0;
    if (decoded) request->warm = 1;
    return decoded;
}

/* Selects the longest cacheable prefix owned by this serial context. The
 * snapshot is restored only after exact token comparison, only into a request
 * of the same model load and context size, and it is kept only if the KV then
 * holds exactly the reused positions. On any doubt the snapshot is dropped and
 * the whole prompt is prefilled again. At least one trailing token is
 * recomputed so the backend produces fresh boundary logits. */
static int64_t slang_request_prefix_prepare_locked(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    int64_t guard = slang_request_decodable(request);
    if (guard != 0) return guard;
    if (request->tree) return slang_tree_prepare_locked(request);
    slang_request_release_lease_locked(request);
    request->eval_start = 0;
    request->selected_prefix = -1;
    /* Snapshots are keyed by the default model's load generation, so a
     * request on a model handle never restores or admits one. */
    if (request->model_handle != 0) {
        llama_memory_clear(llama_get_memory(request->ctx), true);
        return 0;
    }
    for (int64_t i = 0; i < SLANG_PREFIX_CACHE_MAX_ENTRIES; i++) {
        struct slang_prefix_entry *entry = &g_prefix[i];
        if (entry->state == NULL || entry->unavailable || entry->token_count <= 1 ||
            request->tok_len < entry->token_count) continue;
        if (entry->model_generation != request->model_generation ||
            entry->context_limit != request->context_limit) continue;
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
            int64_t reuse = entry->token_count - 1;
            int64_t ubatch = slang_request_first_ubatch(request);
            /* See slang_request_warm: a context that has never decoded must
             * start with a full micro-batch, so give some reuse back. */
            if (ubatch > 0 && request->tok_len >= ubatch &&
                request->tok_len - reuse < ubatch)
                reuse = request->tok_len - ubatch;
            if (reuse > 0 &&
                llama_memory_seq_rm(llama_get_memory(request->ctx), 0,
                                    (llama_pos)reuse, -1) &&
                slang_request_kv_holds(request, reuse)) {
                request->eval_start = reuse;
                entry->last_used = ++g_prefix_clock;
                g_prefix_hits++;
                g_prefix_tokens_reused += request->eval_start;
                return request->eval_start;
            }
            if (reuse <= 0) {
                slang_request_release_lease_locked(request);
                llama_memory_clear(llama_get_memory(request->ctx), true);
                g_prefix_misses++;
                return 0;
            }
        }
        g_prefix_restore_failures++;
        entry->unavailable = 1;
        slang_request_release_lease_locked(request);
    }
    llama_memory_clear(llama_get_memory(request->ctx), true);
    g_prefix_misses++;
    return 0;
}

int64_t slang_ggml_request_prefix_prepare(int64_t handle) {
    /* The warm-up decodes, so it runs before the lock is taken, like every
     * other decode. The KV is cleared again on both paths below. */
    struct slang_request *request = slang_request_get(handle);
    if (request != NULL && request->ctx != NULL && !request->cancelled &&
        !slang_request_warm(request))
        return SLANG_ERR_DECODE;
    SLANG_LOCK();
    int64_t result = slang_request_prefix_prepare_locked(handle);
    SLANG_UNLOCK();
    return result;
}

int64_t slang_ggml_prefix_prepare(void) {
    return slang_ggml_request_prefix_prepare(g_compat_handle);
}

int64_t slang_ggml_prefix_hits(void) { SLANG_LOCKED_GET(g_prefix_hits); }
int64_t slang_ggml_prefix_misses(void) { SLANG_LOCKED_GET(g_prefix_misses); }
int64_t slang_ggml_prefix_tokens_reused(void) { SLANG_LOCKED_GET(g_prefix_tokens_reused); }
int64_t slang_ggml_prefix_tokens_prefilled(void) { SLANG_LOCKED_GET(g_prefix_tokens_prefilled); }
int64_t slang_ggml_prefix_admissions(void) { SLANG_LOCKED_GET(g_prefix_admissions); }
int64_t slang_ggml_prefix_evictions(void) { SLANG_LOCKED_GET(g_prefix_evictions); }
int64_t slang_ggml_prefix_resident_entries(void) {
    SLANG_LOCKED_GET(g_tree_mode ? slang_tree_terminals() : g_prefix_resident_entries);
}
int64_t slang_ggml_prefix_resident_bytes(void) { SLANG_LOCKED_GET(g_prefix_resident_bytes); }
int64_t slang_ggml_prefix_rejected_bytes(void) { SLANG_LOCKED_GET(g_prefix_rejected_bytes); }
int64_t slang_ggml_prefix_restore_failures(void) { SLANG_LOCKED_GET(g_prefix_restore_failures); }

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
    if (request->model_handle != 0) return;
    if (g_prefix_capacity == 0 || g_prefix_byte_limit == 0) return;
    int64_t exact = slang_prefix_exact_slot(request);
    if (exact >= 0) {
        g_prefix[exact].last_used = ++g_prefix_clock;
        return;
    }
    if (request->tok_len <= 0 || !slang_request_kv_holds(request, request->tok_len)) return;
    size_t state_size = llama_state_seq_get_size(request->ctx, 0);
    if (state_size == 0) return;
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
    g_prefix[slot].model_generation = request->model_generation;
    g_prefix[slot].context_limit = request->context_limit;
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
    int64_t guard = slang_request_decodable(request);
    if (guard != 0) return guard;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
    request->legacy_logits_valid = 0;
    if (request->tok_len == 0) return SLANG_ERR_TOKENIZE;
    if (request->tree) return slang_tree_eval_prompt(request);
    if (request->eval_start < 0 || request->eval_start > request->tok_len)
        return SLANG_ERR_DECODE;
    int64_t suffix_len = request->tok_len - request->eval_start;
    /* A caller that skipped prefix_prepare still gets the full first
     * micro-batch, as long as the KV is empty and so safe to clear. */
    if (request->eval_start == 0 && slang_request_kv_holds(request, 0) &&
        !slang_request_warm(request)) {
        slang_request_release_lease(request);
        return SLANG_ERR_DECODE;
    }
    if (suffix_len > 0) {
        /* The last prompt token is always decoded alone, on the cold path and
         * the prefix-hit path alike, so its logits come from one batch shape
         * (doc/08_tracking/bug/slang_prefix_cache_hit_output_drift_2026-11-14.md).
         * Skipped while the first-micro-batch workaround needs a full batch. */
        int64_t head = suffix_len > 1 && slang_request_first_ubatch(request) == 0
                           ? suffix_len - 1 : suffix_len;
        struct llama_batch batch = llama_batch_get_one(
            request->tok + request->eval_start, (int32_t)head);
        if (llama_decode(request->ctx, batch) != 0) {
            slang_request_release_lease(request);
            return SLANG_ERR_DECODE;
        }
        if (head < suffix_len) {
            struct llama_batch last = llama_batch_get_one(
                request->tok + request->tok_len - 1, 1);
            if (llama_decode(request->ctx, last) != 0) {
                slang_request_release_lease(request);
                return SLANG_ERR_DECODE;
            }
        }
        if (suffix_len >= (int64_t)llama_n_ubatch(request->ctx)) request->warm = 1;
    }
    SLANG_LOCK();
    if (suffix_len > 0) g_prefix_tokens_prefilled += suffix_len;
    slang_prefix_admit(request);
    SLANG_UNLOCK();
    request->eval_start = request->tok_len;
    request->legacy_logits_valid = 1;
    return request->tok_len;
}

int64_t slang_ggml_eval_prompt(void) {
    int64_t result = slang_ggml_request_eval_prompt(g_compat_handle);
    struct slang_request *request = slang_compat_request();
    /* A tree request keeps its sequence until generation ends. */
    if (result >= 0 && request != NULL && !request->tree) slang_request_release_lease(request);
    return result;
}

/* One decode step. slang's worker calls this in its own loop, which is what
 * keeps the generation loop on the Simple side of the boundary. */
int64_t slang_ggml_request_eval(int64_t handle, int64_t token) {
    struct slang_request *request = slang_request_get(handle);
    int64_t guard = slang_request_decodable(request);
    if (guard != 0) return guard;
#if SLANG_HAS_EXTERNAL_PAGED_PROVIDER
    request->paged_logits_valid = 0;
#endif
    request->legacy_logits_valid = 0;
    llama_token t = (llama_token)token;
    if (request->tree) {
        if (request->seq < 0 || slang_tree_decode(request, &t, 1) != 0) {
            slang_request_release_lease(request);
            return SLANG_ERR_DECODE;
        }
        request->legacy_logits_valid = 1;
        return 0;
    }
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
    if (request == NULL || request->model == NULL) return SLANG_ERR_INVALID;
    int64_t count = (int64_t)llama_vocab_n_tokens(llama_model_get_vocab(request->model));
    if (index < 0 || index >= count) return SLANG_ERR_INVALID;
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
    if (g_context_threads > 0) {
        cp.n_threads = g_context_threads;
        cp.n_threads_batch = g_context_threads;
    }

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

/* ===== mtmd group =====
 * Multimodal input (image / audio) through llama.cpp's libmtmd. Everything
 * below is compiled only with -DSLANG_WITH_MTMD, so the default build without
 * libmtmd is unchanged. int64-only ABI; media bytes arrive through
 * spl_wffi_call_i64_with_bytes as (ptr, len) and are decoded here before the
 * call returns, so no pointer outlives it. The shim never opens a host file.
 *
 * Decoding is the encoded-bytes boundary (stb_image / miniaudio inside
 * libmtmd), reached only after a magic-byte sniff admits the container. Video
 * containers are refused by the sniff, so the helper's ffmpeg/ffprobe
 * subprocess path is unreachable from client bytes.
 *
 * A media request bypasses the prefix cache entirely: it never calls
 * slang_request_prefix_prepare_locked or slang_prefix_admit, and clears its KV
 * before the multimodal prefill. */
#ifdef SLANG_WITH_MTMD
#include "mtmd.h"
#include "mtmd-helper.h"

#define SLANG_MM_MAX_BITMAPS 16
#define SLANG_MM_MAX_BYTES ((int64_t)256 * 1024 * 1024)
#define SLANG_ERR_MM_MARKERS   (-12)
#define SLANG_ERR_MM_PREPROC   (-13)
#define SLANG_ERR_MM_FORMAT    (-14)

/* mtmd_helper_eval_chunks is NOT thread-safe on the shared mtmd_context, and the
 * context's encoder state is shared by every request: this lock is the one
 * documented exception to lockless-by-default, held only around the encode and
 * decode of a media prefill. */
#if defined(_WIN32)
static SRWLOCK g_mm_lock = SRWLOCK_INIT;
#  define SLANG_MM_LOCK()   AcquireSRWLockExclusive(&g_mm_lock)
#  define SLANG_MM_UNLOCK() ReleaseSRWLockExclusive(&g_mm_lock)
#else
static pthread_mutex_t g_mm_lock = PTHREAD_MUTEX_INITIALIZER;
#  define SLANG_MM_LOCK()   pthread_mutex_lock(&g_mm_lock)
#  define SLANG_MM_UNLOCK() pthread_mutex_unlock(&g_mm_lock)
#endif

struct slang_mm_slot {
    uint64_t generation;               /* request generation this slot belongs to */
    mtmd_bitmap *bitmaps[SLANG_MM_MAX_BITMAPS];
    int64_t n_bitmaps;
    mtmd_input_chunks *chunks;
};

static mtmd_context *g_mm_ctx = NULL;
static struct slang_mm_slot g_mm_slots[SLANG_REQUEST_MAX_ENTRIES];

static void slang_mm_slot_clear(struct slang_mm_slot *slot) {
    for (int64_t i = 0; i < slot->n_bitmaps; i++) mtmd_bitmap_free(slot->bitmaps[i]);
    if (slot->chunks != NULL) mtmd_input_chunks_free(slot->chunks);
    memset(slot, 0, sizeof(*slot));
}

/* The slot of a live request. A slot left behind by a request that closed
 * without mm_reset belongs to an older generation and is freed here, so a
 * recycled request slot never inherits another request's media. */
static struct slang_mm_slot *slang_mm_slot_for(struct slang_request *request) {
    struct slang_mm_slot *slot = &g_mm_slots[(int64_t)(request - g_requests)];
    if (slot->generation != request->generation) {
        slang_mm_slot_clear(slot);
        slot->generation = request->generation;
    }
    return slot;
}

static int slang_mm_sniff_ok(const uint8_t *b, int64_t n) {
    if (n < 12) return 0;
    if (b[0] == 0xFF && b[1] == 0xD8 && b[2] == 0xFF) return 1;                 /* jpeg */
    if (memcmp(b, "\x89PNG\r\n\x1a\n", 8) == 0) return 1;                       /* png */
    if (memcmp(b, "GIF8", 4) == 0 || (b[0] == 'B' && b[1] == 'M')) return 1;    /* gif, bmp */
    if (memcmp(b, "RIFF", 4) == 0 && memcmp(b + 8, "WAVE", 4) == 0) return 1;   /* wav */
    if (memcmp(b, "ID3", 3) == 0 || memcmp(b, "fLaC", 4) == 0) return 1;        /* mp3, flac */
    if (b[0] == 0xFF && (b[1] & 0xE0) == 0xE0) return 1;                        /* mp3 frame */
    return 0;
}

/* Loads the projector whose path is in the string buffer (the compat request's
 * when one is open, else the load buffer). Returns the capability mask
 * (1 = vision, 2 = audio) or a negative error. */
int64_t slang_ggml_mm_load(void) {
    SLANG_LOCK();
    int64_t result;
    struct slang_request *compat = slang_compat_request();
    const char *path = compat != NULL ? compat->str : g_load_str;
    if (g_model == NULL) {
        result = SLANG_ERR_NO_MODEL;
    } else if (g_mm_ctx != NULL) {
        result = SLANG_ERR_ALREADY;
    } else if (path[0] == '\0') {
        result = SLANG_ERR_LOAD_FAILED;
    } else {
        struct mtmd_context_params params = mtmd_context_params_default();
        params.media_marker = mtmd_default_marker();
        params.print_timings = false;
        if (g_context_threads > 0) params.n_threads = g_context_threads;
        g_mm_ctx = mtmd_init_from_file(path, g_model, params);
        if (g_mm_ctx == NULL) {
            result = SLANG_ERR_LOAD_FAILED;
        } else {
            result = (mtmd_support_vision(g_mm_ctx) ? 1 : 0) | (mtmd_support_audio(g_mm_ctx) ? 2 : 0);
        }
    }
    SLANG_UNLOCK();
    return result;
}

int64_t slang_ggml_mm_caps(void) {
    if (g_mm_ctx == NULL) return 0;
    return (mtmd_support_vision(g_mm_ctx) ? 1 : 0) | (mtmd_support_audio(g_mm_ctx) ? 2 : 0);
}

/* Must run before slang_ggml_free releases the model the projector was built on. */
int64_t slang_ggml_mm_free(void) {
    SLANG_MM_LOCK();
    SLANG_LOCK();
    for (int64_t i = 0; i < SLANG_REQUEST_MAX_ENTRIES; i++) slang_mm_slot_clear(&g_mm_slots[i]);
    if (g_mm_ctx != NULL) { mtmd_free(g_mm_ctx); g_mm_ctx = NULL; }
    SLANG_UNLOCK();
    SLANG_MM_UNLOCK();
    return 0;
}

int64_t slang_ggml_request_mm_reset(int64_t handle) {
    SLANG_LOCK();
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) { SLANG_UNLOCK(); return SLANG_ERR_INVALID; }
    struct slang_mm_slot *slot = slang_mm_slot_for(request);
    slang_mm_slot_clear(slot);
    slot->generation = request->generation;
    SLANG_UNLOCK();
    return 0;
}

/* Adds one encoded image or audio file (the bytes arrive as ptr,len). Returns
 * the number of media items now pending (>= 1), or a negative error. */
int64_t slang_ggml_request_mm_add_encoded(int64_t handle, const uint8_t *buf, int64_t len) {
    if (g_mm_ctx == NULL) return SLANG_ERR_NO_MODEL;
    if (buf == NULL || len <= 0 || len > SLANG_MM_MAX_BYTES) return SLANG_ERR_INVALID;
    if (!slang_mm_sniff_ok(buf, len)) return SLANG_ERR_MM_FORMAT;
    SLANG_LOCK();
    struct slang_request *request = slang_request_get(handle);
    struct slang_mm_slot *slot = request == NULL ? NULL : slang_mm_slot_for(request);
    int64_t result = SLANG_ERR_INVALID;
    if (slot != NULL && slot->n_bitmaps >= SLANG_MM_MAX_BITMAPS) {
        result = SLANG_ERR_OVERFLOW;
    } else if (slot != NULL) {
        struct mtmd_helper_bitmap_wrapper w = mtmd_helper_bitmap_init_from_buf(
            g_mm_ctx, buf, (size_t)len, false, mtmd_helper_init_opt_default());
        if (w.video_ctx != NULL) {
            mtmd_helper_video_free(w.video_ctx);
            if (w.bitmap != NULL) mtmd_bitmap_free(w.bitmap);
            result = SLANG_ERR_MM_FORMAT;
        } else if (w.bitmap == NULL) {
            result = SLANG_ERR_MM_PREPROC;
        } else {
            slot->bitmaps[slot->n_bitmaps++] = w.bitmap;
            result = slot->n_bitmaps;
        }
    }
    SLANG_UNLOCK();
    return result;
}

/* Tokenizes the request string buffer (the rendered prompt, holding one marker
 * per pending media item) together with the pending media. Returns the number
 * of KV positions the prompt consumes, -12 when marker and media counts differ,
 * -13 when media preprocessing failed. */
int64_t slang_ggml_request_mm_tokenize(int64_t handle) {
    SLANG_LOCK();
    struct slang_request *request = slang_request_get(handle);
    int64_t result;
    if (request == NULL) {
        result = SLANG_ERR_INVALID;
    } else if (g_mm_ctx == NULL) {
        result = SLANG_ERR_NO_MODEL;
    } else {
        struct slang_mm_slot *slot = slang_mm_slot_for(request);
        if (slot->chunks != NULL) { mtmd_input_chunks_free(slot->chunks); slot->chunks = NULL; }
        slot->chunks = mtmd_input_chunks_init();
        struct mtmd_input_text text;
        text.text = request->str;
        text.text_len = (size_t)request->str_len;
        text.add_special = true;
        text.parse_special = true;
        int32_t rc = mtmd_tokenize(g_mm_ctx, slot->chunks, &text,
                                   (const mtmd_bitmap *const *)slot->bitmaps,
                                   (size_t)slot->n_bitmaps);
        if (rc == 1) result = SLANG_ERR_MM_MARKERS;
        else if (rc != 0) result = SLANG_ERR_MM_PREPROC;
        else result = (int64_t)mtmd_helper_get_n_pos(slot->chunks);
        if (result < 0) { mtmd_input_chunks_free(slot->chunks); slot->chunks = NULL; }
    }
    SLANG_UNLOCK();
    return result;
}

/* Multimodal prefill: clears the KV (no prefix reuse, no admission), encodes the
 * media and decodes every chunk, leaving logits for the last token. Returns the
 * new position count. Decoding runs outside the state lock like every other
 * decode; the mm lock serialises use of the shared mtmd_context. */
int64_t slang_ggml_request_mm_eval_prompt(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    if (request->ctx == NULL || g_mm_ctx == NULL || request->tree) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    struct slang_mm_slot *slot = &g_mm_slots[(int64_t)(request - g_requests)];
    if (slot->generation != request->generation || slot->chunks == NULL) return SLANG_ERR_INVALID;
    slang_request_release_lease(request);
    request->legacy_logits_valid = 0;
    request->eval_start = 0;
    llama_memory_clear(llama_get_memory(request->ctx), true);
    llama_pos new_n_past = 0;
    SLANG_MM_LOCK();
    int32_t rc = mtmd_helper_eval_chunks(g_mm_ctx, request->ctx, slot->chunks, 0, 0,
                                         (int32_t)llama_n_batch(request->ctx), true,
                                         &new_n_past);
    SLANG_MM_UNLOCK();
    SLANG_LOCK();
    slang_mm_slot_clear(slot);
    slot->generation = request->generation;
    SLANG_UNLOCK();
    if (rc != 0) return SLANG_ERR_DECODE;
    request->legacy_logits_valid = 1;
    return (int64_t)new_n_past;
}
#endif /* SLANG_WITH_MTMD */
/* ===== end mtmd group ===== */

/* ---- bulk byte I/O (capability bit 256) -------------------------------
 *
 * One call per buffer instead of one per byte. The Simple side passes bytes
 * IN with spl_wffi_call_i64_with_bytes (callee gets ptr, len) and reads them
 * OUT with spl_wffi_call_i64_into_bytes (callee gets buf, cap, out_len). An
 * out call always reports the size it needs in *out_len; when cap is smaller
 * it copies nothing and returns SLANG_ERR_OVERFLOW, so cap 0 is a size probe. */

static int64_t slang_append_bytes(char *dst, int64_t *len, const uint8_t *src, int64_t n) {
    if (n < 0 || (n > 0 && src == NULL)) return SLANG_ERR_INVALID;
    if (n > SLANG_STR_CAP - 1 - *len) return SLANG_ERR_OVERFLOW;
    if (n > 0) memcpy(dst + *len, src, (size_t)n);
    *len += n;
    dst[*len] = '\0';
    return *len;
}

static int64_t slang_copy_out(const void *src, int64_t n, uint8_t *buf, int64_t cap, int64_t *out_len) {
    if (out_len != NULL) *out_len = n;
    if (cap < n) return SLANG_ERR_OVERFLOW;
    if (n > 0) {
        if (buf == NULL) return SLANG_ERR_INVALID;
        memcpy(buf, src, (size_t)n);
    }
    return 0;
}

int64_t slang_ggml_request_str_push_bytes(int64_t handle, const uint8_t *ptr, int64_t len) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    return slang_append_bytes(request->str, &request->str_len, ptr, len);
}

/* Same routing as slang_ggml_str_push: the compat request when one exists,
 * else the load-path buffer (a model path is pushed before any context). */
int64_t slang_ggml_str_push_bytes(const uint8_t *ptr, int64_t len) {
    if (slang_compat_request() != NULL)
        return slang_ggml_request_str_push_bytes(g_compat_handle, ptr, len);
    return slang_append_bytes(g_load_str, &g_load_str_len, ptr, len);
}

int64_t slang_ggml_request_out_into(int64_t handle, uint8_t *buf, int64_t cap, int64_t *out_len) {
    if (out_len != NULL) *out_len = 0;
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL) return SLANG_ERR_INVALID;
    return slang_copy_out(request->out, request->out_len, buf, cap, out_len);
}

int64_t slang_ggml_out_into(uint8_t *buf, int64_t cap, int64_t *out_len) {
    return slang_ggml_request_out_into(g_compat_handle, buf, cap, out_len);
}

/* ---- model handles (capability bit 512) --------------------------------
 *
 * slang_ggml_model_load keeps owning the default model (handle 0). These load
 * further models beside it. Opening a path that is already open returns the
 * same handle: a server thread that starts from a stale module snapshot then
 * finds the resident model instead of loading a second copy. */

int64_t slang_ggml_model_open(const uint8_t *path, int64_t len, int64_t n_gpu_layers) {
    if (path == NULL || len <= 0 || len >= SLANG_STR_CAP) return SLANG_ERR_INVALID;
    char *owned = (char *)malloc((size_t)len + 1);
    if (owned == NULL) return SLANG_ERR_LOAD_FAILED;
    memcpy(owned, path, (size_t)len);
    owned[len] = '\0';
    SLANG_LOCK();
    int64_t result = SLANG_ERR_BUSY;
    int64_t free_slot = -1;
    for (int64_t i = 0; i < SLANG_MODEL_MAX_HANDLES; i++) {
        struct slang_model_slot *slot = &g_model_slots[i];
        if (slot->model != NULL && strcmp(slot->path, owned) == 0) {
            result = (int64_t)(slot->generation * SLANG_MODEL_MAX_HANDLES + (uint64_t)i + 1);
            slot->opens++;
            free_slot = -2;
            break;
        }
        if (slot->model == NULL && free_slot == -1) free_slot = i;
    }
    if (free_slot >= 0) {
        if (g_model_slot_generation >= SLANG_MODEL_MAX_GENERATION) {
            result = SLANG_ERR_EXHAUSTED;
        } else {
            struct llama_model_params mp = llama_model_default_params();
            mp.n_gpu_layers = (n_gpu_layers < 0) ? 999 : (int32_t)n_gpu_layers;
            struct llama_model *model = llama_model_load_from_file(owned, mp);
            if (model == NULL) {
                result = SLANG_ERR_LOAD_FAILED;
            } else {
                struct slang_model_slot *slot = &g_model_slots[free_slot];
                slot->model = model;
                slot->path = owned;
                owned = NULL;
                slot->generation = ++g_model_slot_generation;
                slot->requests = 0;
                slot->opens = 1;
                slot->offloaded = mp.n_gpu_layers != 0 && llama_supports_gpu_offload();
                result = (int64_t)(slot->generation * SLANG_MODEL_MAX_HANDLES + (uint64_t)free_slot + 1);
            }
        }
    }
    SLANG_UNLOCK();
    free(owned);
    return result;
}

/* Gives back one owner's hold. While other owners hold the model it stays
 * loaded and the close succeeds; the last owner's close frees it, and is
 * refused with SLANG_ERR_BUSY while a request built on the model is open. */
int64_t slang_ggml_model_close(int64_t handle) {
    SLANG_LOCK();
    int64_t result = SLANG_ERR_INVALID;
    struct slang_model_slot *slot = slang_model_slot_get(handle);
    if (slot != NULL) {
        if (slot->opens > 1) {
            slot->opens--;
            result = 0;
        } else if (slot->requests > 0) {
            result = SLANG_ERR_BUSY;
        } else {
            llama_model_free(slot->model);
            free(slot->path);
            slot->opens = 0;
            slot->model = NULL;
            slot->path = NULL;
            result = 0;
        }
    }
    SLANG_UNLOCK();
    return result;
}

/* A request on model `handle`; handle 0 is the default model, exactly
 * slang_ggml_request_create. Every request_* entry then works on it. */
int64_t slang_ggml_request_create_for(int64_t handle, int64_t n_ctx) {
    if (handle == 0) return slang_ggml_request_create(n_ctx);
    SLANG_LOCK();
    int64_t result = SLANG_ERR_INVALID;
    struct slang_model_slot *slot = slang_model_slot_get(handle);
    if (slot != NULL) {
        result = slang_request_create_model_locked(slot->model, handle, n_ctx > 0 ? n_ctx : 4096, 0);
        if (result > 0) slot->requests++;
    }
    SLANG_UNLOCK();
    return result;
}

/* ---- embeddings and rerank (capability bit 512) ------------------------
 *
 * request_embed_configure rebuilds the request's context with embeddings on
 * and the given pooling (-1 the model's own, else enum llama_pooling_type:
 * 0 none, 1 mean, 2 cls, 3 last, 4 rank). n_batch = n_ubatch = n_ctx because
 * non-causal attention needs the whole sequence in one micro-batch. Returns
 * the pooling the context really uses. */
int64_t slang_ggml_request_embed_configure(int64_t handle, int64_t pooling) {
    if (pooling < -1 || pooling > 4) return SLANG_ERR_INVALID;
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->ctx == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    /* A tree request shares the persistent tree context; it is never rebuilt. */
    if (request->tree) return SLANG_ERR_INVALID;
    struct llama_context_params cp = llama_context_default_params();
    cp.n_ctx = (uint32_t)request->context_limit;
    cp.n_batch = cp.n_ctx;
    cp.n_ubatch = cp.n_ctx;
    cp.embeddings = true;
    cp.pooling_type = (enum llama_pooling_type)pooling;
    struct llama_context *ctx = llama_init_from_model(request->model, cp);
    if (ctx == NULL) return SLANG_ERR_NO_CTX;
    llama_free(request->ctx);
    request->ctx = ctx;
    request->embed_valid = 0;
    request->embed_tokens = 0;
    request->legacy_logits_valid = 0;
    return (int64_t)llama_pooling_type(ctx);
}

/* Runs the tokenized string buffer as ONE batch with every output on (the
 * pooled vector needs every position). Not eval_prompt: that decodes the last
 * token separately and may decode a warm-up filler, which would corrupt a
 * pooled result. Refuses more tokens than the model was trained on: an
 * absolute-position encoder (BERT) has no embedding past n_ctx_train, and a
 * vocoder longer than that is out of its trained range too.
 *
 * llama_decode, not llama_encode: at llama.cpp 99b9548, decode on a context
 * with no memory (every encoder-only arch, BERT and WavTokenizer-dec alike)
 * forwards to encode() itself (llama-context.cpp `llama_context::decode`),
 * and llama_model_has_encoder is true only for T5/T5ENCODER/EAGLE3/DFLASH, so
 * switching on it would still pick decode for those models. */
int64_t slang_ggml_request_embed_eval(int64_t handle) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->ctx == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    /* A tree request decodes on the shared tree context: clearing its memory
     * here would drop every other request's cached sequences. */
    if (request->tree) return SLANG_ERR_INVALID;
    request->embed_valid = 0;
    if (request->tok_len <= 0) return SLANG_ERR_TOKENIZE;
    int32_t trained = llama_model_n_ctx_train(request->model);
    if (request->tok_len > request->context_limit ||
        (trained > 0 && request->tok_len > (int64_t)trained))
        return SLANG_ERR_OVERFLOW;
    struct llama_batch batch = llama_batch_init((int32_t)request->tok_len, 0, 1);
    for (int64_t i = 0; i < request->tok_len; i++) {
        batch.token[i] = request->tok[i];
        batch.pos[i] = (llama_pos)i;
        batch.n_seq_id[i] = 1;
        batch.seq_id[i][0] = 0;
        batch.logits[i] = 1;
    }
    batch.n_tokens = (int32_t)request->tok_len;
    llama_memory_clear(llama_get_memory(request->ctx), true);
    int32_t rc = llama_decode(request->ctx, batch);
    llama_batch_free(batch);
    if (rc != 0) return SLANG_ERR_DECODE;
    request->embed_tokens = request->tok_len;
    request->embed_valid = 1;
    return request->tok_len;
}

/* Copies the last embed_eval result as float32 in host byte order (little-
 * endian on every supported target): pooling none gives tokens * n_embd_out
 * floats, rank gives n_cls_out scores, any other pooling n_embd_out. */
int64_t slang_ggml_request_embeddings_into(int64_t handle, uint8_t *buf, int64_t cap, int64_t *out_len) {
    if (out_len != NULL) *out_len = 0;
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->ctx == NULL) return SLANG_ERR_INVALID;
    if (!request->embed_valid) return SLANG_ERR_DECODE;
    enum llama_pooling_type pooling = llama_pooling_type(request->ctx);
    const float *values = NULL;
    int64_t count = 0;
    if (pooling == LLAMA_POOLING_TYPE_NONE) {
        values = llama_get_embeddings(request->ctx);
        count = request->embed_tokens * (int64_t)llama_model_n_embd_out(request->model);
    } else {
        values = llama_get_embeddings_seq(request->ctx, 0);
        count = pooling == LLAMA_POOLING_TYPE_RANK
            ? (int64_t)llama_model_n_cls_out(request->model)
            : (int64_t)llama_model_n_embd_out(request->model);
    }
    if (values == NULL || count <= 0) return SLANG_ERR_DECODE;
    return slang_copy_out(values, count * (int64_t)sizeof(float), buf, cap, out_len);
}

/* Appends the tokens of text[0..n) at request->tok[*at]. */
static int slang_tokenize_append(struct slang_request *request, const char *text, int64_t n,
                                 int parse_special) {
    int32_t got = llama_tokenize(llama_model_get_vocab(request->model), text, (int32_t)n,
                                 request->tok + request->tok_len,
                                 (int32_t)(SLANG_TOK_CAP - request->tok_len), false, parse_special != 0);
    if (got < 0) return 0;
    request->tok_len += got;
    return 1;
}

static int slang_token_append(struct slang_request *request, llama_token token) {
    if (request->tok_len >= SLANG_TOK_CAP) return 0;
    request->tok[request->tok_len++] = token;
    return 1;
}

/* Replaces every `key` in `tmpl` with value[0..n). Caller frees. */
static char *slang_replace_all(const char *tmpl, const char *key, const char *value, int64_t n) {
    size_t key_len = strlen(key), hits = 0;
    for (const char *p = strstr(tmpl, key); p != NULL; p = strstr(p + key_len, key)) hits++;
    size_t size = strlen(tmpl) + hits * (size_t)n + 1;
    char *out = (char *)malloc(size);
    if (out == NULL) return NULL;
    char *w = out;
    const char *r = tmpl;
    for (const char *p = strstr(r, key); p != NULL; p = strstr(r, key)) {
        memcpy(w, r, (size_t)(p - r)); w += p - r;
        memcpy(w, value, (size_t)n); w += n;
        r = p + key_len;
    }
    strcpy(w, r);
    return out;
}

/* Tokenizes a (query, document) pair for a rank-pooled model, exactly as
 * llama.cpp's server format_prompt_rerank does: the model's "rerank" chat
 * template when it has one, else [BOS] query [EOS] [SEP] doc [EOS] following
 * the vocab's add flags. The string buffer holds the query bytes followed by
 * the document bytes; query_len splits them. Returns the token count. */
int64_t slang_ggml_request_rerank_tokenize(int64_t handle, int64_t query_len) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->model == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    /* request->tok is the path a tree request's lease pins; only
     * request_tokenize releases that lease before overwriting it. */
    if (request->tree) return SLANG_ERR_INVALID;
    if (query_len < 0 || query_len > request->str_len) return SLANG_ERR_INVALID;
    request->embed_valid = 0;
    request->legacy_logits_valid = 0;
    request->tok_len = 0;
    const char *query = request->str;
    const char *doc = request->str + query_len;
    int64_t doc_len = request->str_len - query_len;
    const struct llama_vocab *vocab = llama_model_get_vocab(request->model);
    const char *tmpl = llama_model_chat_template(request->model, "rerank");
    int ok = 1;
    if (tmpl != NULL) {
        char *with_query = slang_replace_all(tmpl, "{query}", query, query_len);
        char *prompt = with_query == NULL ? NULL :
            slang_replace_all(with_query, "{document}", doc, doc_len);
        ok = prompt != NULL && slang_tokenize_append(request, prompt, (int64_t)strlen(prompt), 1);
        free(with_query);
        free(prompt);
    } else {
        llama_token eos = llama_vocab_eos(vocab);
        if (eos == LLAMA_TOKEN_NULL) eos = llama_vocab_sep(vocab);
        if (ok && llama_vocab_get_add_bos(vocab)) ok = slang_token_append(request, llama_vocab_bos(vocab));
        if (ok) ok = slang_tokenize_append(request, query, query_len, 0);
        if (ok && llama_vocab_get_add_eos(vocab)) ok = slang_token_append(request, eos);
        if (ok && llama_vocab_get_add_sep(vocab)) ok = slang_token_append(request, llama_vocab_sep(vocab));
        if (ok) ok = slang_tokenize_append(request, doc, doc_len, 0);
        if (ok && llama_vocab_get_add_eos(vocab)) ok = slang_token_append(request, eos);
    }
    if (!ok) {
        request->tok_len = 0;
        return SLANG_ERR_TOKENIZE;
    }
    return request->tok_len;
}

/* Replaces the request's token list with raw ids, int32 little-endian, for
 * input that is not text (a vocoder's audio codes). `len` is in bytes. The
 * ids are checked against the request model's vocabulary. Returns the count;
 * embed_eval or eval_prompt then runs them. */
int64_t slang_ggml_request_tokens_set(int64_t handle, const uint8_t *ptr, int64_t len) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->model == NULL) return SLANG_ERR_INVALID;
    if (request->cancelled) return SLANG_ERR_CANCELLED;
    if (request->tree) return SLANG_ERR_INVALID; /* as rerank_tokenize */
    if (len < 0 || (len % 4) != 0 || (len > 0 && ptr == NULL)) return SLANG_ERR_INVALID;
    int64_t count = len / 4;
    if (count > SLANG_TOK_CAP) return SLANG_ERR_OVERFLOW;
    int32_t vocab_size = llama_vocab_n_tokens(llama_model_get_vocab(request->model));
    for (int64_t i = 0; i < count; i++) {
        int32_t id;
        memcpy(&id, ptr + i * 4, sizeof(id));
        if (id < 0 || id >= vocab_size) return SLANG_ERR_INVALID;
    }
    if (count > 0) memcpy(request->tok, ptr, (size_t)len);
    request->tok_len = count;
    request->eval_start = 0;
    request->embed_valid = 0;
    request->legacy_logits_valid = 0;
    return count;
}

/* Replaces the request's sampler chain. temp_milli <= 0 keeps greedy (the
 * default every request starts with), with the repetition penalty in front
 * when it is not 1.0. Otherwise the chain is penalties -> top_k (if > 0) ->
 * top_p (if < 1000) -> temperature -> dist(seed); seed < 0 is a random seed.
 * Fractions are in thousandths so the ABI stays int64-only. */
int64_t slang_ggml_request_sampler_configure(int64_t handle, int64_t temp_milli, int64_t top_k,
                                             int64_t top_p_milli, int64_t repeat_milli, int64_t seed) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->ctx == NULL || request->model == NULL) return SLANG_ERR_INVALID;
    if (top_k < 0 || top_k > INT32_MAX || top_p_milli <= 0 || top_p_milli > 1000 ||
        repeat_milli <= 0 || repeat_milli > 100000 || temp_milli > 100000 || seed > (int64_t)UINT32_MAX)
        return SLANG_ERR_INVALID;
    struct llama_sampler *chain = llama_sampler_chain_init(llama_sampler_chain_default_params());
    if (chain == NULL) return SLANG_ERR_NO_CTX;
    if (repeat_milli != 1000)
        llama_sampler_chain_add(chain, llama_sampler_init_penalties(
            llama_vocab_n_tokens(llama_model_get_vocab(request->model)), 64,
            (float)repeat_milli / 1000.0f, 0.0f, 0.0f));
    if (temp_milli <= 0) {
        llama_sampler_chain_add(chain, llama_sampler_init_greedy());
    } else {
        if (top_k > 0) llama_sampler_chain_add(chain, llama_sampler_init_top_k((int32_t)top_k));
        if (top_p_milli < 1000)
            llama_sampler_chain_add(chain, llama_sampler_init_top_p((float)top_p_milli / 1000.0f, 1));
        llama_sampler_chain_add(chain, llama_sampler_init_temp((float)temp_milli / 1000.0f));
        llama_sampler_chain_add(chain, llama_sampler_init_dist(seed < 0 ? LLAMA_DEFAULT_SEED : (uint32_t)seed));
    }
    llama_sampler_free(request->smpl);
    request->smpl = chain;
    return 0;
}

/* End-of-generation against the REQUEST's model. slang_ggml_is_eog asks the
 * default model's vocabulary, which is wrong (or absent) for a request on a
 * model handle. */
int64_t slang_ggml_request_is_eog(int64_t handle, int64_t token) {
    struct slang_request *request = slang_request_get(handle);
    if (request == NULL || request->model == NULL) return SLANG_ERR_INVALID;
    return llama_vocab_is_eog(llama_model_get_vocab(request->model), (llama_token)token) ? 1 : 0;
}
