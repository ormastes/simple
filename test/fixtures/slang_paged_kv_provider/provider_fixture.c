#include "slang_paged_kv_provider.h"
#include "provider_fixture.h"

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define FIXTURE_NAMESPACE INT64_C(701)
#define MAX_POOLS 2
#define MAX_PAGES 16
#define MAX_REQUESTS 8
#define MAX_TRANSACTIONS 8
#define MAX_TABLE_PAGES 8
#define MAX_PAGE_TOKENS 8
#define MAX_REQUEST_TOKENS 64

#define ERR_INVALID (-1)
#define ERR_BUSY (-2)
#define ERR_LIMIT (-3)
#define ERR_STATE (-4)
#define ERR_INJECTED (-5)

struct page_record {
    uint64_t generation;
    int active;
    int sealed;
    int poisoned;
    int64_t valid_rows;
    int64_t map_refs;
    int64_t staged_refs;
    int64_t exclusive_transaction;
    int64_t rows[MAX_PAGE_TOKENS];
};

struct pool_record {
    uint64_t generation;
    int active;
    int64_t execution_namespace;
    int64_t page_tokens;
    int64_t page_capacity;
    int64_t byte_limit;
    struct page_record pages[MAX_PAGES];
};

struct request_record {
    uint64_t generation;
    int active;
    int cancelled;
    int logits_valid;
    int64_t execution_namespace;
    int64_t token_capacity;
    int64_t tokens[MAX_REQUEST_TOKENS];
    int64_t token_count;
    int64_t active_transaction;
    int64_t pool_handle;
    int64_t table_base;
    int64_t page_count;
    int64_t pages[MAX_TABLE_PAGES];
    int64_t cursor;
    int64_t logits;
};

struct transaction_entry {
    int64_t page_handle;
    int64_t initial_valid;
    int64_t writable_capacity;
    int mutable;
    int original_sealed;
    int original_poisoned;
    int64_t original_rows[MAX_PAGE_TOKENS];
};

struct transaction_record {
    uint64_t generation;
    int active;
    int failed;
    int produced_logits;
    int64_t logits_position;
    int64_t request_handle;
    int64_t pool_handle;
    int64_t table_base;
    int64_t expected_pages;
    int64_t entry_count;
    int64_t pending_logits;
    struct transaction_entry entries[MAX_TABLE_PAGES];
};

static struct pool_record pools[MAX_POOLS];
static struct request_record requests[MAX_REQUESTS];
static struct transaction_record transactions[MAX_TRANSACTIONS];
static int fail_copy;
static int fail_prefill;
static int fail_commit;
static uint64_t page_generation_clock;

static int64_t make_handle(uint64_t generation, int64_t slot, int64_t width) {
    if (generation == 0 || generation > (uint64_t)(INT64_MAX / width - 1))
        return ERR_LIMIT;
    return (int64_t)(generation * (uint64_t)width + (uint64_t)slot + 1);
}

static int decode_handle(int64_t handle, int64_t width, int64_t *slot,
                         uint64_t *generation) {
    uint64_t raw;
    if (handle <= 0) return 0;
    raw = (uint64_t)(handle - 1);
    *slot = (int64_t)(raw % (uint64_t)width);
    *generation = raw / (uint64_t)width;
    return *generation != 0;
}

static struct pool_record *get_pool(int64_t handle) {
    int64_t slot;
    uint64_t generation;
    if (!decode_handle(handle, MAX_POOLS, &slot, &generation)) return NULL;
    if (!pools[slot].active || pools[slot].generation != generation) return NULL;
    return &pools[slot];
}

static struct page_record *get_page(struct pool_record *pool, int64_t handle) {
    int64_t slot;
    uint64_t generation;
    if (pool == NULL || !decode_handle(handle, MAX_PAGES, &slot, &generation))
        return NULL;
    if (!pool->pages[slot].active || pool->pages[slot].generation != generation)
        return NULL;
    return &pool->pages[slot];
}

static struct request_record *get_request(int64_t handle) {
    int64_t slot;
    uint64_t generation;
    if (!decode_handle(handle, MAX_REQUESTS, &slot, &generation)) return NULL;
    if (!requests[slot].active || requests[slot].generation != generation)
        return NULL;
    return &requests[slot];
}

static struct transaction_record *get_transaction(int64_t handle) {
    int64_t slot;
    uint64_t generation;
    if (!decode_handle(handle, MAX_TRANSACTIONS, &slot, &generation)) return NULL;
    if (!transactions[slot].active || transactions[slot].generation != generation)
        return NULL;
    return &transactions[slot];
}

static int64_t page_bytes_of(const struct pool_record *pool) {
    if (pool->page_tokens > INT64_MAX / (int64_t)sizeof(int64_t)) return ERR_LIMIT;
    return pool->page_tokens * (int64_t)sizeof(int64_t);
}

static int64_t kv_value(int64_t token, int64_t position) {
    if (token < 0 || position < 0 || token > (INT64_MAX - position) / 1000)
        return ERR_LIMIT;
    return token * 1000 + position;
}

static int64_t fail_transaction(struct transaction_record *txn, int64_t error) {
    struct request_record *request;
    if (txn == NULL) return error;
    txn->failed = 1;
    request = get_request(txn->request_handle);
    if (request != NULL) request->logits_valid = 0;
    return error;
}

static int64_t entry_base(const struct transaction_record *txn, int64_t index,
                          int64_t page_tokens) {
    if (index < 0 || page_tokens <= 0 || index > INT64_MAX / page_tokens)
        return ERR_LIMIT;
    if (txn->table_base > INT64_MAX - index * page_tokens) return ERR_LIMIT;
    return txn->table_base + index * page_tokens;
}

static void unmap_request(struct request_record *request) {
    struct pool_record *pool = get_pool(request->pool_handle);
    if (pool != NULL) {
        for (int64_t i = 0; i < request->page_count; ++i) {
            struct page_record *page = get_page(pool, request->pages[i]);
            if (page != NULL && page->map_refs > 0) page->map_refs--;
        }
    }
    request->pool_handle = 0;
    request->page_count = 0;
    request->cursor = 0;
}

static void consume_abort(struct transaction_record *txn) {
    struct pool_record *pool = get_pool(txn->pool_handle);
    struct request_record *request = get_request(txn->request_handle);
    int64_t transaction_handle = make_handle(
        txn->generation, (int64_t)(txn - transactions), MAX_TRANSACTIONS);
    if (pool != NULL) {
        for (int64_t i = 0; i < txn->entry_count; ++i) {
            struct transaction_entry *entry = &txn->entries[i];
            struct page_record *page = get_page(pool, entry->page_handle);
            if (page == NULL) continue;
            if (entry->mutable) {
                page->valid_rows = entry->initial_valid;
                page->sealed = entry->original_sealed;
                page->poisoned = entry->original_poisoned;
                memcpy(page->rows, entry->original_rows, sizeof(page->rows));
            }
            if (page->staged_refs > 0) page->staged_refs--;
            if (page->exclusive_transaction == transaction_handle)
                page->exclusive_transaction = 0;
        }
    }
    if (request != NULL) {
        request->active_transaction = 0;
        request->logits_valid = 0;
    }
    txn->active = 0;
}

int64_t slang_ggml_page_abi_version(void) { return SLANG_PHYSICAL_PAGE_ABI_V1; }
int64_t slang_ggml_page_execution_namespace(void) { return FIXTURE_NAMESPACE; }

int64_t slang_ggml_page_pool_create(int64_t execution_namespace,
                                    int64_t page_tokens,
                                    int64_t page_capacity,
                                    int64_t byte_limit) {
    int64_t bytes;
    if (execution_namespace != FIXTURE_NAMESPACE || page_tokens <= 0 ||
        page_tokens > MAX_PAGE_TOKENS || page_capacity <= 0 ||
        page_capacity > MAX_PAGES || byte_limit <= 0)
        return ERR_INVALID;
    if (page_tokens > INT64_MAX / (int64_t)sizeof(int64_t)) return ERR_LIMIT;
    bytes = page_tokens * (int64_t)sizeof(int64_t);
    if (page_capacity > INT64_MAX / bytes || page_capacity * bytes > byte_limit)
        return ERR_LIMIT;
    for (int64_t i = 0; i < MAX_POOLS; ++i) {
        if (!pools[i].active) {
            uint64_t generation = pools[i].generation + 1;
            uint64_t page_generations[MAX_PAGES];
            int64_t handle = make_handle(generation, i, MAX_POOLS);
            if (generation == 0) return ERR_LIMIT;
            if (handle <= 0) return handle;
            for (int64_t j = 0; j < MAX_PAGES; ++j)
                page_generations[j] = pools[i].pages[j].generation;
            memset(&pools[i], 0, sizeof(pools[i]));
            for (int64_t j = 0; j < MAX_PAGES; ++j)
                pools[i].pages[j].generation = page_generations[j];
            pools[i].generation = generation;
            pools[i].active = 1;
            pools[i].execution_namespace = execution_namespace;
            pools[i].page_tokens = page_tokens;
            pools[i].page_capacity = page_capacity;
            pools[i].byte_limit = byte_limit;
            return handle;
        }
    }
    return ERR_BUSY;
}

int64_t slang_ggml_page_pool_destroy(int64_t pool_handle) {
    struct pool_record *pool = get_pool(pool_handle);
    if (pool == NULL) return ERR_INVALID;
    for (int64_t i = 0; i < pool->page_capacity; ++i)
        if (pool->pages[i].active) return ERR_BUSY;
    for (int64_t i = 0; i < MAX_TRANSACTIONS; ++i)
        if (transactions[i].active && transactions[i].pool_handle == pool_handle)
            return ERR_BUSY;
    pool->active = 0;
    return 0;
}

int64_t slang_ggml_page_reserve(int64_t pool_handle) {
    struct pool_record *pool = get_pool(pool_handle);
    if (pool == NULL) return ERR_INVALID;
    for (int64_t i = 0; i < pool->page_capacity; ++i) {
        if (!pool->pages[i].active) {
            uint64_t generation = page_generation_clock + 1;
            int64_t handle = make_handle(generation, i, MAX_PAGES);
            if (generation == 0 || handle <= 0) return ERR_LIMIT;
            memset(&pool->pages[i], 0, sizeof(pool->pages[i]));
            pool->pages[i].generation = generation;
            pool->pages[i].active = 1;
            page_generation_clock = generation;
            return handle;
        }
    }
    return ERR_BUSY;
}

int64_t slang_ggml_page_release(int64_t pool_handle, int64_t page_handle) {
    struct page_record *page = get_page(get_pool(pool_handle), page_handle);
    if (page == NULL) return ERR_INVALID;
    if (page->map_refs != 0 || page->staged_refs != 0) return ERR_BUSY;
    page->active = 0;
    return 0;
}

int64_t slang_ggml_page_seal(int64_t pool_handle, int64_t page_handle) {
    struct page_record *page = get_page(get_pool(pool_handle), page_handle);
    if (page == NULL || page->poisoned) return ERR_INVALID;
    if (page->exclusive_transaction != 0) return ERR_BUSY;
    page->sealed = 1;
    return 0;
}

int64_t slang_ggml_page_copy_tail(int64_t pool_handle, int64_t source_page,
                                  int64_t destination_page, int64_t valid_rows) {
    struct pool_record *pool = get_pool(pool_handle);
    struct page_record *source = get_page(pool, source_page);
    struct page_record *destination = get_page(pool, destination_page);
    if (pool == NULL || source == NULL || destination == NULL ||
        source == destination || !source->sealed || source->poisoned ||
        source->staged_refs != 0 || destination->sealed || destination->poisoned ||
        destination->map_refs != 0 || destination->staged_refs != 0 ||
        valid_rows < 0 || valid_rows > source->valid_rows ||
        valid_rows > pool->page_tokens)
        return ERR_INVALID;
    if (fail_copy) {
        fail_copy = 0;
        destination->poisoned = 1;
        return ERR_INJECTED;
    }
    memcpy(destination->rows, source->rows,
           (size_t)valid_rows * sizeof(destination->rows[0]));
    destination->valid_rows = valid_rows;
    return 0;
}

int64_t slang_ggml_page_table_begin(int64_t request_handle,
                                    int64_t pool_handle,
                                    int64_t table_base_position,
                                    int64_t expected_pages) {
    struct request_record *request = get_request(request_handle);
    struct pool_record *pool = get_pool(pool_handle);
    if (request == NULL || pool == NULL || request->cancelled ||
        request->execution_namespace != pool->execution_namespace ||
        request->active_transaction != 0 || table_base_position < 0 ||
        expected_pages <= 0 || expected_pages > MAX_TABLE_PAGES)
        return ERR_INVALID;
    for (int64_t i = 0; i < MAX_TRANSACTIONS; ++i) {
        if (!transactions[i].active) {
            uint64_t generation = transactions[i].generation + 1;
            int64_t handle = make_handle(generation, i, MAX_TRANSACTIONS);
            if (generation == 0) return ERR_LIMIT;
            if (handle <= 0) return handle;
            memset(&transactions[i], 0, sizeof(transactions[i]));
            transactions[i].generation = generation;
            transactions[i].active = 1;
            transactions[i].request_handle = request_handle;
            transactions[i].pool_handle = pool_handle;
            transactions[i].table_base = table_base_position;
            transactions[i].expected_pages = expected_pages;
            request->active_transaction = handle;
            return handle;
        }
    }
    return ERR_BUSY;
}

int64_t slang_ggml_page_table_push(int64_t transaction_handle,
                                   int64_t page_handle, int64_t valid_rows,
                                   int64_t writable_capacity) {
    struct transaction_record *txn = get_transaction(transaction_handle);
    struct pool_record *pool;
    struct page_record *page;
    struct transaction_entry *entry;
    int64_t base;
    if (txn == NULL || txn->failed) return ERR_STATE;
    pool = get_pool(txn->pool_handle);
    page = get_page(pool, page_handle);
    if (pool == NULL || page == NULL || page->poisoned ||
        txn->entry_count >= txn->expected_pages || valid_rows < 0 ||
        writable_capacity < 0 || valid_rows > pool->page_tokens ||
        writable_capacity > pool->page_tokens - valid_rows ||
        page->valid_rows != valid_rows || page->exclusive_transaction != 0 ||
        (page->sealed && writable_capacity != 0) ||
        (!page->sealed &&
         (page->map_refs != 0 || page->staged_refs != 0))) {
        return fail_transaction(txn, ERR_INVALID);
    }
    for (int64_t i = 0; i < txn->entry_count; ++i) {
        if (txn->entries[i].page_handle == page_handle) {
            return fail_transaction(txn, ERR_INVALID);
        }
    }
    base = entry_base(txn, txn->entry_count, pool->page_tokens);
    if (base < 0 || valid_rows > INT64_MAX - base ||
        writable_capacity > INT64_MAX - base - valid_rows) {
        return fail_transaction(txn, ERR_LIMIT);
    }
    entry = &txn->entries[txn->entry_count++];
    entry->page_handle = page_handle;
    entry->initial_valid = valid_rows;
    entry->writable_capacity = writable_capacity;
    entry->mutable = writable_capacity > 0;
    entry->original_sealed = page->sealed;
    entry->original_poisoned = page->poisoned;
    memcpy(entry->original_rows, page->rows, sizeof(entry->original_rows));
    page->staged_refs++;
    if (!page->sealed) page->exclusive_transaction = transaction_handle;
    return 0;
}

static int64_t write_position(struct transaction_record *txn, int64_t position,
                              int64_t token) {
    struct pool_record *pool = get_pool(txn->pool_handle);
    for (int64_t i = 0; pool != NULL && i < txn->entry_count; ++i) {
        struct transaction_entry *entry = &txn->entries[i];
        struct page_record *page = get_page(pool, entry->page_handle);
        int64_t base = entry_base(txn, i, pool->page_tokens);
        int64_t row;
        int64_t value;
        if (page == NULL || base < 0) return ERR_STATE;
        if (position < base + entry->initial_valid ||
            position >= base + entry->initial_valid + entry->writable_capacity)
            continue;
        row = position - base;
        if (row != page->valid_rows || token < 0) return ERR_INVALID;
        value = kv_value(token, position);
        if (value < 0) return value;
        page->rows[row] = value;
        if (row + 1 > page->valid_rows) page->valid_rows = row + 1;
        if (page->valid_rows == pool->page_tokens) page->sealed = 1;
        txn->pending_logits = value;
        txn->logits_position = position;
        txn->produced_logits = 1;
        return 0;
    }
    return ERR_INVALID;
}

int64_t slang_ggml_page_prefill(int64_t transaction_handle,
                                int64_t start_position, int64_t token_start,
                                int64_t token_count) {
    struct transaction_record *txn = get_transaction(transaction_handle);
    struct request_record *request;
    if (txn == NULL || txn->failed) return ERR_STATE;
    request = get_request(txn->request_handle);
    if (request == NULL || start_position < 0 || token_start < 0 ||
        token_count <= 0 || token_start > request->token_count ||
        token_count > request->token_count - token_start ||
        start_position > INT64_MAX - token_count) {
        return fail_transaction(txn, ERR_INVALID);
    }
    for (int64_t i = 0; i < token_count; ++i) {
        int64_t status = write_position(txn, start_position + i,
                                        request->tokens[token_start + i]);
        if (status != 0) {
            return fail_transaction(txn, status);
        }
        if (fail_prefill) {
            fail_prefill = 0;
            return fail_transaction(txn, ERR_INJECTED);
        }
    }
    return 0;
}

int64_t slang_ggml_page_decode(int64_t transaction_handle,
                               int64_t token, int64_t position) {
    struct transaction_record *txn = get_transaction(transaction_handle);
    int64_t status;
    if (txn == NULL || txn->failed) return ERR_STATE;
    if (position < 0 || token < 0) return fail_transaction(txn, ERR_INVALID);
    status = write_position(txn, position, token);
    if (status != 0) return fail_transaction(txn, status);
    return status;
}

int64_t slang_ggml_page_boundary_logits(int64_t transaction_handle,
                                        int64_t boundary_token_index,
                                        int64_t boundary_position) {
    struct transaction_record *txn = get_transaction(transaction_handle);
    struct request_record *request;
    struct pool_record *pool;
    if (txn == NULL || txn->failed) return ERR_STATE;
    request = get_request(txn->request_handle);
    pool = get_pool(txn->pool_handle);
    if (request == NULL || pool == NULL || boundary_token_index < 0 ||
        boundary_token_index >= request->token_count || boundary_position < 0) {
        return fail_transaction(txn, ERR_INVALID);
    }
    for (int64_t i = 0; i < txn->entry_count; ++i) {
        struct page_record *page = get_page(pool, txn->entries[i].page_handle);
        int64_t base = entry_base(txn, i, pool->page_tokens);
        int64_t row = boundary_position - base;
        int64_t expected = kv_value(request->tokens[boundary_token_index],
                                    boundary_position);
        if (page != NULL && row >= 0 && row < page->valid_rows &&
            page->rows[row] == expected) {
            txn->pending_logits = expected;
            txn->logits_position = boundary_position;
            txn->produced_logits = 1;
            return 0;
        }
    }
    return fail_transaction(txn, ERR_INVALID);
}

int64_t slang_ggml_page_table_commit(int64_t transaction_handle) {
    struct transaction_record *txn = get_transaction(transaction_handle);
    struct request_record *request;
    struct pool_record *pool;
    if (txn == NULL) return ERR_INVALID;
    request = get_request(txn->request_handle);
    pool = get_pool(txn->pool_handle);
    if (fail_commit) {
        fail_commit = 0;
        txn->failed = 1;
    }
    if (request == NULL || pool == NULL || txn->failed ||
        txn->entry_count != txn->expected_pages || !txn->produced_logits) {
        consume_abort(txn);
        return ERR_STATE;
    }
    for (int64_t i = 0; i < txn->entry_count; ++i) {
        struct page_record *page = get_page(pool, txn->entries[i].page_handle);
        if (page == NULL || page->poisoned ||
            (i + 1 < txn->entry_count &&
             (page->valid_rows != pool->page_tokens || !page->sealed))) {
            consume_abort(txn);
            return ERR_STATE;
        }
    }
    {
        struct page_record *last = get_page(
            pool, txn->entries[txn->entry_count - 1].page_handle);
        int64_t last_base = entry_base(txn, txn->entry_count - 1,
                                       pool->page_tokens);
        if (last == NULL || last_base < 0 || last->valid_rows <= 0 ||
            last->valid_rows > INT64_MAX - last_base ||
            txn->logits_position != last_base + last->valid_rows - 1) {
            consume_abort(txn);
            return ERR_STATE;
        }
    }
    unmap_request(request);
    request->pool_handle = txn->pool_handle;
    request->table_base = txn->table_base;
    request->page_count = txn->entry_count;
    for (int64_t i = 0; i < txn->entry_count; ++i) {
        struct page_record *page = get_page(pool, txn->entries[i].page_handle);
        request->pages[i] = txn->entries[i].page_handle;
        page->map_refs++;
        if (page->staged_refs > 0) page->staged_refs--;
        if (page->exclusive_transaction == transaction_handle)
            page->exclusive_transaction = 0;
    }
    request->cursor = txn->table_base +
        (txn->entry_count - 1) * pool->page_tokens +
        get_page(pool, txn->entries[txn->entry_count - 1].page_handle)->valid_rows;
    request->logits = txn->pending_logits;
    request->logits_valid = 1;
    request->active_transaction = 0;
    txn->active = 0;
    return 0;
}

int64_t slang_ggml_page_table_abort(int64_t transaction_handle) {
    struct transaction_record *txn = get_transaction(transaction_handle);
    if (txn == NULL) return ERR_INVALID;
    consume_abort(txn);
    return 0;
}

int64_t slang_ggml_page_allocated_bytes(int64_t pool_handle) {
    struct pool_record *pool = get_pool(pool_handle);
    int64_t count = 0;
    int64_t bytes;
    if (pool == NULL) return ERR_INVALID;
    bytes = page_bytes_of(pool);
    if (bytes < 0) return bytes;
    for (int64_t i = 0; i < pool->page_capacity; ++i)
        if (pool->pages[i].active) count++;
    return count * bytes;
}

int64_t slang_ggml_page_bytes(int64_t pool_handle) {
    struct pool_record *pool = get_pool(pool_handle);
    return pool == NULL ? ERR_INVALID : page_bytes_of(pool);
}

int64_t fixture_request_create(int64_t execution_namespace, int64_t token_capacity) {
    if (execution_namespace != FIXTURE_NAMESPACE || token_capacity <= 0 ||
        token_capacity > MAX_REQUEST_TOKENS) return ERR_INVALID;
    for (int64_t i = 0; i < MAX_REQUESTS; ++i) {
        if (!requests[i].active) {
            uint64_t generation = requests[i].generation + 1;
            int64_t handle = make_handle(generation, i, MAX_REQUESTS);
            if (generation == 0) return ERR_LIMIT;
            if (handle <= 0) return handle;
            memset(&requests[i], 0, sizeof(requests[i]));
            requests[i].generation = generation;
            requests[i].active = 1;
            requests[i].execution_namespace = execution_namespace;
            requests[i].token_capacity = token_capacity;
            return handle;
        }
    }
    return ERR_BUSY;
}

static int64_t end_request(int64_t request_handle, int cancelled) {
    struct request_record *request = get_request(request_handle);
    if (request == NULL) return ERR_INVALID;
    if (request->active_transaction != 0) {
        struct transaction_record *txn = get_transaction(request->active_transaction);
        if (txn != NULL) consume_abort(txn);
    }
    unmap_request(request);
    request->cancelled = cancelled;
    request->active = 0;
    request->logits_valid = 0;
    return 0;
}

int64_t fixture_request_close(int64_t request_handle) {
    return end_request(request_handle, 0);
}

int64_t fixture_request_cancel(int64_t request_handle) {
    return end_request(request_handle, 1);
}

int64_t fixture_request_set_token(int64_t request_handle, int64_t index,
                                  int64_t token) {
    struct request_record *request = get_request(request_handle);
    if (request == NULL || index < 0 || index >= request->token_capacity)
        return ERR_INVALID;
    if (token < 0) return ERR_INVALID;
    request->tokens[index] = token;
    if (index + 1 > request->token_count) request->token_count = index + 1;
    return 0;
}

int64_t fixture_request_sample(int64_t request_handle) {
    struct request_record *request = get_request(request_handle);
    return request == NULL || !request->logits_valid ? ERR_STATE : request->logits;
}

int64_t fixture_request_cursor(int64_t request_handle) {
    struct request_record *request = get_request(request_handle);
    return request == NULL ? ERR_INVALID : request->cursor;
}

int64_t fixture_request_page(int64_t request_handle, int64_t index) {
    struct request_record *request = get_request(request_handle);
    if (request == NULL || index < 0 || index >= request->page_count)
        return ERR_INVALID;
    return request->pages[index];
}

int64_t fixture_page_row(int64_t pool_handle, int64_t page_handle, int64_t row) {
    struct pool_record *pool = get_pool(pool_handle);
    struct page_record *page = get_page(pool, page_handle);
    if (pool == NULL || page == NULL || row < 0 || row >= page->valid_rows)
        return ERR_INVALID;
    return page->rows[row];
}

int64_t fixture_page_valid_rows(int64_t pool_handle, int64_t page_handle) {
    struct page_record *page = get_page(get_pool(pool_handle), page_handle);
    return page == NULL ? ERR_INVALID : page->valid_rows;
}

int64_t fixture_page_is_sealed(int64_t pool_handle, int64_t page_handle) {
    struct page_record *page = get_page(get_pool(pool_handle), page_handle);
    return page == NULL ? ERR_INVALID : page->sealed;
}

int64_t fixture_fail_next_copy(void) { fail_copy = 1; return 0; }
int64_t fixture_fail_next_prefill(void) { fail_prefill = 1; return 0; }
int64_t fixture_fail_next_commit(void) { fail_commit = 1; return 0; }
