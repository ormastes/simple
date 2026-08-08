/*
 * Fast In-Memory Database Runtime
 *
 * Provides rt_db_* symbols for fast in-memory database operations that bypass
 * interpreter overhead. Uses open-addressing hash tables for PK index and
 * flat arrays for typed column storage.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_db.c -o runtime_db.o
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ================================================================
 * ABI: plain machine i64, NOT tagged RuntimeValues
 *
 * This file used to box/unbox every integer as a RuntimeValue
 * (`v << 3`). That convention is wrong for an `extern fn` whose Simple
 * signature declares `i64` params and an `i64` result: generated code passes
 * and expects a RAW machine word there. A JIT trace of
 * rt_db_table_create("probe_table", 3, 0) showed num_cols arriving as 3, not
 * 24, so `unbox_int` turned it into 0 and every call returned -1. The entire
 * rt_db_* family therefore failed closed from the JIT; only the interpreter
 * worked, because the interpreter runs a separate Rust implementation
 * (compiler/src/interpreter_extern/sffi_db.rs) and never reached this file.
 *
 * The reference for the correct convention is the rt_package_* family
 * (runtime/src/value/sffi/package.rs), whose raw-i64 signatures were proven
 * through this exact codegen path.
 *
 * Text params are `(ptr, len)` pairs, never `const char*`: Simple heap strings
 * are allocated as size_of::<RuntimeString>() + len with NO trailing NUL (see
 * alloc_runtime_string), so a bare pointer makes strlen/strdup read past the
 * allocation. A text RESULT is a RuntimeValue built by rt_string_new, for the
 * mirror-image reason -- codegen cannot turn a raw C pointer back into a
 * Simple text.
 * ================================================================ */

/* Runtime string constructor (runtime_native.c). Returns a RuntimeValue. */
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

/* Copy a Simple (ptr, len) text argument into a NUL-terminated C string so the
 * table's internal strdup/strcmp machinery stays unchanged. Caller frees. */
static char* db_text_dup(const uint8_t* ptr, int64_t len) {
    if (!ptr || len < 0) {
        len = 0;
    }
    char* out = (char*)malloc((size_t)len + 1);
    if (!out) {
        return NULL;
    }
    if (len > 0) {
        memcpy(out, ptr, (size_t)len);
    }
    out[len] = '\0';
    return out;
}

/* ================================================================
 * Constants
 * ================================================================ */

#define DB_MAX_TABLES    64
#define DB_INIT_CAP      256
#define DB_MAX_COLS      64
#define DB_SCAN_MAX      65536
#define DB_LOAD_FACTOR   0.7

/* ================================================================
 * Column value types
 * ================================================================ */

typedef enum {
    COL_UNSET = 0,
    COL_INT   = 1,
    COL_TEXT  = 2
} ColType;

/* ================================================================
 * Row structure: typed column storage
 * ================================================================ */

typedef struct {
    char*    pk_text;       /* primary key (owned, strdup'd) */
    int64_t* int_values;    /* int column values */
    char**   text_values;   /* text column values (owned, strdup'd) */
    ColType* col_types;     /* per-column type tag */
    int      alive;         /* 0 = empty, 1 = alive, 2 = tombstone */
} DbRow;

/* ================================================================
 * Table structure: open-addressing hash + flat row array
 * ================================================================ */

typedef struct {
    char*    name;
    int64_t  num_cols;
    int64_t  pk_col;

    /* Row storage (flat array, index = row id) */
    DbRow*   rows;
    int64_t  row_cap;
    int64_t  row_count;     /* next row id to allocate */
    int64_t  alive_count;   /* number of non-deleted rows */

    /* PK hash index: maps pk_text -> row index */
    int64_t* pk_index;      /* hash table: stores row index or -1 */
    char**   pk_keys;       /* parallel array of key copies for probing */
    int64_t  pk_cap;        /* hash table capacity (power of 2) */
    int64_t  pk_used;       /* number of occupied slots (including tombstones) */

    /* Scan results buffer */
    int64_t* scan_results;
    int64_t  scan_count;

    int      in_use;
} DbTable;

/* ================================================================
 * Global table registry
 * ================================================================ */

static DbTable g_tables[DB_MAX_TABLES];
static int     g_tables_init = 0;

static void ensure_init(void) {
    if (!g_tables_init) {
        memset(g_tables, 0, sizeof(g_tables));
        g_tables_init = 1;
    }
}

/* ================================================================
 * FNV-1a hash for strings
 * ================================================================ */

static uint64_t fnv1a(const char* s) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (; *s; s++) {
        h ^= (uint64_t)(unsigned char)*s;
        h *= 0x100000001b3ULL;
    }
    return h;
}

/* ================================================================
 * PK hash index operations
 * ================================================================ */

static void pk_index_init(DbTable* t, int64_t cap) {
    t->pk_cap = cap;
    t->pk_used = 0;
    t->pk_index = (int64_t*)malloc((size_t)cap * sizeof(int64_t));
    t->pk_keys  = (char**)calloc((size_t)cap, sizeof(char*));
    for (int64_t i = 0; i < cap; i++) {
        t->pk_index[i] = -1;
    }
}

static int64_t pk_lookup(DbTable* t, const char* key) {
    uint64_t h = fnv1a(key);
    int64_t mask = t->pk_cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);

    for (int64_t probe = 0; probe < t->pk_cap; probe++) {
        int64_t slot = (idx + probe) & mask;
        if (t->pk_index[slot] == -1 && t->pk_keys[slot] == NULL) {
            /* empty slot, key not found */
            return -1;
        }
        if (t->pk_keys[slot] != NULL && strcmp(t->pk_keys[slot], key) == 0) {
            /* found — check if the row is alive */
            int64_t row = t->pk_index[slot];
            if (row >= 0 && t->rows[row].alive == 1) {
                return row;
            }
            /* tombstone — continue probing */
        }
        /* collision or tombstone, keep probing */
    }
    return -1;
}

static void pk_resize(DbTable* t);

static void pk_insert(DbTable* t, const char* key, int64_t row_idx) {
    /* Check load factor */
    if ((double)(t->pk_used + 1) / (double)t->pk_cap > DB_LOAD_FACTOR) {
        pk_resize(t);
    }

    uint64_t h = fnv1a(key);
    int64_t mask = t->pk_cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);

    for (int64_t probe = 0; probe < t->pk_cap; probe++) {
        int64_t slot = (idx + probe) & mask;
        if (t->pk_index[slot] == -1 || t->pk_keys[slot] == NULL) {
            /* empty or tombstone slot */
            if (t->pk_keys[slot]) free(t->pk_keys[slot]);
            t->pk_keys[slot] = strdup(key);
            t->pk_index[slot] = row_idx;
            t->pk_used++;
            return;
        }
        if (strcmp(t->pk_keys[slot], key) == 0) {
            /* update existing */
            t->pk_index[slot] = row_idx;
            return;
        }
    }
}

static void pk_resize(DbTable* t) {
    int64_t old_cap = t->pk_cap;
    int64_t* old_index = t->pk_index;
    char** old_keys = t->pk_keys;

    int64_t new_cap = old_cap * 2;
    t->pk_cap = new_cap;
    t->pk_used = 0;
    t->pk_index = (int64_t*)malloc((size_t)new_cap * sizeof(int64_t));
    t->pk_keys  = (char**)calloc((size_t)new_cap, sizeof(char*));
    for (int64_t i = 0; i < new_cap; i++) {
        t->pk_index[i] = -1;
    }

    /* Re-insert live entries */
    for (int64_t i = 0; i < old_cap; i++) {
        if (old_keys[i] != NULL && old_index[i] >= 0) {
            pk_insert(t, old_keys[i], old_index[i]);
            free(old_keys[i]);
        }
    }
    free(old_index);
    free(old_keys);
}

static void pk_remove(DbTable* t, const char* key) {
    uint64_t h = fnv1a(key);
    int64_t mask = t->pk_cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);

    for (int64_t probe = 0; probe < t->pk_cap; probe++) {
        int64_t slot = (idx + probe) & mask;
        if (t->pk_index[slot] == -1 && t->pk_keys[slot] == NULL) {
            return; /* not found */
        }
        if (t->pk_keys[slot] != NULL && strcmp(t->pk_keys[slot], key) == 0) {
            /* tombstone: clear key but leave slot marked as used for probing */
            free(t->pk_keys[slot]);
            t->pk_keys[slot] = NULL;
            t->pk_index[slot] = -2; /* tombstone marker */
            return;
        }
    }
}

/* ================================================================
 * Row allocation
 * ================================================================ */

static void ensure_row_cap(DbTable* t, int64_t needed) {
    if (needed <= t->row_cap) return;
    int64_t new_cap = t->row_cap * 2;
    if (new_cap < needed) new_cap = needed;
    t->rows = (DbRow*)realloc(t->rows, (size_t)new_cap * sizeof(DbRow));
    memset(t->rows + t->row_cap, 0, (size_t)(new_cap - t->row_cap) * sizeof(DbRow));
    t->row_cap = new_cap;
}

static int64_t alloc_row(DbTable* t) {
    ensure_row_cap(t, t->row_count + 1);
    int64_t idx = t->row_count++;
    DbRow* r = &t->rows[idx];
    r->pk_text = NULL;
    r->int_values = (int64_t*)calloc((size_t)t->num_cols, sizeof(int64_t));
    r->text_values = (char**)calloc((size_t)t->num_cols, sizeof(char*));
    r->col_types = (ColType*)calloc((size_t)t->num_cols, sizeof(ColType));
    r->alive = 1;
    t->alive_count++;
    return idx;
}

static void free_row(DbRow* r, int64_t num_cols) {
    if (r->pk_text) { free(r->pk_text); r->pk_text = NULL; }
    if (r->text_values) {
        for (int64_t i = 0; i < num_cols; i++) {
            if (r->text_values[i]) free(r->text_values[i]);
        }
        free(r->text_values);
        r->text_values = NULL;
    }
    if (r->int_values) { free(r->int_values); r->int_values = NULL; }
    if (r->col_types) { free(r->col_types); r->col_types = NULL; }
    r->alive = 0;
}

/* ================================================================
 * Public API: rt_db_* functions
 * ================================================================ */

static int64_t db_table_create_cstr(const char* name, int64_t num_cols_in, int64_t pk_col_in) {
    ensure_init();
    int64_t num_cols = (num_cols_in);
    int64_t pk_col = (pk_col_in);
    if (num_cols <= 0 || num_cols > DB_MAX_COLS) return (-1);
    if (pk_col < 0 || pk_col >= num_cols) return (-1);

    for (int i = 0; i < DB_MAX_TABLES; i++) {
        if (!g_tables[i].in_use) {
            DbTable* t = &g_tables[i];
            memset(t, 0, sizeof(DbTable));
            t->name = strdup(name ? name : "");
            t->num_cols = num_cols;
            t->pk_col = pk_col;
            t->row_cap = DB_INIT_CAP;
            t->rows = (DbRow*)calloc((size_t)DB_INIT_CAP, sizeof(DbRow));
            t->row_count = 0;
            t->alive_count = 0;
            t->scan_results = (int64_t*)malloc((size_t)DB_SCAN_MAX * sizeof(int64_t));
            t->scan_count = 0;
            pk_index_init(t, DB_INIT_CAP);
            t->in_use = 1;
            return ((int64_t)i);
        }
    }
    return (-1); /* no free table slots */
}

void rt_db_table_destroy(int64_t handle_in) {
    ensure_init();
    int64_t handle = (handle_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return;
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return;

    for (int64_t i = 0; i < t->row_count; i++) {
        if (t->rows[i].alive) {
            free_row(&t->rows[i], t->num_cols);
        }
    }
    free(t->rows);

    for (int64_t i = 0; i < t->pk_cap; i++) {
        if (t->pk_keys[i]) free(t->pk_keys[i]);
    }
    free(t->pk_index);
    free(t->pk_keys);
    free(t->scan_results);
    free(t->name);

    memset(t, 0, sizeof(DbTable));
}

static int64_t db_put_cstr(int64_t handle_in, const char* pk_text, int64_t num_values_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t num_values = (num_values_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (-1);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (-1);
    (void)num_values; /* reserved for future use */

    /* Check if PK already exists */
    int64_t existing = pk_lookup(t, pk_text ? pk_text : "");
    if (existing >= 0) {
        /* Update existing row — return its index */
        return (existing);
    }

    /* Allocate new row */
    int64_t row = alloc_row(t);
    t->rows[row].pk_text = strdup(pk_text ? pk_text : "");
    pk_insert(t, pk_text ? pk_text : "", row);
    return (row);
}

void rt_db_put_value_int(int64_t handle_in, int64_t row_in, int64_t col_in, int64_t value_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t row = (row_in);
    int64_t col = (col_in);
    int64_t value = (value_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return;
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return;
    if (row < 0 || row >= t->row_count) return;
    if (col < 0 || col >= t->num_cols) return;
    DbRow* r = &t->rows[row];
    if (!r->alive) return;
    r->int_values[col] = value;
    r->col_types[col] = COL_INT;
}

static void db_put_value_text_cstr(int64_t handle_in, int64_t row_in, int64_t col_in, const char* value) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t row = (row_in);
    int64_t col = (col_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return;
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return;
    if (row < 0 || row >= t->row_count) return;
    if (col < 0 || col >= t->num_cols) return;
    DbRow* r = &t->rows[row];
    if (!r->alive) return;
    if (r->text_values[col]) free(r->text_values[col]);
    r->text_values[col] = strdup(value ? value : "");
    r->col_types[col] = COL_TEXT;
}

static int64_t db_get_cstr(int64_t handle_in, const char* pk_text) {
    ensure_init();
    int64_t handle = (handle_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (-1);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (-1);
    return (pk_lookup(t, pk_text ? pk_text : ""));
}

int64_t rt_db_get_int(int64_t handle_in, int64_t row_in, int64_t col_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t row = (row_in);
    int64_t col = (col_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);
    if (row < 0 || row >= t->row_count) return (0);
    if (col < 0 || col >= t->num_cols) return (0);
    DbRow* r = &t->rows[row];
    if (!r->alive) return (0);
    return (r->int_values[col]);
}

static const char* db_get_text_cstr(int64_t handle_in, int64_t row_in, int64_t col_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t row = (row_in);
    int64_t col = (col_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return "";
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return "";
    if (row < 0 || row >= t->row_count) return "";
    if (col < 0 || col >= t->num_cols) return "";
    DbRow* r = &t->rows[row];
    if (!r->alive) return "";
    if (r->col_types[col] == COL_TEXT && r->text_values[col]) {
        return r->text_values[col];
    }
    return "";
}

int64_t rt_db_scan_range(int64_t handle_in, int64_t col_in, int64_t low_in, int64_t high_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t col = (col_in);
    int64_t low = (low_in);
    int64_t high = (high_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);
    if (col < 0 || col >= t->num_cols) return (0);

    t->scan_count = 0;
    for (int64_t i = 0; i < t->row_count && t->scan_count < DB_SCAN_MAX; i++) {
        DbRow* r = &t->rows[i];
        if (!r->alive) continue;
        if (r->col_types[col] == COL_INT) {
            int64_t v = r->int_values[col];
            if (v >= low && v <= high) {
                t->scan_results[t->scan_count++] = i;
            }
        }
    }
    return (t->scan_count);
}

int64_t rt_db_scan_result(int64_t handle_in, int64_t result_idx_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t result_idx = (result_idx_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (-1);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (-1);
    if (result_idx < 0 || result_idx >= t->scan_count) return (-1);
    return (t->scan_results[result_idx]);
}

static int64_t db_delete_cstr(int64_t handle_in, const char* pk_text) {
    ensure_init();
    int64_t handle = (handle_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);

    int64_t row = pk_lookup(t, pk_text ? pk_text : "");
    if (row < 0) return (0);

    pk_remove(t, pk_text ? pk_text : "");
    free_row(&t->rows[row], t->num_cols);
    t->rows[row].alive = 2; /* tombstone */
    t->alive_count--;
    return (1);
}

int64_t rt_db_row_count(int64_t handle_in) {
    ensure_init();
    int64_t handle = (handle_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);
    return (t->alive_count);
}

int64_t rt_db_col_count(int64_t handle_in) {
    ensure_init();
    int64_t handle = (handle_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);
    return (t->num_cols);
}

/* ================================================================
 * Batched operations — reduce interpreter dispatch overhead
 * ================================================================ */

/* Insert a 3-column row: (int, text, int) in one call.
 * type_mask encodes column types: bit i = 1 means text, 0 means int.
 * For type_mask=0b010 (=2): col0=int, col1=text, col2=int.
 * v0,v1,v2 are i64 values; for text cols the value is a char* cast to i64. */
static int64_t db_put_row3_cstr(int64_t handle_in, const char* pk,
                       int64_t type_mask_in,
                       int64_t v0_in, int64_t v1_in, int64_t v2_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t type_mask = (type_mask_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (-1);
    DbTable* t = &g_tables[handle];
    if (!t->in_use || t->num_cols < 3) return (-1);

    const char* key = pk ? pk : "";
    int64_t existing = pk_lookup(t, key);
    if (existing >= 0) return (existing);

    int64_t row_idx = t->row_count;
    if (row_idx >= t->row_cap) {
        int64_t new_cap = t->row_cap * 2;
        t->rows = (DbRow*)realloc(t->rows, (size_t)new_cap * sizeof(DbRow));
        for (int64_t i = t->row_cap; i < new_cap; i++) {
            memset(&t->rows[i], 0, sizeof(DbRow));
        }
        t->row_cap = new_cap;
    }

    DbRow* r = &t->rows[row_idx];
    r->pk_text = strdup(key);
    r->int_values = (int64_t*)calloc((size_t)t->num_cols, sizeof(int64_t));
    r->text_values = (char**)calloc((size_t)t->num_cols, sizeof(char*));
    r->col_types = (ColType*)calloc((size_t)t->num_cols, sizeof(ColType));
    r->alive = 1;

    int64_t vals[3] = {(v0_in), (v1_in), (v2_in)};
    for (int c = 0; c < 3; c++) {
        if (type_mask & (1 << c)) {
            const char* s = (const char*)(uintptr_t)vals[c];
            r->text_values[c] = strdup(s ? s : "");
            r->col_types[c] = COL_TEXT;
        } else {
            r->int_values[c] = vals[c];
            r->col_types[c] = COL_INT;
        }
    }

    pk_insert(t, key, row_idx);
    t->row_count++;
    t->alive_count++;
    return (row_idx);
}

/* Lookup by PK and return an int column value in one call.
 * Returns the value, or default_val if not found. */
static int64_t db_get_int_by_pk_cstr(int64_t handle_in, const char* pk, int64_t col_in,
                            int64_t default_val_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t col = (col_in);
    int64_t default_val = (default_val_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (default_val);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (default_val);

    int64_t row = pk_lookup(t, pk ? pk : "");
    if (row < 0 || row >= t->row_count) return (default_val);
    if (col < 0 || col >= t->num_cols) return (default_val);
    DbRow* r = &t->rows[row];
    if (!r->alive || r->col_types[col] != COL_INT) return (default_val);
    return (r->int_values[col]);
}

/* Update an int column by PK in one call. Returns 1 on success, 0 on not found. */
static int64_t db_update_int_cstr(int64_t handle_in, const char* pk, int64_t col_in,
                         int64_t value_in) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t col = (col_in);
    int64_t value = (value_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);

    int64_t row = pk_lookup(t, pk ? pk : "");
    if (row < 0 || row >= t->row_count) return (0);
    if (col < 0 || col >= t->num_cols) return (0);
    DbRow* r = &t->rows[row];
    if (!r->alive) return (0);
    r->int_values[col] = value;
    r->col_types[col] = COL_INT;
    return (1);
}

/* Update a text column by PK in one call. Returns 1 on success, 0 on not found. */
static int64_t db_update_text_cstr(int64_t handle_in, const char* pk, int64_t col_in,
                          const char* value) {
    ensure_init();
    int64_t handle = (handle_in);
    int64_t col = (col_in);
    if (handle < 0 || handle >= DB_MAX_TABLES) return (0);
    DbTable* t = &g_tables[handle];
    if (!t->in_use) return (0);

    int64_t row = pk_lookup(t, pk ? pk : "");
    if (row < 0 || row >= t->row_count) return (0);
    if (col < 0 || col >= t->num_cols) return (0);
    DbRow* r = &t->rows[row];
    if (!r->alive) return (0);
    if (r->text_values[col]) free(r->text_values[col]);
    r->text_values[col] = strdup(value ? value : "");
    r->col_types[col] = COL_TEXT;
    return (1);
}

/* ================================================================
 * Integer-PK variants (zero string allocation from caller)
 * ================================================================ */

static inline void ipk_to_str(int64_t pk, char buf[32]) {
    snprintf(buf, 32, "%ld", (long)pk);
}

/* Integer-PK variants: no caller-side string allocation. The PK is rendered
 * into a stack buffer and handed to the internal _cstr helpers directly, so
 * these never go through the (ptr, len) wrappers. */
int64_t rt_db_iput3(int64_t handle_in, int64_t pk_int_in,
                    int64_t v0_in, int64_t v1_in, int64_t v2_in) {
    char buf[32];
    ipk_to_str((pk_int_in), buf);
    return db_put_row3_cstr(handle_in, buf, 0, v0_in, v1_in, v2_in);
}

int64_t rt_db_iget_int(int64_t handle_in, int64_t pk_int_in, int64_t col_in,
                       int64_t default_val_in) {
    char buf[32];
    ipk_to_str((pk_int_in), buf);
    return db_get_int_by_pk_cstr(handle_in, buf, col_in, default_val_in);
}

int64_t rt_db_iupdate_int(int64_t handle_in, int64_t pk_int_in, int64_t col_in,
                          int64_t value_in) {
    char buf[32];
    ipk_to_str((pk_int_in), buf);
    return db_update_int_cstr(handle_in, buf, col_in, value_in);
}

int64_t rt_db_idelete(int64_t handle_in, int64_t pk_int_in) {
    char buf[32];
    ipk_to_str((pk_int_in), buf);
    return db_delete_cstr(handle_in, buf);
}

/* ================================================================
 * Exported entry points: Simple `text` as an explicit (ptr, len) pair
 *
 * These are the symbols generated code calls. Each copies its text arguments
 * into NUL-terminated buffers before touching the internal helpers, because a
 * Simple heap string has no trailing NUL and strlen/strdup would otherwise
 * read past the end of the allocation.
 * ================================================================ */

int64_t rt_db_table_create(const uint8_t* name_ptr, int64_t name_len,
                           int64_t num_cols, int64_t pk_col) {
    char* name = db_text_dup(name_ptr, name_len);
    int64_t result = db_table_create_cstr(name ? name : "", num_cols, pk_col);
    free(name);
    return result;
}

int64_t rt_db_put(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len,
                  int64_t num_values) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    int64_t result = db_put_cstr(handle, pk ? pk : "", num_values);
    free(pk);
    return result;
}

void rt_db_put_value_text(int64_t handle, int64_t row, int64_t col,
                          const uint8_t* value_ptr, int64_t value_len) {
    char* value = db_text_dup(value_ptr, value_len);
    db_put_value_text_cstr(handle, row, col, value ? value : "");
    free(value);
}

int64_t rt_db_get(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    int64_t result = db_get_cstr(handle, pk ? pk : "");
    free(pk);
    return result;
}

/* Returns a RuntimeValue text, not a `const char*`. A raw C pointer has no
 * lowering back to a Simple `text`, so the old signature handed generated code
 * a pointer it would have used as a tagged value. */
int64_t rt_db_get_text(int64_t handle, int64_t row, int64_t col) {
    const char* text = db_get_text_cstr(handle, row, col);
    if (!text) {
        return rt_string_new(NULL, 0);
    }
    return rt_string_new((const uint8_t*)text, (uint64_t)strlen(text));
}

int64_t rt_db_delete(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    int64_t result = db_delete_cstr(handle, pk ? pk : "");
    free(pk);
    return result;
}

int64_t rt_db_put_row3(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len,
                       int64_t type_mask, int64_t v0, int64_t v1, int64_t v2) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    int64_t result = db_put_row3_cstr(handle, pk ? pk : "", type_mask, v0, v1, v2);
    free(pk);
    return result;
}

int64_t rt_db_get_int_by_pk(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len,
                            int64_t col, int64_t default_val) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    int64_t result = db_get_int_by_pk_cstr(handle, pk ? pk : "", col, default_val);
    free(pk);
    return result;
}

int64_t rt_db_update_int(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len,
                         int64_t col, int64_t value) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    int64_t result = db_update_int_cstr(handle, pk ? pk : "", col, value);
    free(pk);
    return result;
}

int64_t rt_db_update_text(int64_t handle, const uint8_t* pk_ptr, int64_t pk_len,
                          int64_t col, const uint8_t* value_ptr, int64_t value_len) {
    char* pk = db_text_dup(pk_ptr, pk_len);
    char* value = db_text_dup(value_ptr, value_len);
    int64_t result = db_update_text_cstr(handle, pk ? pk : "", col, value ? value : "");
    free(pk);
    free(value);
    return result;
}
