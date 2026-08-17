/*
 * SQLite3 Runtime Binding for Simple Native Builds
 *
 * Provides rt_sqlite_* extern functions that the Simple database module
 * declares in sqlite_sffi.spl. Wraps libsqlite3 with the Simple runtime's
 * tagged value format.
 *
 * Build: cc -c -fPIC -O2 runtime_sqlite.c -o runtime_sqlite.o
 * Link:  -lsqlite3
 */

#include "runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <sqlite3.h>

/* Tagged value helpers — must match runtime.h / runtime_native.c */
#define TAG_MASK     0x7ULL
#define TAG_INT      0x0ULL
#define TAG_HEAP     0x1ULL
#define TAG_SPECIAL  0x3ULL
#define SPECIAL_NIL  3ULL   /* 0 << 3 | 0b011 */
#define SPECIAL_TRUE 11ULL  /* 1 << 3 | 0b011 */
#define SPECIAL_FALSE 19ULL /* 2 << 3 | 0b011 */

typedef int64_t RtValue;

/*
 * Integers cross this boundary RAW, not tagged (measured 2026-08-17, the first
 * time any lane actually linked this file into an AOT `--native` binary).
 *
 * `sqlite_sffi.spl` declares these entry points as `extern fn ... -> i64` /
 * `(idx: i64)`, and the native codegen passes and receives plain machine
 * integers for such a declaration -- it applies no tagging to a declared
 * extern's scalar arguments or return value. The original `v << 3` / `v >> 3`
 * helpers therefore corrupted every integer in both directions, e.g.
 * `rt_sqlite_column_count` returning 1 was read by Simple as 8 and
 * `rt_sqlite_query_next` returning SPECIAL_TRUE was read as 11 rather than 1,
 * so `while has_row == 1` never entered and every query returned zero rows.
 * This was invisible until now because the interpreter's `rt_sqlite_*`
 * emulation (interpreter_extern/sffi_db.rs) is untagged and never ran this C.
 *
 * Pointer and string values are NOT affected and keep their tagging: those
 * cross as heap handles (`from_ptr`/`make_string`) whose representation the
 * runtime and Simple already agree on -- `rt_sqlite_column_text` was returning
 * correct text throughout.
 */
static inline RtValue from_int(int64_t v) { return v; }
static inline int64_t as_int(RtValue v) { return v; }
static inline RtValue from_ptr(void *p) { return (RtValue)((uintptr_t)p | TAG_HEAP); }
static inline void *as_ptr(RtValue v) { return (void *)((uintptr_t)v & ~TAG_MASK); }
static inline int is_nil(RtValue v) { return v == (RtValue)SPECIAL_NIL; }

static uint64_t c_string_len(const char *s) {
    uint64_t len = 0;
    while (s[len] != '\0') len++;
    return len;
}

static RtValue make_string(const char *s) {
    if (!s) return (RtValue)SPECIAL_NIL;
    return (RtValue)rt_string_new((const uint8_t *)s, c_string_len(s));
}

/*
 * Simple's rt_string is (data, len) and its payload is NOT guaranteed to be
 * NUL-terminated. Every sqlite3 entry point below takes a C string, so
 * handing it rt_string_data() directly makes sqlite read past the end of the
 * payload into whatever follows it on the heap.
 *
 * That is not theoretical. Measured 2026-08-17 (lane W12-A) in an AOT
 * --native binary: rt_sqlite_begin/rollback pass make_string("BEGIN") /
 * make_string("ROLLBACK") and sqlite reported
 *     near "BEGINX": syntax error
 *     near "ROLLBACK\xef\xbf\xbd\xef\xbf\xbdS\xef\xbf\xbdX": syntax error
 * — the literal plus trailing heap garbage. Whether it fails depends purely
 * on the byte that happens to follow the allocation, which is why the same
 * primitive sequence looked correct when run standalone and failed inside
 * store_open(): a failed ROLLBACK leaves the transaction open, so every
 * later BEGIN dies with "cannot start a transaction within a transaction"
 * and enterprise_store's probe_backend_acid() honestly reported acid=false.
 *
 * borrow_string() therefore copies the payload into a NUL-terminated buffer.
 * Callers must release it with release_string(). rt_string_len() is the
 * authority on length; the payload may legitimately contain no NUL at all.
 */
typedef struct { char *ptr; char inline_buf[128]; } CStr;

static const char *borrow_string(RtValue v, CStr *out) {
    out->ptr = NULL;
    if (is_nil(v)) return NULL;
    if ((v & TAG_MASK) != TAG_HEAP) return NULL;
    const uint8_t *data = rt_string_data((int64_t)v);
    if (!data) return NULL;
    int64_t len = rt_string_len((int64_t)v);
    if (len < 0) return NULL;
    char *buf = out->inline_buf;
    if ((uint64_t)len + 1 > sizeof(out->inline_buf)) {
        buf = (char *)malloc((size_t)len + 1);
        if (!buf) return NULL;
        out->ptr = buf;
    }
    for (int64_t i = 0; i < len; i++) buf[i] = (char)data[i];
    buf[len] = '\0';
    return buf;
}

static void release_string(CStr *s) {
    if (s->ptr) { free(s->ptr); s->ptr = NULL; }
}

/* ================================================================
 * rt_sqlite_* implementations
 * ================================================================ */

RtValue rt_sqlite_open(RtValue path) {
    CStr pbuf;
    const char *p = borrow_string(path, &pbuf);
    if (!p) return (RtValue)SPECIAL_NIL;
    sqlite3 *db = NULL;
    int rc = sqlite3_open(p, &db);
    release_string(&pbuf);
    if (rc != SQLITE_OK) {
        if (db) sqlite3_close(db);
        return (RtValue)SPECIAL_NIL;
    }
    return from_ptr(db);
}

RtValue rt_sqlite_open_memory(void) {
    sqlite3 *db = NULL;
    int rc = sqlite3_open(":memory:", &db);
    if (rc != SQLITE_OK) {
        if (db) sqlite3_close(db);
        return (RtValue)SPECIAL_NIL;
    }
    return from_ptr(db);
}

/*
 * Return-code contract for all boolean-status rt_sqlite_* functions below
 * (close, execute, execute_batch, bind_*, reset, begin/commit/rollback):
 * 1 = success, 0 = failure. This matches the Rust seed's convention
 * (src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs) and the
 * Simple-side wrapper (src/lib/nogc_sync_mut/io/sqlite_sffi.spl), which
 * checks `result == 1` uniformly. Do NOT reintroduce sqlite3's native
 * SQLITE_OK==0 polarity here — that was the source of a three-way
 * contract mismatch (doc/08_tracking/bug, defect 2, 2026-08-08) where this
 * file returned 0 for success while the seed and the Simple wrapper both
 * expect 1 for success.
 */
RtValue rt_sqlite_close(RtValue handle) {
    if (is_nil(handle)) return from_int(1);
    sqlite3 *db = (sqlite3 *)as_ptr(handle);
    int rc = sqlite3_close(db);
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

RtValue rt_sqlite_execute(RtValue conn, RtValue sql) {
    if (is_nil(conn)) return from_int(0);
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    CStr sbuf;
    const char *s = borrow_string(sql, &sbuf);
    if (!s) return from_int(0);
    char *err = NULL;
    int rc = sqlite3_exec(db, s, NULL, NULL, &err);
    if (err) sqlite3_free(err);
    release_string(&sbuf);
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

RtValue rt_sqlite_execute_batch(RtValue conn, RtValue sql) {
    return rt_sqlite_execute(conn, sql);
}

RtValue rt_sqlite_query(RtValue conn, RtValue sql) {
    if (is_nil(conn)) return (RtValue)SPECIAL_NIL;
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    CStr sbuf;
    const char *s = borrow_string(sql, &sbuf);
    if (!s) return (RtValue)SPECIAL_NIL;
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, s, -1, &stmt, NULL);
    release_string(&sbuf);
    if (rc != SQLITE_OK || !stmt) return (RtValue)SPECIAL_NIL;
    return from_ptr(stmt);
}

RtValue rt_sqlite_query_next(RtValue stmt_val) {
    /* `sqlite_query_all` tests `has_row == 1`, so this returns a raw 1/0 rather
       than SPECIAL_TRUE/SPECIAL_FALSE (11/19). See the from_int note above. */
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_step(stmt);
    return from_int(rc == SQLITE_ROW ? 1 : 0);
}

void rt_sqlite_query_done(RtValue stmt_val) {
    if (is_nil(stmt_val)) return;
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    sqlite3_finalize(stmt);
}

RtValue rt_sqlite_column_count(RtValue stmt_val) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    return from_int(sqlite3_column_count(stmt));
}

RtValue rt_sqlite_column_name(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return (RtValue)SPECIAL_NIL;
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    const char *name = sqlite3_column_name(stmt, (int)as_int(idx));
    return make_string(name);
}

RtValue rt_sqlite_column_text(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return (RtValue)SPECIAL_NIL;
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    const char *text = (const char *)sqlite3_column_text(stmt, (int)as_int(idx));
    return make_string(text);
}

RtValue rt_sqlite_column_int(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    return from_int(sqlite3_column_int64(stmt, (int)as_int(idx)));
}

double rt_sqlite_column_float(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return 0.0;
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    return sqlite3_column_double(stmt, (int)as_int(idx));
}

RtValue rt_sqlite_column_type(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return make_string("null");
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int type = sqlite3_column_type(stmt, (int)as_int(idx));
    switch (type) {
        case SQLITE_INTEGER: return make_string("integer");
        case SQLITE_FLOAT:   return make_string("real");
        case SQLITE_TEXT:    return make_string("text");
        case SQLITE_BLOB:    return make_string("blob");
        default:             return make_string("null");
    }
}

RtValue rt_sqlite_prepare(RtValue conn, RtValue sql) {
    if (is_nil(conn)) return (RtValue)SPECIAL_NIL;
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    CStr sbuf;
    const char *s = borrow_string(sql, &sbuf);
    if (!s) return (RtValue)SPECIAL_NIL;
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, s, -1, &stmt, NULL);
    release_string(&sbuf);
    if (rc != SQLITE_OK || !stmt) return (RtValue)SPECIAL_NIL;
    return from_ptr(stmt);
}

RtValue rt_sqlite_bind_text(RtValue stmt_val, RtValue idx, RtValue value) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    CStr vbuf;
    const char *s = borrow_string(value, &vbuf);
    /* SQLITE_TRANSIENT: sqlite copies immediately, so releasing right after
       the call is safe. */
    int rc = sqlite3_bind_text(stmt, (int)as_int(idx), s ? s : "", -1, SQLITE_TRANSIENT);
    release_string(&vbuf);
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

RtValue rt_sqlite_bind_int(RtValue stmt_val, RtValue idx, RtValue value) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_bind_int64(stmt, (int)as_int(idx), as_int(value));
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

RtValue rt_sqlite_bind_float(RtValue stmt_val, RtValue idx, double value) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_bind_double(stmt, (int)as_int(idx), value);
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

RtValue rt_sqlite_bind_null(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_bind_null(stmt, (int)as_int(idx));
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

RtValue rt_sqlite_reset(RtValue stmt_val) {
    if (is_nil(stmt_val)) return from_int(0);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_reset(stmt);
    return from_int(rc == SQLITE_OK ? 1 : 0);
}

void rt_sqlite_finalize(RtValue stmt_val) {
    if (is_nil(stmt_val)) return;
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    sqlite3_finalize(stmt);
}

RtValue rt_sqlite_begin(RtValue conn) {
    return rt_sqlite_execute(conn, make_string("BEGIN"));
}

RtValue rt_sqlite_commit(RtValue conn) {
    return rt_sqlite_execute(conn, make_string("COMMIT"));
}

RtValue rt_sqlite_rollback(RtValue conn) {
    return rt_sqlite_execute(conn, make_string("ROLLBACK"));
}

RtValue rt_sqlite_last_insert_rowid(RtValue conn) {
    if (is_nil(conn)) return from_int(0);
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    return from_int(sqlite3_last_insert_rowid(db));
}

RtValue rt_sqlite_changes(RtValue conn) {
    if (is_nil(conn)) return from_int(0);
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    return from_int(sqlite3_changes(db));
}

RtValue rt_sqlite_error_message(RtValue conn) {
    if (is_nil(conn)) return make_string("null connection");
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    return make_string(sqlite3_errmsg(db));
}
