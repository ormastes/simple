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

static inline RtValue from_int(int64_t v) { return (uint64_t)v << 3; }
static inline int64_t as_int(RtValue v) { return v >> 3; }
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

static const char *get_string(RtValue v) {
    if (is_nil(v)) return NULL;
    if ((v & TAG_MASK) == TAG_HEAP) return (const char *)rt_string_data((int64_t)v);
    return NULL;
}

/* ================================================================
 * rt_sqlite_* implementations
 * ================================================================ */

RtValue rt_sqlite_open(RtValue path) {
    const char *p = get_string(path);
    if (!p) return (RtValue)SPECIAL_NIL;
    sqlite3 *db = NULL;
    int rc = sqlite3_open(p, &db);
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

RtValue rt_sqlite_close(RtValue handle) {
    if (is_nil(handle)) return from_int(1);
    sqlite3 *db = (sqlite3 *)as_ptr(handle);
    int rc = sqlite3_close(db);
    return from_int(rc == SQLITE_OK ? 0 : 1);
}

RtValue rt_sqlite_execute(RtValue conn, RtValue sql) {
    if (is_nil(conn)) return from_int(-1);
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    const char *s = get_string(sql);
    if (!s) return from_int(-1);
    char *err = NULL;
    int rc = sqlite3_exec(db, s, NULL, NULL, &err);
    if (err) sqlite3_free(err);
    return from_int(rc == SQLITE_OK ? 0 : -1);
}

RtValue rt_sqlite_execute_batch(RtValue conn, RtValue sql) {
    return rt_sqlite_execute(conn, sql);
}

RtValue rt_sqlite_query(RtValue conn, RtValue sql) {
    if (is_nil(conn)) return (RtValue)SPECIAL_NIL;
    sqlite3 *db = (sqlite3 *)as_ptr(conn);
    const char *s = get_string(sql);
    if (!s) return (RtValue)SPECIAL_NIL;
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, s, -1, &stmt, NULL);
    if (rc != SQLITE_OK || !stmt) return (RtValue)SPECIAL_NIL;
    return from_ptr(stmt);
}

RtValue rt_sqlite_query_next(RtValue stmt_val) {
    if (is_nil(stmt_val)) return (RtValue)SPECIAL_FALSE;
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_step(stmt);
    return (rc == SQLITE_ROW) ? (RtValue)SPECIAL_TRUE : (RtValue)SPECIAL_FALSE;
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
    const char *s = get_string(sql);
    if (!s) return (RtValue)SPECIAL_NIL;
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, s, -1, &stmt, NULL);
    if (rc != SQLITE_OK || !stmt) return (RtValue)SPECIAL_NIL;
    return from_ptr(stmt);
}

RtValue rt_sqlite_bind_text(RtValue stmt_val, RtValue idx, RtValue value) {
    if (is_nil(stmt_val)) return from_int(-1);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    const char *s = get_string(value);
    int rc = sqlite3_bind_text(stmt, (int)as_int(idx), s ? s : "", -1, SQLITE_TRANSIENT);
    return from_int(rc == SQLITE_OK ? 0 : -1);
}

RtValue rt_sqlite_bind_int(RtValue stmt_val, RtValue idx, RtValue value) {
    if (is_nil(stmt_val)) return from_int(-1);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_bind_int64(stmt, (int)as_int(idx), as_int(value));
    return from_int(rc == SQLITE_OK ? 0 : -1);
}

RtValue rt_sqlite_bind_float(RtValue stmt_val, RtValue idx, double value) {
    if (is_nil(stmt_val)) return from_int(-1);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_bind_double(stmt, (int)as_int(idx), value);
    return from_int(rc == SQLITE_OK ? 0 : -1);
}

RtValue rt_sqlite_bind_null(RtValue stmt_val, RtValue idx) {
    if (is_nil(stmt_val)) return from_int(-1);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_bind_null(stmt, (int)as_int(idx));
    return from_int(rc == SQLITE_OK ? 0 : -1);
}

RtValue rt_sqlite_reset(RtValue stmt_val) {
    if (is_nil(stmt_val)) return from_int(-1);
    sqlite3_stmt *stmt = (sqlite3_stmt *)as_ptr(stmt_val);
    int rc = sqlite3_reset(stmt);
    return from_int(rc == SQLITE_OK ? 0 : -1);
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
