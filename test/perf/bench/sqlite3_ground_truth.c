/* Ground-truth SQLite3 benchmark — same workloads as compiled_db_baseline_spec.spl
 * Compile: gcc -O2 -o sqlite3_bench sqlite3_ground_truth.c -lsqlite3
 * Run:     ./sqlite3_bench
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sqlite3.h>

static long long now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static void exec(sqlite3 *db, const char *sql) {
    char *err = NULL;
    if (sqlite3_exec(db, sql, NULL, NULL, &err) != SQLITE_OK) {
        fprintf(stderr, "SQL error: %s\n", err);
        sqlite3_free(err);
        exit(1);
    }
}

static void bench_w1_insert_200(void) {
    sqlite3 *db;
    sqlite3_open(":memory:", &db);
    exec(db, "CREATE TABLE w1 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)");
    exec(db, "BEGIN");

    long long t0 = now_ns();
    char sql[256];
    for (int i = 0; i < 200; i++) {
        snprintf(sql, sizeof(sql),
            "INSERT INTO w1 (id, name, score) VALUES (%d, 'user_%d', %d)",
            i, i, i * 10);
        exec(db, sql);
    }
    exec(db, "COMMIT");
    long long t1 = now_ns();

    printf("[W1] INSERT 200 (SQLite, deferred): %lld us (%.3f ms)\n",
           (t1-t0)/1000, (t1-t0)/1000000.0);
    sqlite3_close(db);
}

static void bench_w1_insert_200_prepared(void) {
    sqlite3 *db;
    sqlite3_open(":memory:", &db);
    exec(db, "CREATE TABLE w1p (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)");
    exec(db, "BEGIN");

    sqlite3_stmt *stmt;
    sqlite3_prepare_v2(db,
        "INSERT INTO w1p (id, name, score) VALUES (?, ?, ?)", -1, &stmt, NULL);

    long long t0 = now_ns();
    char name[64];
    for (int i = 0; i < 200; i++) {
        snprintf(name, sizeof(name), "user_%d", i);
        sqlite3_bind_int(stmt, 1, i);
        sqlite3_bind_text(stmt, 2, name, -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 3, i * 10);
        sqlite3_step(stmt);
        sqlite3_reset(stmt);
    }
    exec(db, "COMMIT");
    long long t1 = now_ns();

    printf("[W1p] INSERT 200 (SQLite, prepared): %lld us (%.3f ms)\n",
           (t1-t0)/1000, (t1-t0)/1000000.0);
    sqlite3_finalize(stmt);
    sqlite3_close(db);
}

static void bench_w2_point_select_100(void) {
    sqlite3 *db;
    sqlite3_open(":memory:", &db);
    exec(db, "CREATE TABLE w2 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)");
    exec(db, "BEGIN");
    char sql[256];
    for (int i = 0; i < 200; i++) {
        snprintf(sql, sizeof(sql),
            "INSERT INTO w2 (id, name, score) VALUES (%d, 'user_%d', %d)",
            i, i, i * 10);
        exec(db, sql);
    }
    exec(db, "COMMIT");

    /* Unprepared — like Simple DB SQL path */
    long long t0 = now_ns();
    for (int j = 0; j < 100; j++) {
        int idx = j * 2;
        snprintf(sql, sizeof(sql),
            "SELECT id, name, score FROM w2 WHERE id = %d", idx);
        sqlite3_stmt *stmt;
        sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);
        sqlite3_step(stmt);
        sqlite3_finalize(stmt);
    }
    long long t1 = now_ns();
    printf("[W2] Point SELECT x100 (SQLite, unprepared): %lld us (%.3f ms)\n",
           (t1-t0)/1000, (t1-t0)/1000000.0);

    /* Prepared — like Simple DB direct API */
    sqlite3_stmt *pstmt;
    sqlite3_prepare_v2(db,
        "SELECT id, name, score FROM w2 WHERE id = ?", -1, &pstmt, NULL);
    long long t2 = now_ns();
    for (int j = 0; j < 100; j++) {
        int idx = j * 2;
        sqlite3_bind_int(pstmt, 1, idx);
        sqlite3_step(pstmt);
        sqlite3_reset(pstmt);
    }
    long long t3 = now_ns();
    printf("[W2p] Point SELECT x100 (SQLite, prepared): %lld us (%.3f ms)\n",
           (t3-t2)/1000, (t3-t2)/1000000.0);

    sqlite3_finalize(pstmt);
    sqlite3_close(db);
}

static void bench_w3_range_scan_100(void) {
    sqlite3 *db;
    sqlite3_open(":memory:", &db);
    exec(db, "CREATE TABLE w3 (id INTEGER PRIMARY KEY, name TEXT)");
    exec(db, "BEGIN");
    char sql[256];
    for (int i = 0; i < 200; i++) {
        snprintf(sql, sizeof(sql),
            "INSERT INTO w3 (id, name) VALUES (%d, 'user_%d')", i, i);
        exec(db, sql);
    }
    exec(db, "COMMIT");

    /* Unprepared */
    long long t0 = now_ns();
    for (int j = 0; j < 100; j++) {
        sqlite3_stmt *stmt;
        sqlite3_prepare_v2(db,
            "SELECT id, name FROM w3 WHERE id >= 50 AND id < 150",
            -1, &stmt, NULL);
        while (sqlite3_step(stmt) == SQLITE_ROW) { /* consume */ }
        sqlite3_finalize(stmt);
    }
    long long t1 = now_ns();
    printf("[W3] Range scan x100 (SQLite, unprepared): %lld us (%.3f ms)\n",
           (t1-t0)/1000, (t1-t0)/1000000.0);

    /* Prepared */
    sqlite3_stmt *pstmt;
    sqlite3_prepare_v2(db,
        "SELECT id, name FROM w3 WHERE id >= ? AND id < ?",
        -1, &pstmt, NULL);
    long long t2 = now_ns();
    for (int j = 0; j < 100; j++) {
        sqlite3_bind_int(pstmt, 1, 50);
        sqlite3_bind_int(pstmt, 2, 150);
        while (sqlite3_step(pstmt) == SQLITE_ROW) { /* consume */ }
        sqlite3_reset(pstmt);
    }
    long long t3 = now_ns();
    printf("[W3p] Range scan x100 (SQLite, prepared): %lld us (%.3f ms)\n",
           (t3-t2)/1000, (t3-t2)/1000000.0);

    sqlite3_finalize(pstmt);
    sqlite3_close(db);
}

static void bench_w7_bulk_insert_10k(void) {
    sqlite3 *db;
    sqlite3_open(":memory:", &db);
    exec(db, "CREATE TABLE w7 (id INTEGER PRIMARY KEY, name TEXT, score INTEGER)");

    sqlite3_stmt *stmt;
    sqlite3_prepare_v2(db,
        "INSERT INTO w7 (id, name, score) VALUES (?, ?, ?)", -1, &stmt, NULL);

    exec(db, "BEGIN");
    long long t0 = now_ns();
    char name[64];
    for (int i = 0; i < 10000; i++) {
        snprintf(name, sizeof(name), "user_%d", i);
        sqlite3_bind_int(stmt, 1, i);
        sqlite3_bind_text(stmt, 2, name, -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 3, i * 10);
        sqlite3_step(stmt);
        sqlite3_reset(stmt);
    }
    exec(db, "COMMIT");
    long long t1 = now_ns();

    printf("[W7] Bulk INSERT 10K (SQLite, prepared): %lld us (%.3f ms)\n",
           (t1-t0)/1000, (t1-t0)/1000000.0);
    sqlite3_finalize(stmt);
    sqlite3_close(db);
}

static void bench_w10_mixed_oltp(void) {
    sqlite3 *db;
    sqlite3_open(":memory:", &db);
    exec(db, "CREATE TABLE w10 (id INTEGER PRIMARY KEY, name TEXT)");
    exec(db, "BEGIN");
    char sql[256];
    for (int i = 0; i < 200; i++) {
        snprintf(sql, sizeof(sql),
            "INSERT INTO w10 (id, name) VALUES (%d, 'user_%d')", i, i);
        exec(db, sql);
    }
    exec(db, "COMMIT");

    sqlite3_stmt *sel_stmt, *upd_stmt;
    sqlite3_prepare_v2(db,
        "SELECT id, name FROM w10 WHERE id = ?", -1, &sel_stmt, NULL);
    sqlite3_prepare_v2(db,
        "UPDATE w10 SET name = ? WHERE id = ?", -1, &upd_stmt, NULL);

    long long t0 = now_ns();
    exec(db, "BEGIN");
    for (int i = 0; i < 1000; i++) {
        int key = i % 200;
        if (i % 5 == 0) {
            /* 20% writes */
            char name[64];
            snprintf(name, sizeof(name), "updated_%d", i);
            sqlite3_bind_text(upd_stmt, 1, name, -1, SQLITE_TRANSIENT);
            sqlite3_bind_int(upd_stmt, 2, key);
            sqlite3_step(upd_stmt);
            sqlite3_reset(upd_stmt);
        } else {
            /* 80% reads */
            sqlite3_bind_int(sel_stmt, 1, key);
            sqlite3_step(sel_stmt);
            sqlite3_reset(sel_stmt);
        }
    }
    exec(db, "COMMIT");
    long long t1 = now_ns();

    printf("[W10] Mixed OLTP 1K ops (SQLite, prepared): %lld us (%.3f ms)\n",
           (t1-t0)/1000, (t1-t0)/1000000.0);
    sqlite3_finalize(sel_stmt);
    sqlite3_finalize(upd_stmt);
    sqlite3_close(db);
}

int main(void) {
    printf("=== SQLite3 Ground-Truth Benchmark ===\n");
    printf("SQLite version: %s\n\n", sqlite3_libversion());

    bench_w1_insert_200();
    bench_w1_insert_200_prepared();
    bench_w2_point_select_100();
    bench_w3_range_scan_100();
    bench_w7_bulk_insert_10k();
    bench_w10_mixed_oltp();

    printf("\nDone.\n");
    return 0;
}
