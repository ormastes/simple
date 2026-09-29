/* Link the real SQLite provider against the admitted Rust runtime owner.
 * This test never interprets a runtime string's header as the C layout. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t rt_sqlite_open_memory(void);
extern int64_t rt_sqlite_close(int64_t);
extern int64_t rt_sqlite_execute(int64_t, int64_t);
extern int64_t rt_sqlite_prepare(int64_t, int64_t);
extern int64_t rt_sqlite_bind_text(int64_t, int64_t, int64_t);
extern int64_t rt_sqlite_bind_int(int64_t, int64_t, int64_t);
extern int64_t rt_sqlite_query(int64_t, int64_t);
extern int64_t rt_sqlite_query_next(int64_t);
extern int64_t rt_sqlite_column_count(int64_t);
extern int64_t rt_sqlite_column_text(int64_t, int64_t);
extern int64_t rt_sqlite_column_int(int64_t, int64_t);
extern void rt_sqlite_finalize(int64_t);
extern void rt_sqlite_query_done(int64_t);

#define REQUIRE(check) do { if (!(check)) { fprintf(stderr, "SQLite owner check failed at line %d: %s\n", __LINE__, #check); return 1; } } while (0)
static int64_t text(const char* bytes) {
    return rt_string_new((const uint8_t*)bytes, (uint64_t)strlen(bytes));
}

int main(void) {
    int64_t db = rt_sqlite_open_memory();
    REQUIRE(db != 3);
    REQUIRE(rt_sqlite_execute(db, text("CREATE TABLE t(s TEXT, n INTEGER)")) == 1);
    int64_t statement = rt_sqlite_prepare(db, text("INSERT INTO t VALUES (?1, ?2)"));
    REQUIRE(statement != 3);
    /* UTF-8 owner bytes have no implicit terminator; embedded NUL keeps the
     * existing provider's C-string prefix semantics and bounded copy. */
    const uint8_t utf8[] = {0xce, 0xb1, 0xe7, 0xaa, 0x97, 0, 't', 'a', 'i', 'l'};
    int64_t owner_text = rt_string_new(utf8, sizeof(utf8));
    REQUIRE(rt_sqlite_bind_text(statement, 1, owner_text) == 1);
    REQUIRE(rt_sqlite_bind_int(statement, 2, -123456789) == 1);
    REQUIRE(rt_sqlite_query_next(statement) == 0);
    rt_sqlite_finalize(statement);
    statement = rt_sqlite_query(db, text("SELECT s,n FROM t"));
    REQUIRE(statement != 3);
    REQUIRE(rt_sqlite_query_next(statement) == 1);
    REQUIRE(rt_sqlite_column_count(statement) == 2);
    owner_text = rt_sqlite_column_text(statement, 0);
    REQUIRE(rt_string_len(owner_text) == 5);
    REQUIRE(memcmp(rt_string_data(owner_text), utf8, 5) == 0);
    REQUIRE(rt_sqlite_column_int(statement, 1) == -123456789);
    REQUIRE(rt_sqlite_query_next(statement) == 0);
    rt_sqlite_query_done(statement);
    REQUIRE(rt_sqlite_close(db) == 1);
    puts("SQLite bounded Rust owner ABI PASS");
    return 0;
}
