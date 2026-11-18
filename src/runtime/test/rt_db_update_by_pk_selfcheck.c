/* Covers rt_db_update_int / rt_db_update_text / rt_db_get_int_by_pk: the
 * shared PK->live-row lookup behind the two update paths must keep returning
 * 0 for every miss and 1 for a hit. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t rt_db_table_create(const uint8_t*, int64_t, int64_t, int64_t);
extern int64_t rt_db_put_row3(int64_t, const uint8_t*, int64_t, int64_t, int64_t, int64_t, int64_t);
extern int64_t rt_db_get_int_by_pk(int64_t, const uint8_t*, int64_t, int64_t, int64_t);
extern int64_t rt_db_update_int(int64_t, const uint8_t*, int64_t, int64_t, int64_t);
extern int64_t rt_db_update_text(int64_t, const uint8_t*, int64_t, int64_t, const uint8_t*, int64_t);
extern int64_t rt_db_delete(int64_t, const uint8_t*, int64_t);

/* runtime_db.c only needs rt_string_new for rt_db_get_text, which is not exercised here. */
int64_t rt_string_new(const uint8_t* p, uint64_t n) { (void)p; return (int64_t)n; }

#define S(x) ((const uint8_t*)(x)), ((int64_t)strlen(x))
#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); return 1; } } while (0)

int main(void) {
    int64_t h = rt_db_table_create(S("upd"), 3, 0);
    CHECK(h >= 0);
    CHECK(rt_db_put_row3(h, S("k1"), 0, 10, 20, 0) >= 0);
    CHECK(rt_db_get_int_by_pk(h, S("k1"), 1, -7) == 20);
    CHECK(rt_db_update_int(h, S("k1"), 1, 99) == 1);
    CHECK(rt_db_get_int_by_pk(h, S("k1"), 1, -7) == 99);
    CHECK(rt_db_update_int(h, S("nope"), 1, 5) == 0);
    CHECK(rt_db_update_int(h, S("k1"), 9, 5) == 0);
    CHECK(rt_db_update_int(h, S("k1"), -1, 5) == 0);
    CHECK(rt_db_update_int(-1, S("k1"), 1, 5) == 0);
    CHECK(rt_db_update_int(1000000, S("k1"), 1, 5) == 0);
    CHECK(rt_db_update_text(h, S("k1"), 1, S("abc")) == 1);
    CHECK(rt_db_get_int_by_pk(h, S("k1"), 1, -7) == -7);
    CHECK(rt_db_update_text(h, S("nope"), 1, S("x")) == 0);
    CHECK(rt_db_update_text(h, S("k1"), 9, S("x")) == 0);
    CHECK(rt_db_update_text(-1, S("k1"), 1, S("x")) == 0);
    CHECK(rt_db_update_int(h, S("k1"), 1, 3) == 1);
    CHECK(rt_db_get_int_by_pk(h, S("k1"), 1, -7) == 3);
    CHECK(rt_db_delete(h, S("k1")) != 0);
    CHECK(rt_db_update_int(h, S("k1"), 1, 5) == 0);
    CHECK(rt_db_update_text(h, S("k1"), 1, S("x")) == 0);
    printf("PASS rt_db_update_by_pk\n");
    return 0;
}
