/* Focused core-C collection capture contract; compile with runtime_native.c. */
#include "runtime.h"
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static int64_t str(const char* value) {
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
}

/* Runtime texts carry an explicit length; Rust-owned texts need not have a
 * trailing NUL. Only this test's finished output needs a C-string copy. */
static char* finish_text(void) {
    int64_t text = spl_collection_capture_finish();
    int64_t len = rt_string_len(text);
    const uint8_t* data = rt_string_data(text);
    assert(len >= 0 && (len == 0 || data != NULL));
    assert((uint64_t)len < SIZE_MAX);
    char* copy = (char*)malloc((size_t)len + 1);
    assert(copy != NULL);
    if (len) memcpy(copy, data, (size_t)len);
    copy[len] = '\0';
    return copy;
}

static size_t count_rows(int64_t text) {
    int64_t len = rt_string_len(text);
    const uint8_t* data = rt_string_data(text);
    assert(len >= 0 && (len == 0 || data != NULL));
    size_t rows = len == 0 ? 0 : 1;
    for (int64_t index = 0; index < len; index++) {
        if (data[index] == '\n') rows++;
    }
    return rows;
}

int main(void) {
    int64_t target = str("x86_64-v3");
    int64_t site = str("ast://capture/selfcheck#1");
    int64_t wrong = str("other-target");
    assert(spl_collection_capture_note_lookup(site, target, 1) == 1);
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_begin(target) == 0);
    assert(spl_collection_capture_note_size(site, target, 2) == 1);
    assert(spl_collection_capture_note_lookup(site, wrong, 1) == 1);
    assert(spl_collection_capture_note_lookup(site, target, 1) == 1);
    assert(spl_collection_capture_note_lookup(site, target, 0) == 1);
    assert(spl_collection_capture_note_hash_probe(site, wrong, 10, 9) == 1);
    assert(spl_collection_capture_note_hash_probe(site, target, 3, 1) == 1);
    assert(spl_collection_capture_note_hash_probe(site, target, 1, 0) == 1);
    assert(spl_collection_capture_note_filter(site, target, 3, 1) == 1);
    assert(spl_collection_capture_note_filter(site, target, 1, 1) == 1);
    assert(spl_collection_capture_note_loop(site, wrong, 100) == 1);
    assert(spl_collection_capture_note_loop(site, target, 3) == 1);
    assert(spl_collection_capture_note_loop(site, target, 2) == 1);
    assert(spl_collection_capture_note_materialization(site, wrong) == 1);
    assert(spl_collection_capture_note_materialization(site, target) == 1);
    assert(spl_collection_capture_note_materialization(site, target) == 1);
    assert(spl_collection_capture_note_size(site, target, 0) == 1);
    char* body = finish_text();
    assert(strstr(body, "name=loop_trip_count;value=5") != NULL);
    assert(body && strstr(body, "site=ast://capture/selfcheck#1") != 0);
    assert(strstr(body, "size_p95=2;lookup_p95=2;hits_p95=1;misses_p95=1") != 0);
    assert(strstr(body, "metric;sample=1;site=ast://capture/selfcheck#1;target=x86_64-v3;name=collection_size;value=2") != 0);
    assert(strstr(body, "metric;sample=2;site=ast://capture/selfcheck#1;target=x86_64-v3;name=lookup_count;value=2") != 0);
    assert(strstr(body, "metric;sample=3;site=ast://capture/selfcheck#1;target=x86_64-v3;name=distinct_key_count;value=0") != 0);
    assert(strstr(body, "metric;sample=4;site=ast://capture/selfcheck#1;target=x86_64-v3;name=materialization_count;value=2") != 0);
    assert(strstr(body, "metric;sample=5;site=ast://capture/selfcheck#1;target=x86_64-v3;name=hash_probe_count;value=4") != 0);
    assert(strstr(body, "metric;sample=6;site=ast://capture/selfcheck#1;target=x86_64-v3;name=hash_collision_count;value=1") != 0);
    assert(strstr(body, "metric;sample=7;site=ast://capture/selfcheck#1;target=x86_64-v3;name=filter_selectivity;value=500000") != 0);
    free(body);
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_hash_probe(site, target, 1, 2) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_size(site, target, 1) == 1);
    body = finish_text();
    assert(body && strstr(body, "name=collection_size;value=1") != 0);
    assert(strstr(body, "name=hash_probe_count") == 0);
    assert(strstr(body, "name=hash_collision_count") == 0);
    assert(strstr(body, "name=filter_selectivity") == 0);
    free(body);
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_filter(site, target, 0, 0) == 1);
    body = finish_text();
    assert(body && body[0] == '\0');
    free(body);
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_filter(site, target, 0, 1) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_filter(site, target, -1, 0) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_filter(site, target, INT64_MAX, INT64_MAX) == 1);
    assert(spl_collection_capture_note_filter(site, target, 1, 0) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());

    /* A completed empty loop is measured zero; an untouched site stays absent. */
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_size(site, target, 0) == 1);
    assert(spl_collection_capture_note_loop(site, target, 0) == 1);
    body = finish_text();
    assert(strstr(body, "name=loop_trip_count;value=0") != NULL);
    assert(count_rows(str(body)) == 6);
    free(body);
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_size(site, target, 1) == 1);
    body = finish_text();
    assert(strstr(body, "loop_trip_count") == NULL);
    free(body);
    /* Missing collection context, negative counts and overflow poison capture. */
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_loop(site, target, 0) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_size(site, target, 1) == 1);
    assert(spl_collection_capture_note_loop(site, target, -1) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_note_size(site, target, 1) == 1);
    assert(spl_collection_capture_note_loop(site, target, INT64_MAX) == 1);
    assert(spl_collection_capture_note_loop(site, target, 1) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());

    /* Exactly 12500 sites with hash and filter samples use all 100000 rows. */
    assert(spl_collection_capture_begin(target) == 1);
    for (int index = 0; index < 12500; index++) {
        char site_text[64];
        int len = snprintf(site_text, sizeof(site_text), "ast://capture/capacity/%d", index);
        assert(len > 0 && (size_t)len < sizeof(site_text));
        int64_t current_site = str(site_text);
        assert(spl_collection_capture_note_hash_probe(current_site, target, 1, 0) == 1);
        assert(spl_collection_capture_note_filter(current_site, target, 1, 1) == 1);
    }
    int64_t full_text = spl_collection_capture_finish();
    assert(full_text != rt_value_nil());
    assert(count_rows(full_text) == 100000);
    assert(spl_collection_capture_begin(target) == 1);
    for (int index = 0; index < 12500; index++) {
        char site_text[64];
        int len = snprintf(site_text, sizeof(site_text), "ast://capture/capacity/%d", index);
        assert(len > 0 && (size_t)len < sizeof(site_text));
        int64_t current_site = str(site_text);
        assert(spl_collection_capture_note_hash_probe(current_site, target, 1, 0) == 1);
        assert(spl_collection_capture_note_filter(current_site, target, 1, 1) == 1);
    }
    int64_t overflow_site = str("ast://capture/capacity/overflow");
    int64_t occupied_site = str("ast://capture/capacity/0");
    assert(spl_collection_capture_note_loop(occupied_site, target, 0) == 0);
    assert(spl_collection_capture_note_filter(overflow_site, target, 1, 1) == 0);
    assert(spl_collection_capture_finish() == rt_value_nil());
    assert(spl_collection_capture_begin(target) == 1);
    assert(spl_collection_capture_abort() == 1);
    assert(spl_collection_capture_begin(target) == 1);
    body = finish_text();
    assert(body && body[0] == '\0');
    free(body);
    return 0;
}
