/* Focused core-C collection capture contract; compile with runtime_native.c. */
#include "runtime.h"
#include <assert.h>
#include <stdint.h>
#include <string.h>

static int64_t str(const char* value) {
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
}

int main(void) {
    int64_t target = str("x86_64-v3");
    int64_t site = str("ast://capture/selfcheck#1");
    int64_t wrong = str("other-target");
    assert(rt_collection_capture_note_lookup(site, target, 1) == 1);
    assert(rt_collection_capture_begin(target) == 1);
    assert(rt_collection_capture_begin(target) == 0);
    assert(rt_collection_capture_note_size(site, target, 2) == 1);
    assert(rt_collection_capture_note_lookup(site, wrong, 1) == 1);
    assert(rt_collection_capture_note_lookup(site, target, 1) == 1);
    assert(rt_collection_capture_note_lookup(site, target, 0) == 1);
    assert(rt_collection_capture_note_hash_probe(site, wrong, 10, 9) == 1);
    assert(rt_collection_capture_note_hash_probe(site, target, 3, 1) == 1);
    assert(rt_collection_capture_note_hash_probe(site, target, 1, 0) == 1);
    assert(rt_collection_capture_note_materialization(site, wrong) == 1);
    assert(rt_collection_capture_note_materialization(site, target) == 1);
    assert(rt_collection_capture_note_materialization(site, target) == 1);
    assert(rt_collection_capture_note_size(site, target, 0) == 1);
    const char* body = rt_interp_cstr(rt_collection_capture_finish());
    assert(body && strstr(body, "site=ast://capture/selfcheck#1") != 0);
    assert(strstr(body, "size_p95=2;lookup_p95=2;hits_p95=1;misses_p95=1") != 0);
    assert(strstr(body, "metric;sample=1;site=ast://capture/selfcheck#1;target=x86_64-v3;name=collection_size;value=2") != 0);
    assert(strstr(body, "metric;sample=2;site=ast://capture/selfcheck#1;target=x86_64-v3;name=lookup_count;value=2") != 0);
    assert(strstr(body, "metric;sample=3;site=ast://capture/selfcheck#1;target=x86_64-v3;name=distinct_key_count;value=0") != 0);
    assert(strstr(body, "metric;sample=4;site=ast://capture/selfcheck#1;target=x86_64-v3;name=materialization_count;value=2") != 0);
    assert(strstr(body, "metric;sample=5;site=ast://capture/selfcheck#1;target=x86_64-v3;name=hash_probe_count;value=4") != 0);
    assert(strstr(body, "metric;sample=6;site=ast://capture/selfcheck#1;target=x86_64-v3;name=hash_collision_count;value=1") != 0);
    assert(rt_collection_capture_begin(target) == 1);
    assert(rt_collection_capture_note_hash_probe(site, target, 1, 2) == 0);
    assert(rt_collection_capture_finish() == rt_value_nil());
    assert(rt_collection_capture_begin(target) == 1);
    assert(rt_collection_capture_note_size(site, target, 1) == 1);
    body = rt_interp_cstr(rt_collection_capture_finish());
    assert(body && strstr(body, "name=collection_size;value=1") != 0);
    assert(strstr(body, "name=hash_probe_count") == 0);
    assert(strstr(body, "name=hash_collision_count") == 0);
    assert(rt_collection_capture_begin(target) == 1);
    assert(rt_collection_capture_abort() == 1);
    assert(rt_collection_capture_begin(target) == 1);
    body = rt_interp_cstr(rt_collection_capture_finish());
    assert(body && body[0] == '\0');
    return 0;
}
