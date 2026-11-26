/* Selfcheck for transient-scope traversal of persistent / multi-scope raw
 * `rt_alloc` blocks (bugs s3_binding_versions_keys_freed_transient_scope_2026-11-19
 * and stage2_sanity_reverse_reference_publish_refused_2026_10_22).
 *
 * Verifies:
 * 1) Pre-scope `rt_alloc` struct/class (e.g. `SymbolTable.scopes[0]`) inside a
 *    persistent `RtCoreDict` does NOT enter `rt_struct_allocs`
 *    (`rt_struct_receiver_valid == 0`), yet IS traversed by
 *    `rt_transient_heap_promote(table_scopes)` so transient keys (including
 *    first-inserted keys retained across unbind/rebind tombstones in
 *    `Scope(0).binding_versions_v1`) survive scope end and heap churn.
 * 2) Tagged (`ptr | 1`) and untagged (`ptr`) persistent `rt_alloc` roots promote
 *    themselves and their children across single and repeated scopes.
 * 3) Mixed scalar+array inline class (`ReverseReferenceModuleBatchV1`-shaped
 *    8-word block) created inside a transient scope starts zeroed, survives
 *    promotion via paused-scope `Some(batch)` (`rt_enum_new`) across Scope 1
 *    end AND across subsequent Scope 2 mutations + re-promotion.
 * 4) `rt_realloc` of a persistent pre-scope raw block preserves persistence,
 *    zero-fills growth bytes, and `rt_free` cleanly unregisters it.
 * 5) BSM `rt_transient_heap_adopt` traverses pre-scope raw `Scope(0)` to adopt
 *    its module-owned dictionary children into the session heap.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "../runtime.h"

extern int64_t rt_dict_keys(int64_t dict);
extern int64_t rt_string_free(int64_t value);
extern void* rt_realloc(void* ptr, int64_t size);
extern void rt_free(void* ptr);

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

static void churn_transient_heap(int rounds) {
    for (int r = 0; r < rounds; r++) {
        if (!rt_transient_array_scope_begin()) {
            failures++;
            return;
        }
        for (int i = 0; i < 64; i++) {
            char buf[48];
            int n = snprintf(buf, sizeof(buf), "churn_slot_%02d_%02d_overwrite", r, i);
            int64_t s = rt_string_new((const uint8_t*)buf, (uint64_t)n);
            int64_t* raw = (int64_t*)rt_alloc(64);
            if (!s || !raw) {
                failures++;
                rt_transient_array_scope_end();
                return;
            }
            raw[0] = (int64_t)0xdeadbeefcafebabeULL;
            raw[1] = s;
        }
        if (!rt_transient_array_scope_end()) {
            failures++;
            return;
        }
    }
}

static void test_prescope_binding_versions_root(void) {
    int64_t table_scopes = rt_dict_new(4);
    int64_t* scope0 = (int64_t*)rt_alloc((int64_t)(4 * sizeof(int64_t)));
    int64_t binding_versions = rt_dict_new(4);
    check(table_scopes != 0 && scope0 != NULL && binding_versions != 0,
          "pre-scope table_scopes, Scope(0), and binding_versions_v1 allocate");
    check(scope0[0] == 0 && scope0[1] == 0 && scope0[2] == 0 && scope0[3] == 0,
          "pre-scope rt_alloc block is zero-initialized");
    check(rt_struct_receiver_valid((int64_t)(uintptr_t)scope0, 0, 8) == 0,
          "pre-scope rt_alloc does not claim rt_struct_alloc receiver ownership");

    scope0[0] = 0;
    scope0[1] = binding_versions;
    check(rt_dict_set(table_scopes, 0, (int64_t)(uintptr_t)scope0) == 1,
          "table_scopes[0] stores pre-scope Scope(0)");

    /* Tagged pre-scope carrier dict checks both untagged and |1-tagged raw refs. */
    int64_t table_scopes_tagged = rt_dict_new(4);
    int64_t* scope1 = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    int64_t bv_tagged = rt_dict_new(4);
    scope1[0] = 8;
    scope1[1] = bv_tagged;
    check(rt_dict_set(table_scopes_tagged, 8, (int64_t)(((uintptr_t)scope1) | 1ULL)) == 1,
          "table_scopes_tagged stores |1-tagged pre-scope Scope(1)");

    check(rt_transient_array_scope_begin() == 1, "binding-versions scope begins");
    const char* key_lit = "alpha_binding_key_v1";
    const uint64_t key_len = (uint64_t)strlen(key_lit);
    int64_t o1 = rt_string_new((const uint8_t*)key_lit, key_len);
    int64_t o1_tag_sib = rt_string_new((const uint8_t*)"tagged_scope1_key_v1", 20);
    int64_t unreached_sib = rt_string_new((const uint8_t*)"unreached_transient_01", 22);
    check(rt_dict_set(binding_versions, o1, 1LL << 3) == 1,
          "binding_versions_v1 inserts first transient key o1");
    int64_t o2 = rt_string_new((const uint8_t*)key_lit, key_len);
    check(o2 != o1, "rebind builds a distinct transient string o2");
    check(rt_dict_set(binding_versions, o2, 2LL << 3) == 1,
          "rebind updates value while keeping first key o1 (core_dict_put_seq contract)");
    check(rt_dict_set(bv_tagged, o1_tag_sib, 3LL << 3) == 1,
          "bv_tagged inserts transient key");

    check(rt_transient_array_scope_pause() == 1, "binding-versions scope pauses");
    /* Critical assertion: promote ONLY table_scopes (never binding_versions directly). */
    check(rt_transient_heap_promote(table_scopes) == 1,
          "promote(table_scopes) traverses pre-scope Scope(0) -> binding_versions_v1");
    check(rt_transient_heap_promote(table_scopes_tagged) == 1,
          "promote(table_scopes_tagged) traverses tagged pre-scope Scope(1)");
    check(rt_transient_array_scope_end() == 1, "binding-versions scope ends");

    churn_transient_heap(4);

    check(rt_string_free(unreached_sib) == 0,
          "control: unpromoted transient string was reclaimed at scope end");
    int64_t keys = rt_dict_keys(binding_versions);
    check(keys != 0 && rt_array_len((SplArray*)(uintptr_t)keys) == 1,
          "binding_versions_v1 retains exactly 1 live key after scope end");
    int64_t kept_key = rt_array_get((SplArray*)(uintptr_t)keys, 0);
    check(kept_key == o1 && rt_string_len(kept_key) == (int64_t)key_len &&
              memcmp(rt_string_data(kept_key), key_lit, key_len) == 0,
          "retained binding_versions_v1 key preserves first-key handle and bytes");

    int64_t probe_lookup = rt_string_new((const uint8_t*)key_lit, key_len);
    check(rt_dict_get(binding_versions, probe_lookup) == (2LL << 3),
          "binding_versions_v1 lookup returns rebound version 2 after churn");

    int64_t tagged_keys = rt_dict_keys(bv_tagged);
    int64_t kept_tagged_key = rt_array_get((SplArray*)(uintptr_t)tagged_keys, 0);
    check(kept_tagged_key == o1_tag_sib && rt_string_len(kept_tagged_key) == 20 &&
              memcmp(rt_string_data(kept_tagged_key), "tagged_scope1_key_v1", 20) == 0,
          "tagged pre-scope raw child retains its transient dict key");

    rt_free(scope0);
    rt_free(scope1);
}

static void test_mixed_scalar_array_batch_and_multiscope(void) {
    check(rt_transient_array_scope_begin() == 1, "batch Scope 1 begins");

    /* 8-word mixed scalar+array class mirroring ReverseReferenceModuleBatchV1:
     * [0]=token, [1]=generation, [2]=sealed, [3]=valid,
     * [4]=facts, [5]=known_families, [6]=incomplete_families, [7]=aliases */
    int64_t* batch = (int64_t*)rt_alloc((int64_t)(8 * sizeof(int64_t)));
    check(batch != NULL, "Scope 1 batch class allocates");
    int all_zero = 1;
    for (int i = 0; i < 8; i++) {
        if (batch[i] != 0) all_zero = 0;
    }
    check(all_zero, "Scope 1 batch rt_alloc is zero-initialized");

    SplArray* facts = rt_array_new(4);
    SplArray* known = rt_array_new(4);
    SplArray* incomplete = rt_array_new(4);
    SplArray* aliases = rt_array_new(4);
    int64_t fam1 = rt_string_new((const uint8_t*)"compiler.common.cache", 21);
    int64_t inc1 = rt_string_new((const uint8_t*)"compiler.incomplete", 19);
    int64_t* alias_row = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    alias_row[0] = rt_string_new((const uint8_t*)"alias_ident_v1", 14);
    alias_row[1] = rt_string_new((const uint8_t*)"alias_src_path_v1", 17);

    check(rt_array_push(known, fam1) == 1 &&
              rt_array_push(incomplete, inc1) == 1 &&
              rt_array_push(aliases, (int64_t)(uintptr_t)alias_row) == 1,
          "Scope 1 batch array limbs populate");

    batch[0] = 1; /* token */
    batch[1] = 1; /* generation */
    batch[2] = 0; /* sealed */
    batch[3] = 1; /* valid */
    batch[4] = (int64_t)(uintptr_t)facts;
    batch[5] = (int64_t)(uintptr_t)known;
    batch[6] = (int64_t)(uintptr_t)incomplete;
    batch[7] = (int64_t)(uintptr_t)aliases;

    check(rt_transient_array_scope_pause() == 1, "batch Scope 1 pauses");
    batch[2] = 1; /* sealed = true before carrier wrap */
    /* Re-assign Option carrier while paused (exact reverse_reference_module_seal_v1 pattern). */
    int64_t carrier = rt_enum_new(1, 0, (int64_t)(uintptr_t)batch);
    check(carrier != 0, "paused Some(batch) enum allocates");
    check(rt_transient_heap_promote(carrier) == 1,
          "promote(Some(batch)) succeeds for mixed scalar+array raw batch");
    check(rt_transient_array_scope_end() == 1, "batch Scope 1 ends");

    churn_transient_heap(4);

    check(rt_enum_payload(carrier) == (int64_t)(uintptr_t)batch,
          "Some(batch) payload pointer survives Scope 1 end");
    check(batch[0] == 1 && batch[1] == 1 && batch[2] == 1 && batch[3] == 1,
          "mixed batch scalar limbs survive Scope 1 end intact");
    check(rt_array_len((SplArray*)(uintptr_t)batch[5]) == 1 &&
              rt_string_len(rt_array_get((SplArray*)(uintptr_t)batch[5], 0)) == 21 &&
              memcmp(rt_string_data(rt_array_get((SplArray*)(uintptr_t)batch[5], 0)),
                     "compiler.common.cache", 21) == 0,
          "mixed batch array limb and element text survive Scope 1 end");
    int64_t* kept_alias = (int64_t*)(uintptr_t)rt_array_get((SplArray*)(uintptr_t)batch[7], 0);
    check(kept_alias == alias_row &&
              rt_string_len(kept_alias[0]) == 14 &&
              memcmp(rt_string_data(kept_alias[0]), "alias_ident_v1", 14) == 0,
          "mixed batch nested raw alias struct survives Scope 1 end");

    /* Scope 2: mutate the Scope-1-promoted batch AFTER Scope 1 cleared its transient_raw table. */
    check(rt_transient_array_scope_begin() == 1, "batch Scope 2 begins");
    int64_t fam2 = rt_string_new((const uint8_t*)"compiler.scope2.fam", 19);
    check(rt_array_push(known, fam2) == 1,
          "Scope 2 appends transient string to Scope-1-promoted batch array limb");
    SplArray* scope2_facts = rt_array_new(2);
    int64_t fact2 = rt_string_new((const uint8_t*)"fact_from_scope2", 16);
    check(rt_array_push(scope2_facts, fact2) == 1, "Scope 2 allocates new facts array");
    batch[4] = (int64_t)(uintptr_t)scope2_facts;

    check(rt_transient_array_scope_pause() == 1, "batch Scope 2 pauses");
    check(rt_transient_heap_promote(carrier) == 1,
          "Scope 2 promote(Some(batch)) still classifies promoted Scope-1 batch");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)batch) == 1,
          "Scope 2 direct promote(batch) succeeds on persistent raw batch");
    check(rt_transient_array_scope_end() == 1, "batch Scope 2 ends");

    churn_transient_heap(4);

    check(rt_array_len(known) == 2 &&
              rt_string_len(rt_array_get(known, 1)) == 19 &&
              memcmp(rt_string_data(rt_array_get(known, 1)), "compiler.scope2.fam", 19) == 0,
          "Scope 2 string inside Scope-1 batch array survives Scope 2 end");
    check(rt_array_len((SplArray*)(uintptr_t)batch[4]) == 1 &&
              rt_string_len(rt_array_get((SplArray*)(uintptr_t)batch[4], 0)) == 16 &&
              memcmp(rt_string_data(rt_array_get((SplArray*)(uintptr_t)batch[4], 0)),
                     "fact_from_scope2", 16) == 0,
          "Scope 2 array assigned into Scope-1 batch survives Scope 2 end");

    rt_free(alias_row);
    rt_free(batch);
}

static void test_prescope_realloc_free_and_bsm_adopt(void) {
    /* Verify pre-scope rt_realloc preserves persistence, zeroes tail, and rt_free unregisters. */
    int64_t* buf = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    check(buf != NULL, "pre-scope buf allocates");
    buf[0] = 77;
    check(rt_transient_array_scope_begin() == 1, "realloc scope begins");
    buf = (int64_t*)rt_realloc(buf, (int64_t)(4 * sizeof(int64_t)));
    check(buf != NULL && buf[0] == 77 && buf[2] == 0 && buf[3] == 0,
          "pre-scope rt_realloc preserves prefix and zeroes growth tail");
    buf[2] = rt_string_new((const uint8_t*)"reallocated_child_v1", 20);
    check(rt_transient_array_scope_pause() == 1, "realloc scope pauses");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)buf) == 1,
          "promote walks resized pre-scope raw block");
    check(rt_transient_array_scope_end() == 1, "realloc scope ends");
    churn_transient_heap(2);
    check(buf[0] == 77 && rt_string_len(buf[2]) == 20 &&
              memcmp(rt_string_data(buf[2]), "reallocated_child_v1", 20) == 0,
          "resized pre-scope block and child survive scope end");

    rt_free(buf);
    check(rt_transient_array_scope_begin() == 1 && rt_transient_array_scope_pause() == 1,
          "freed-probe scope begins and pauses");
    check(rt_transient_heap_promote((int64_t)(((uintptr_t)buf) | 1ULL)) == 0,
          "freed persistent raw block is unregistered and refused as tagged root");
    check(rt_transient_array_scope_end() == 1, "freed-probe scope ends");

    /* BSM adopt + session promote through pre-scope Scope(0). */
    int64_t* legacy_scope0 = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    int64_t legacy_bv = rt_dict_new(4);
    legacy_scope0[0] = 0;
    legacy_scope0[1] = legacy_bv;

    uint32_t session = rt_session_heap_begin();
    check(session != 0, "BSM session begins");
    int64_t* sess_scope0 = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    check(rt_transient_array_scope_begin() == 1, "BSM module scope begins");
    int64_t mod_bv = rt_dict_new(4);
    int64_t mod_key = rt_string_new((const uint8_t*)"session_adopted_key1", 20);
    int64_t legacy_key = rt_string_new((const uint8_t*)"session_promot_key02", 20);
    check(rt_dict_set(mod_bv, mod_key, 9LL << 3) == 1,
          "module dict inserts module key inside Scope(0)");
    sess_scope0[0] = 0;
    sess_scope0[1] = mod_bv;
    check(rt_dict_set(legacy_bv, legacy_key, 10LL << 3) == 1,
          "pre-session persistent dict inserts module key inside Scope(0)");
    check(rt_transient_array_scope_pause() == 1, "BSM module scope pauses");
    check(rt_transient_heap_adopt((int64_t)(uintptr_t)sess_scope0) == 1,
          "adopt traverses pre-scope Scope(0) to adopt module dict and key into session");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)legacy_scope0) == 1,
          "promote under live session traverses pre-session Scope(0) into persistent dict");
    check(rt_transient_array_scope_end() == 1, "BSM module scope ends");
    check(rt_string_len(mod_key) == 20 &&
              memcmp(rt_string_data(mod_key), "session_adopted_key1", 20) == 0 &&
              rt_string_len(legacy_key) == 20 &&
              memcmp(rt_string_data(legacy_key), "session_promot_key02", 20) == 0,
          "adopted and session-promoted keys survive module scope end");
    check(rt_session_heap_end(session) == 1, "BSM session ends");
    check(rt_string_free(mod_key) == 0 && rt_string_free(legacy_key) == 0,
          "session-adopted and session-promoted keys are reclaimed at session end");
    rt_free(sess_scope0);
    rt_free(legacy_scope0);
}

static void test_struct_realloc_across_table_growth(void) {
    printf("[test] rt_struct_alloc realloc across transient raw table growth\n");
    check(rt_transient_array_scope_begin() == 1, "setup scope begins for promoted_struct");
    int64_t* promoted_struct = (int64_t*)rt_struct_alloc((int64_t)(2 * sizeof(int64_t)));
    check(promoted_struct != NULL, "promoted rt_struct_alloc allocated");
    promoted_struct[0] = 9999;
    promoted_struct[1] = rt_string_new((const uint8_t*)"struct_grow_child_v1", 20);
    check(rt_transient_array_scope_pause() == 1, "setup scope pauses for promoted_struct");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)promoted_struct) == 1,
          "initial promoted_struct promotes cleanly");
    check(rt_transient_array_scope_end() == 1, "setup scope ends for promoted_struct");

    check(rt_transient_array_scope_begin() == 1, "growth scope begins");
    int64_t* owned_struct = (int64_t*)rt_struct_alloc((int64_t)(2 * sizeof(int64_t)));
    check(owned_struct != NULL, "owned rt_struct_alloc allocated");
    owned_struct[0] = 4242;
    owned_struct[1] = 8484;

    /* Repeatedly resize both owned and promoted struct blocks while growing the
     * transient raw registry past multiple 70% resize thresholds (256 -> 512
     * -> 1024), exercising standalone rt_realloc's value-snapshotted `tracked`
     * metadata across rt_core_transient_raw_grow() free(old). */
    int realloc_ok = 1;
    int valid_ok = 1;
    for (int i = 0; i < 420; i++) {
        void* filler = rt_alloc(16);
        if (!filler) {
            realloc_ok = 0;
            break;
        }
        int64_t owned_sz = (int64_t)((2 + (i % 6)) * sizeof(int64_t));
        int64_t* next_owned = (int64_t*)rt_realloc(owned_struct, owned_sz);
        if (!next_owned || next_owned[0] != 4242 || next_owned[1] != 8484) {
            realloc_ok = 0;
            break;
        }
        owned_struct = next_owned;
        if (!rt_struct_receiver_valid((int64_t)(uintptr_t)owned_struct, 0, owned_sz)) {
            valid_ok = 0;
            break;
        }

        int64_t prom_sz = (int64_t)((2 + ((i + 3) % 6)) * sizeof(int64_t));
        int64_t* next_prom = (int64_t*)rt_realloc(promoted_struct, prom_sz);
        if (!next_prom || next_prom[0] != 9999 || rt_string_len(next_prom[1]) != 20) {
            realloc_ok = 0;
            break;
        }
        promoted_struct = next_prom;
        if (!rt_struct_receiver_valid((int64_t)(uintptr_t)promoted_struct, 0, prom_sz)) {
            valid_ok = 0;
            break;
        }
    }
    check(realloc_ok, "struct reallocs across table growth preserve contents");
    check(valid_ok, "resized struct blocks pass rt_struct_receiver_valid");

    check(rt_transient_array_scope_pause() == 1, "growth scope pauses");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)promoted_struct) == 1,
          "re-promoting resized promoted_struct succeeds");
    check(rt_transient_array_scope_end() == 1, "growth scope ends");
    churn_transient_heap(2);

    check(rt_struct_receiver_valid((int64_t)(uintptr_t)owned_struct, 0, 8) == 0,
          "owned rt_struct_alloc resized across growth is reclaimed at scope end");
    check(rt_struct_receiver_valid((int64_t)(uintptr_t)promoted_struct, 0, 8) == 1,
          "promoted rt_struct_alloc resized across growth remains registered");
    check(promoted_struct[0] == 9999 && rt_string_len(promoted_struct[1]) == 20 &&
              memcmp(rt_string_data(promoted_struct[1]), "struct_grow_child_v1", 20) == 0,
          "promoted rt_struct_alloc payload and child survive scope end and churn");
    rt_free(promoted_struct);
    check(rt_struct_receiver_valid((int64_t)(uintptr_t)promoted_struct, 0, 8) == 0,
          "freed promoted rt_struct_alloc unregisters cleanly");
}

static void test_paused_scope_realloc_preserves_owned(void) {
    printf("[test] paused-scope rt_realloc preserves owned=1 and unowned=0 lifetimes\n");
    check(rt_transient_array_scope_begin() == 1, "paused-realloc scope 1 begins");

    int64_t* owned_raw = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    int64_t* owned_struct = (int64_t*)rt_struct_alloc((int64_t)(2 * sizeof(int64_t)));
    int64_t* paused_persistent = NULL;
    check(owned_raw != NULL && owned_struct != NULL, "scope-owned blocks allocated");
    owned_raw[0] = 111;
    owned_struct[0] = 222;

    check(rt_transient_array_scope_pause() == 1, "paused-realloc scope 1 pauses");
    paused_persistent = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    check(paused_persistent != NULL, "paused-scope raw block allocated");
    paused_persistent[0] = 333;

    owned_raw = (int64_t*)rt_realloc(owned_raw, (int64_t)(4 * sizeof(int64_t)));
    owned_struct = (int64_t*)rt_realloc(owned_struct, (int64_t)(4 * sizeof(int64_t)));
    check(owned_raw != NULL && owned_raw[0] == 111 && owned_raw[3] == 0,
          "paused-scope rt_realloc of owned raw preserves prefix and zeroes tail");
    check(owned_struct != NULL && owned_struct[0] == 222 && owned_struct[3] == 0,
          "paused-scope rt_realloc of owned struct preserves prefix and zeroes tail");
    check(rt_struct_receiver_valid((int64_t)(uintptr_t)owned_struct, 0, 32) == 1,
          "paused-scope rt_realloc of owned struct remains valid before scope end");

    check(rt_transient_array_scope_end() == 1, "paused-realloc scope 1 ends");

    /* Check immediately in an empty probe scope (before any Scope 2 malloc
     * can reuse the freed addresses) that neither owned block remained in
     * persistent_raw, and both were reclaimed. */
    check(rt_struct_receiver_valid((int64_t)(uintptr_t)owned_struct, 0, 8) == 0,
          "paused-realloc owned struct was reclaimed at scope 1 end");
    check(rt_transient_array_scope_begin() == 1 && rt_transient_array_scope_pause() == 1,
          "empty probe scope begins and pauses");
    check(rt_transient_heap_promote((int64_t)(((uintptr_t)owned_raw) | 1ULL)) == 0,
          "paused-realloc owned raw was reclaimed and not left in persistent_raw");
    check(rt_transient_heap_promote((int64_t)(((uintptr_t)owned_struct) | 1ULL)) == 0,
          "paused-realloc owned struct was reclaimed and not left in persistent_raw");
    check(rt_transient_array_scope_end() == 1, "empty probe scope ends");

    check(rt_transient_array_scope_begin() == 1, "paused-realloc scope 2 begins");
    paused_persistent = (int64_t*)rt_realloc(paused_persistent, (int64_t)(4 * sizeof(int64_t)));
    check(paused_persistent != NULL && paused_persistent[0] == 333 && paused_persistent[3] == 0,
          "paused_persistent survives unpaused scope 2 realloc");
    paused_persistent[1] = rt_string_new((const uint8_t*)"unpaused_realloc_v01", 20);
    check(rt_transient_array_scope_pause() == 1, "paused-realloc scope 2 pauses");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)paused_persistent) == 1,
          "unpaused-realloc persistent raw remains promotable");
    check(rt_transient_array_scope_end() == 1, "paused-realloc scope 2 ends");
    churn_transient_heap(2);
    check(paused_persistent[0] == 333 && rt_string_len(paused_persistent[1]) == 20 &&
              memcmp(rt_string_data(paused_persistent[1]), "unpaused_realloc_v01", 20) == 0,
          "persistent raw reallocated during unpaused scope 2 survives scope end");
    rt_free(paused_persistent);
}

int main(void) {
    test_prescope_binding_versions_root();
    test_mixed_scalar_array_batch_and_multiscope();
    test_prescope_realloc_free_and_bsm_adopt();
    test_struct_realloc_across_table_growth();
    test_paused_scope_realloc_preserves_owned();
    if (failures == 0) {
        printf("SELFCHECK PASSED (0 failures)\n");
        return 0;
    }
    printf("SELFCHECK FAILED (%d failures)\n", failures);
    return 1;
}
