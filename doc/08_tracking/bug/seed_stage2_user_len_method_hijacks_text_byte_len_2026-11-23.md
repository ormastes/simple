# Seed-built Stage 2: a user `len()` method in the module hijacks `text.byte_len()`

Status: seed mangler fix landed 2026-11-24, NOT yet confirmed by a Stage 2 rebuild. Root cause located and pinned by
a regression test at the mangler level. A Stage 2 was NOT rebuilt to confirm it
end to end; see "Root cause and fix" below for exactly what was executed.

The Symptom / Evidence sections are the diagnosing session's report and were
not re-executed.

## Root cause and fix (2026-11-24)

The rebind happens in the seed's native-project name mangler, before codegen —
not in MIR lowering, struct-method inlining, or the LLVM `byte_len` redirect.

1. MIR lowering emits `MethodCallStatic` named `byte_len` (erased receiver) or
   `str.byte_len` (text receiver)
   (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`).
2. `mangle_mir` finds no exact binding, so `resolve_method_call_static`
   (`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`) falls
   through to `resolve_by_suffix`
   (`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:334`).
3. `resolve_by_suffix` cuts the name at every `_` and looks the TAIL up as a
   method: `byte_len` / `str.byte_len` becomes a lookup of `len`, and a lone
   candidate binds with no check that the head (`byte`) names its owner.
4. The LOCAL suffix index (`mangle.rs`, "Build local suffix index") lists the
   lowercase leaf of every method the module itself defines
   (`<prefix>__IncrChangeSet.len` -> `len`). The global index only lists
   uppercase leaves, and use/import-map values are `_dot_`-escaped so they add
   no leaf. So `len` has exactly one candidate precisely when the module
   defines one struct `len()` — which is why the trigger was "a user `len()`
   in the same file", and why removing it restored `rt_string_len` (with no
   local candidate only the global index is consulted, and it lists free
   functions named `len`, not methods; that nothing bound there is inferred
   from the pre-trigger build working, not measured).
5. Codegen then sees a resolvable `…IncrChangeSet.len`, its `direct_func` arm
   (`codegen/llvm/functions.rs`) calls it and returns before the
   `rt_string_len` redirect; LLVM inlines the tiny body, giving the observed
   "load field 0, read +8" on a text pointer.

`MirInst::Call` targets take the same fallthrough in `resolve_call_target`.
`char_count` is the same shape (tail `count`).

Fix: the four last-resort fallthroughs in `resolve_call_target` and
`resolve_method_call_static` go through `resolve_unbound_by_suffix`
(`mangle.rs`). For the text-only builtin leaves `byte_len` and `char_count` it
allows only an EXACT lone candidate (a real user `byte_len`, e.g.
`src/os/kernel/loader/byte_utils.spl`) and never the underscore cut, so the
name stays as emitted and codegen's `rt_string_*` lowering owns it.
`resolve_by_suffix` itself is unchanged: legacy `Owner_method` names depend on
the cut and a Stage 2 could not be rebuilt on this host to re-validate a wider
change.

Regression tests (`mangle.rs`, `mod tests`):
- `source_struct_len_never_captures_unwrapped_text_byte_len` — parses and
  lowers the `incremental.spl:1026` shape (struct `fn len()` plus
  `text?.unwrap().byte_len()`) through the real HIR/MIR pipeline, then runs the
  real `mangle_mir`.
- `local_struct_len_never_captures_text_byte_len` — hand-written MIR: bare and
  `str.`/`text.` spellings, the `Call` route, `char_count`, and an
  `Owner_method` control that must still bind.
- `exact_user_byte_len_candidate_still_binds`.

Executed (2026-11-24, `cargo test --release -p simple-compiler --lib`, default
features, clang/lld):
- Guard disabled: the source test FAILED with lowering's `str.byte_len`
  mangled to `driver__incremental__ChangeSet.len`, and the MIR test FAILED with
  all six text-builtin calls bound to `IncrChangeSet.len` / `.count`.
- Guard enabled: `-- mangle suffix byte_len` reports 70 passed, 0 failed.
- A wider `pipeline::native_project` run was killed (rc 143) after 252 of 451
  tests and is not a pass. In it,
  `test_bootstrap_mutex_capsule_exports_only_canonical_bootstrap_abi` failed on
  an exported C-runtime symbol set (`rt_process_rss_kib`,
  `rt_secure_temp_dir_*`) this change does not touch; it was not baselined on
  the unmodified tree.

Not executed or measured:
- A Stage 2 rebuild with `IncrChangeSet.len()` restored. The link from this
  rebind to the reported SIGSEGV is the mechanism above plus the matching
  symptom.
- The tests pass empty use/import maps. In a real build the count of local
  `len` candidates also depends on `import_map["len"]`, a first-wins pick over
  every bare `len` in the closure: if it lands on one of the free `fn len`
  definitions instead of a (`_dot_`-escaped) method, the count is 2 and this
  route does not bind. Which one wins is file-order dependent and was not
  measured.


Not fixed, same defect class: any other snake_case method whose tail equals a
method the module defines (`index_of` -> a local `of`, `to_text` -> a local
`text`) still takes the cut. The earlier per-name guards (`starts_with`,
`to_u64`, ...) cover the measured ones. The pure-Simple arm
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`) was not
checked.

## Symptom

Commit `0d38bb8581a` added this method to
`src/compiler/80.driver/driver_build/incremental.spl`:

```
impl IncrChangeSet:
    fn len() -> i64:
        self.changes.len()
```

In a Stage 2 compiler built by the Rust seed from a tree containing that
method, an unrelated call in the same file was miscompiled:

```
pub fn incremental_fingerprint_digest_valid_v1(digest_opt: text?) -> bool:
    if digest_opt == nil: return false
    val digest = digest_opt.unwrap()
    if digest.byte_len() != 64: return false      # incremental.spl:1026
```

`digest.byte_len()` on a `text` was emitted as the inlined struct method
(load field 0 of the receiver, then read `+8`) instead of a call to
`rt_string_len`. That is the shape of `IncrChangeSet.len()` — field 0 is
`changes`, `+8` is the array length — applied to a text pointer.

## Evidence (reported, not re-run here)

- Every per-file native-build worker died with SIGSEGV, kernel line
  `segfault at 5800000008`, on the first `FileFingerprint.from_file(object_path)`
  after codegen (`src/compiler/80.driver/driver_aot_native_output.spl` ~4177).
- 24 of 24 worker units crashed.
- Without the `len()` method, the same source calls `rt_string_len` and works.
- The receiver is the result of `text?.unwrap()`, so its static type may reach
  the seed's method lowering erased rather than as `STRING`. Not confirmed.

## Correction to the original diagnosis

The diagnosis said `IncrChangeSet.len()` had no callers. It has one:
`test/01_unit/compiler/driver/lockfree_parallel_pipeline_spec.spl:461`,
`detect_res.changes.len()`, where `detect_res` is the
`IncrementalCompileResult` returned by `incremental_detect_changes_at` and
`.changes` is therefore an `IncrChangeSet`. `0d38bb8581a` introduced the method
and the `IncrementalCompileResult` return together. The method was renamed, not
deleted, and that call site was updated. Every other `.changes.len()` in
`src/` and `test/` is on an array field.

## Where the defect is, and is not (original 2026-11-23 analysis, superseded above)

The bad code was emitted by the **Rust seed** compiling Stage 2, so the
pure-Simple arm is not the code that ran:

- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3956-3967` —
  the `byte_len` arm; emits `rt_string_len` when
  `text_builtin_resolution_allowed and not resolution_is_static_method and not
  predicate_has_custom_owner`. It may share the defect (a user `len` owner in
  the module flipping one of those predicates) but that was not established.

Seed sites examined. None of them binds `byte_len` to a user `len`; each one
that guards against a user definition checks for a user **`byte_len`**, never a
user `len`:

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2575-2592` — bare
  `byte_len` redirect, gated by `module_has_user_byte_len`.
- `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:80-91`
  (`module_has_user_byte_len`), `:1978-1986`, `:2186-2192`.
- `src/compiler_rust/compiler/src/codegen/llvm/mod.rs:83-101`
  (`resolved_text_runtime_method`).
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:4543` and
  `codegen/instr/closures_structs.rs:2783` — Cranelift `byte_len` ->
  `rt_string_len` tables.
- `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:2399`, `:2816-2818` —
  result typing only; `byte_len` sits next to `"len" | "length" | "size"`.
- `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:197`
  (`resolve_name_variants`) — has a last-resort bare-method lookup that
  discards the type qualifier; no path from `byte_len` to `len` was found in it.

Not read: the seed's struct-method inlining pass and the MIR method lowering in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`. The
`byte_len` -> `len` step is most likely in one of those.

## Related records

- `doc/08_tracking/bug/2026-10-04_seed_nominal_field_slot_zero_fallback.md` —
  seed substitutes field slot 0 when a nominal owner cannot be proven.
- `doc/08_tracking/bug/cranelift_inline_len_heap_tag_space_collision_dict_closure_2026-09-06.md`
- `doc/08_tracking/bug/2026-11-12_dir_create_all_same_signature_collision_swaps_bodies.md`

## Repair gate (item 1 met for the mangler, not for emitted code; 2 open; 3 stays until a Stage 2 rebuild confirms)

1. Seed regression: a module with a struct `impl` defining `fn len()` plus a
   free function calling `byte_len()` on a `text?.unwrap()` result must lower
   the call to `rt_string_len`, with no `MethodCallStatic` / inlined field load.
2. Check the pure-Simple arm with the same fixture.
3. Until then, avoid adding a zero-argument `len()` method to any struct in a
   module that calls `text.byte_len()`.
