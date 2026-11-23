# Seed-built Stage 2: a user `len()` method in the module hijacks `text.byte_len()`

Status: OPEN. Root cause NOT located and NOT fixed. Only the trigger was removed
(`IncrChangeSet.len()` renamed to `change_count()`).

Nothing in this record was re-executed while writing it: the host had no
runnable `simple` binary. The evidence below is the diagnosing session's
report; the source facts were re-read on `origin/release/1.0.0` at
`3b8523be415`.

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

## Where the defect is, and is not

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

## Repair gate

1. Seed regression: a module with a struct `impl` defining `fn len()` plus a
   free function calling `byte_len()` on a `text?.unwrap()` result must lower
   the call to `rt_string_len`, with no `MethodCallStatic` / inlined field load.
2. Check the pure-Simple arm with the same fixture.
3. Until then, avoid adding a zero-argument `len()` method to any struct in a
   module that calls `text.byte_len()`.
