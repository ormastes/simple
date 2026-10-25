# Array `==` / `!=` lowered as an identity compare (Stage-2 native codegen)

- Date: 2026-10-25
- Status: open (compiler); workaround at one site
- Found by: Phase 3 broad sweep (run-28s)

## Symptom
The Stage 3 self-build (parse sharding on) stops after about 98 s with
`error: parse-shard closure selector mapping mismatch`
(src/app/cli/native_build_parse_closure_owner.spl, `selected_roots != canonical.unwrap()`).
The Stage 2 build of the same source passes that check.

## Reproduction (Stage-2 native)
The following programs were built by the Stage 2 compiler and then run:
- `[text]` lists built separately with equal content print `!= true`, `== false`.
- `[i64] [1,2] != [1,2]` prints `true`.
- `[u8] [1,2,3] == [1,2,3]` prints `false`.

The spec is test/01_unit/app/cli/array_eq_identity_compare_spec.spl. It shows red only when built natively by an affected compiler.

## Root cause (suspected routing gap)
In the Stage 3 binary, `native_build_parse_closure_write_v1` calls `unwrap` on both Results and then goes straight to
`file_hash_sha256`, with no `rt_native_eq` call. The array comparison is therefore a raw word (pointer)
compare. The runtime's `rt_native_eq` already compares registered arrays element-wise
(runtime_native.c), and MIR has `emit_runtime_word_eq` for it. Array-typed Eq/NotEq is apparently
not routed there. This is inferred from the emitted calls; the MIR lowering path itself has not been traced.
The same wrong result also appears in programs built by the Stage 3 compiler, so the defect is in the compiler source and not only in the Stage 2 binary.

## Fix / workaround
- Compiler fix (open): route array-typed `Eq`/`NotEq` through `emit_runtime_word_eq` in MIR lowering.
- Workaround (@workaround, this bug): `_parse_closure_text_list_eq_v1`, an element-wise compare, in
  native_build_parse_closure_owner.spl. Delete it once the compiler fix is in the producing compiler.
- Env alternative: `SIMPLE_PARSE_SHARDING=0`. However, the unsharded parent parse then OOMs at an 80G cap.

Other array-comparison sites that would be affected (INFERRED; not observed failing):
`src/compiler/70.backend/linker/managed_link_toolchain_closure_v1.spl:1389`,
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:486` and `:488`.
Var-vs-var array comparisons have not been censused.
