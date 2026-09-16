# Authority recovery: five unrelated compiler test failures

## Evidence

`build/mini_builds/authority_fix_recovery_tests_20260811/logs/compiler_resume.log`
reports 45 passing and five failing filtered tests. Detailed panic text is in
the companion `compiler_resume.time`. This note classifies those failures; it
does not claim a fix.

## Classification

1. `test_jit_i32_struct_fields_do_not_retain_stale_upper_bits` fails because
   the in-process JIT provider cannot resolve newly required
   `rt_struct_alloc`. This extends
   `stage2_struct_allocation_receiver_guard_mismatch_2026-08-11.md`: the
   allocator lowering is correct, but the JIT test/provider symbol registry is
   stale. It does not block the native authority tuple or Stage-2 native-build
   path, provided tuple admission independently proves the exported symbol. It
   does block a clean Rust compiler unit-test gate.

2. `imported_trait_optional_struct_return_preserves_field_type` loses
   `MouseEvent?` and reaches an `ANY.left_just_pressed` field lookup. This is
   already Category D in
   `cargo_test_lib_129_failures_triage_2026-08-10.md` and the imported/ANY field
   class in `hir_type_inference_any_field_2026-05-02.md`.

3. `test_lower_field_access_uses_unique_duplicate_struct_variant` reaches
   `ANY.handle` instead of selecting the unique duplicate `CompilerContext`
   layout. This is the duplicate-definition side-table class documented in
   `compiler_context_multidef_collision_2026-05-02.md`; the record's former
   FIXED status has regressed under the current tree.

4. `test_cross_module_optional_struct_match_keeps_payload_type` loses the
   `MemoryRuntimeMapping` payload type. This is already the cross-module
   optional-struct payload Category D entry in
   `cargo_test_lib_129_failures_triage_2026-08-10.md`.

5. `test_duplicate_struct_sidecar_resolves_unique_compiler_context_handle`
   fails with `UnknownType("CompilerContext")`. This is already the
   duplicate-struct sidecar Category D entry in that triage and the concrete
   regression oracle in `compiler_context_multidef_collision_2026-05-02.md`.

## Gate impact

Failures 2–5 are HIR/import-layout regressions in filtered Rust unit tests.
They do not change the frozen runtime/compiler-backfill tuple and are not the
Stage-2 invalid-receiver root cause. They remain compiler correctness defects
and therefore block claiming a globally clean Rust test suite, but do not by
themselves block the narrowly scoped authority tuple or exact Stage-2
admission. The JIT failure has the same disposition only if native symbol-table
and executable probes explicitly confirm `rt_struct_alloc`; without that
evidence, authority admission must fail closed.
