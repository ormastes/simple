# Bug (or stale-test — needs design-intent call): GPU-intrinsic bad-arity
"emits diagnostic comment" specs call `.unwrap()` unconditionally, crashing
on the `Err` the backend now correctly returns

**Status:** OPEN — filed, not fixed (classification needs a product-design
decision: see below)

**Date:** 2026-07-20
**Campaign:** whole-suite 01_unit triage (fix_guide.md)
**Severity:** Test-authoring defect at minimum; possibly documents a real
behavior change (graceful embedded-diagnostic-comment → hard compile Err)
that was never reconciled with the specs describing the old behavior

## Summary

Several `test/01_unit/compiler/codegen/*_contract_spec.spl` files have a
paired "good" / "bad arity" example structure per GPU intrinsic, e.g. (from
`test/01_unit/compiler/codegen/vec_types_contract_spec.spl:211-213`):

```
it "emits diagnostic comment for gpu_vec4_load_f32 with bad arity":
    val func = make_opencl_vec_kernel("opencl_vec4_load_bad", 302, vec4_load_bad_args_block())
    val source = OpenClBackend.compile_module_to_opencl_source(make_module_from(func)).unwrap()
    ...
```

The example's own name ("emits diagnostic comment ... with bad arity")
states the design intent: bad arity should produce a **successful** compile
whose output source embeds a diagnostic comment, inspectable via
`expect(source).to_contain(...)`. But `compile_module_to_opencl_source(...)`
now returns `Err(CompileError(message: "CUDA intrinsic 'gpu_vec4_load_f32'
requires 2 arguments", phase: "backend (cuda)", ...))` for the bad-arity
input, and the spec's own `.unwrap()` panics on that `Err` before the
`expect(source).to_contain(...)` line is ever reached — i.e. the crash is in
the **spec's** unconditional `.unwrap()`, not (necessarily) in the backend.

## Open question this doc does not resolve

Is returning a hard `Err` on bad arity the *correct, current* design
(diagnostics should be compile errors, not embedded comments — arguably
safer), making the spec's `.unwrap()` simply wrong and needing a
match-on-Err rewrite? Or did the backend regress away from the
graceful-diagnostic-comment behavior these specs were written to verify,
making this a real product bug? Both readings are consistent with the
evidence gathered in this pass; resolving it needs either git history on the
intrinsic-lowering bad-arity path or a design-owner call. Filed as
GENUINE-BUG (not silently rewritten to `match`) per the campaign's hard rule
against weakening assertions — matching the Err message instead of the
Ok-source content would be a different assertion, not a syntax migration.

## Confirmed affected specs (2, directly reproduced)

- `test/01_unit/compiler/codegen/vec_types_contract_spec.spl` — 2 confirmed
  failures of this shape: "emits diagnostic comment for gpu_vec4_load_f32
  with bad arity (PTX)" (`CompileError(...'gpu_vec4_load_f32' requires 2
  arguments...)`), "emits diagnostic comment for gpu_vec4_store_f32 with bad
  arity (PTX)" (`...requires 6 arguments...`). The OpenCL-target examples in
  the same file (lines 211-213 above) share the identical `.unwrap()` shape
  and are very likely the same failure, not individually re-run in this
  pass.

## Likely-same-pattern, not individually reproduced (same file bucket,
`compiler/codegen/*_contract_spec.spl`, 9 files total in the failing set)

`test/01_unit/compiler/codegen/group_algorithms_contract_spec.spl`,
`hip_backend_contract_spec.spl`, `host_gpu_lane_codegen_marker_spec.spl`,
`opencl_backend_contract_spec.spl`, `spec_constants_contract_spec.spl`,
`subgroup_intrinsics_contract_spec.spl`, `vhdl_kernel_entity_contract_spec.spl`
— not confirmed to share this exact root; flagged for a follow-up grep of
`.unwrap()` immediately after a `compile_module_to_*` call inside an example
named `*bad arity*`/`*diagnostic*`.

## Reproduction

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/codegen/vec_types_contract_spec.spl \
  --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -A2 '✗'
```

## Suggested follow-up

1. Get a design-owner ruling on intended bad-arity behavior (embedded
   comment vs. hard Err).
2. If hard Err is correct: rewrite these examples to assert on the `Err`
   message instead of unwrapping, across the whole `*_contract_spec.spl`
   bucket in one pass.
3. If embedded comment is correct: file a product bug against the
   CUDA/OpenCL intrinsic arity-check path for returning Err instead.
