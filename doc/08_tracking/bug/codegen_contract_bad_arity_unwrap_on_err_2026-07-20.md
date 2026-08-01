# Bug (or stale-test — needs design-intent call): GPU-intrinsic bad-arity
"emits diagnostic comment" specs call `.unwrap()` unconditionally, crashing
on the `Err` the backend now correctly returns

**Status:** RESOLVED 2026-08-01 — does not reproduce at HEAD. The design
question below is answered (hard `Err` is correct for CUDA/PTX) and the two
crashing examples were already rewritten by `ecfc9518ca0` (2026-07-29,
"fix(cuda): preserve pointer address spaces"). See **Resolution** at the
bottom for the re-run evidence and the one residual asymmetry.

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

## Resolution (2026-08-01)

**Does not reproduce.** Seed oracle
`src/compiler_rust/target/bootstrap/simple` on
`test/01_unit/compiler/codegen/vec_types_contract_spec.spl`:
`Results: 23 total, 23 passed, 0 failed`. (The original repro line under-runs:
the runner's default per-file timeout kills this spec at ~125 s and reports
`file timed out` as `1 total, 0 passed, 1 failed`. It needs
`--timeout 900` / `SIMPLE_TIMEOUT_SECONDS=900`; the file takes ~323 s.)

### Why the arity was "wrong"

It was never a backend miscomputation — the mismatch is *authored into the
fixture on purpose*, and the doc's panic-message-based reading of it was
right only by accident. `vec_types_contract_spec.spl:146-161` builds
`gpu_vec4_load_f32` with **one** operand and `gpu_vec4_store_f32` with
**three**:

```
fn vec4_load_bad_args_block() -> MirBlock:
    ... MirInstKind.Intrinsic(Some(LocalId(id: 0)), "gpu_vec4_load_f32", [copy_operand(1)]) ...
fn vec4_store_bad_args_block() -> MirBlock:
    ... MirInstKind.Intrinsic(nil, "gpu_vec4_store_f32", [copy_operand(1), copy_operand(2), copy_operand(3)]) ...
```

The `Err` comes from the CUDA backend's deliberate arity gate,
`src/compiler/70.backend/backend/cuda_backend.spl:1617-1644`:

```
me validate_intrinsic(name: text, dest: LocalId?, arg_count: i64) -> Result<(), CompileError>:
    ...
    case "min" | ... | "gpu_vec4_load_f32" | "gpu_vec2_load_f32": required_args = 2
    case "gpu_vec4_store_f32":
        required_args = 6
        requires_dest = false
    ...
    if arg_count != required_args:
        return Err(compileerror_backend_error(BackendKind.Cuda, "CUDA intrinsic '{name}' requires exactly {required_args} arguments"))
```

So the crash was in the **spec's** unconditional `.unwrap()`, exactly as
filed — the backend was behaving correctly.

### The open question, answered

Hard `Err` is correct for CUDA/PTX, and it is not merely "arguably safer" —
`validate_intrinsic` is the only thing standing between bad arity and two
distinct failure modes. Deleting just the `arg_count != required_args` guard
(one-line A/B, reverted) turns the two examples into:

- `gpu_vec4_load_f32` (1 arg) → `semantic: array index out of bounds: index
  is 1 but length is 1` — the emitter crashes reading `args[1]`.
- `gpu_vec4_store_f32` (3 args) → `called unwrap_err on Ok` — the backend
  returns **Ok**, silently emitting PTX for a 6-operand store built from 3.

A comment cannot be substituted here: PTX is register-based, so a dropped
vector load leaves an undefined register rather than an inert comment.

`ecfc9518ca0` already applied follow-up (2) to the CUDA/PTX half, renaming
`"emits diagnostic comment for gpu_vec4_{load,store}_f32 with bad arity
(PTX)"` to `"rejects ..."` and replacing `.unwrap()` with
`expect(result.is_err()).to_equal(true)` +
`expect(result.unwrap_err().message).to_contain("requires exactly N
arguments")` — an assertion *change*, correctly landed with the design call
rather than as a syntax migration.

### Regression coverage — already in tree, proven non-vacuous

The guard is `vec_types_contract_spec.spl:275-297` (the two `"rejects ...
with bad arity"` CUDA examples). No new spec was added; a duplicate would be
gold-plating. Non-vacuity proof (`--timeout 900`, seed oracle):

| `cuda_backend.spl:1638` arity guard | vec_types_contract_spec.spl |
|---|---|
| present (HEAD) | 23 total, **23 passed, 0 failed** |
| neutered (`if false and arg_count != required_args`) | 23 total, 21 passed, **2 failed** — and exactly the two bad-arity examples |

### Scope correction to the "likely-same-pattern" list

The 9-file bucket was over-broad. Enumerating every example in
`test/01_unit/compiler/codegen/*_contract_spec.spl` that calls
`compile_module_to_*`/`.compile()` from an `it` named
`*bad*`/`*invalid*`/`*missing*`/`*diagnostic*`/`*arity*` yields only
`vec_types_contract_spec.spl` (4) and `spec_constants_contract_spec.spl`
(2). `group_algorithms`, `hip_backend`, `host_gpu_lane_codegen_marker`,
`opencl_backend`, `subgroup_intrinsics` and `vhdl_kernel_entity` have no
example of this shape. `spec_constants_contract_spec.spl` re-run clean:
`Results: 13 total, 13 passed, 0 failed`.

### Residual (not fixed here — deliberate, separately owned)

CUDA and OpenCL disagree on bad arity, and the OpenCL side is the fail-open
one. `OpenClBackend.emit_vec_load`/`emit_vec_store`
(`opencl_backend.spl:838-867`) return a `// {name} missing arguments ...`
comment and compile reports **success**, dropping the instruction and leaving
the destination local undefined in the emitted C. The existing gate
`OpenClBackend.validate_generated_source` (`opencl_backend.spl:83-94`) turns
lowering markers into `Err`, but only matches `// unsupported OpenCL` and
`// unsupported MIR instruction for OpenCL subset` — not the
`missing arguments` / `missing destination` markers.

This is *intended, specified* behavior today, asserted in two places
(`vec_types_contract_spec.spl:220-239`,
`spec_constants_contract_spec.spl:199-209`), so tightening it is an
assertion-changing design call, not a bug fix, and is left to the same owner
who ruled on the CUDA half. Recording it here so the asymmetry is not
rediscovered as a "crash" a third time.
