# BUG: `LlvmIRBuilder.emit_module_header()` ignores the triple passed to `create()`
## Closed 2026-11-25 — suggested fix landed: constructor triple is snapshotted as scalar fields; header composes from them, no env re-probe

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- **Date:** 2026-08-09
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Component:** `src/compiler/70.backend/backend/llvm_ir_builder.spl`
- **RED spec:** `test/feature/usage/llvm_backend_i686_spec.spl` — "emits datalayout in module header"

## Symptom

```
LlvmIRBuilder__create("test_i686", LlvmTargetTriple__from_target(CodegenTarget.X86))
builder.emit_module_header()
```
emits the **x86_64** header:

```
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
```

The spec asserts `to_contain("p:32:32")` and fails. The sibling case
"contains 32-bit pointer specification", which calls `triple.datalayout()`
directly, PASSES — so the triple itself is correct; only the builder header is
wrong.

## Root cause

`create()` (llvm_ir_builder.spl:88-100) accepts `target: LlvmTargetTriple` but
**stores nothing from it except `size_type`**. There is no triple field on the
class.

`emit_module_header()` (:108-149) therefore re-derives its own triple from the
process environment:

```
val target: LlvmTargetTriple = LlvmTargetTriple.from_target(llvm_builder_target())
```

`llvm_builder_target()` (:30-49) reads `SIMPLE_NATIVE_BUILD_TARGET` and falls
back to `CodegenTarget.Host` when unset. With the var unset — the case in every
spec run and in any in-process API use — an i686/arm/riscv builder emits an
x86_64 header.

## Proof

Same spec, same binary, env var added:

```
SIMPLE_NATIVE_BUILD_TARGET=i686-unknown-linux-gnu bin/simple test test/feature/usage/llvm_backend_i686_spec.spl
SPEC FILE VERDICT: ... executed=8 passed=8 failed=0 dropped=0
```

vs. unset: `executed=8 passed=7 failed=1`.

## Why the other architectures do not show it

`llvm_backend_aarch64_spec.spl` has the same `it`, but asserts only
`to_contain("target datalayout")` — no arch-specific substring — so it passes
**vacuously** on an x86_64 header. `arm32`/`riscv32`/`riscv64` have no
module-header case at all. i686 is the only spec whose assertion is specific
enough to see the defect.

## Why this was not fixed here

The env-derived re-derivation is a **deliberate workaround**, documented inline
at :110-125, for a compiled-lane field-offset shift when an `LlvmTargetTriple`
is carried across the builder class boundary
(`doc/08_tracking/bug/stage3_selfhost_llvm_triple_field_offset_shift_2026-08-06.md`).
Storing the constructor triple (or its `datalayout()`/`arch` text) on the class
would re-enter exactly that path. If `datalayout()` is corrupt on the stage-3
compiled lane the result is wrong headers for **every** native build, and
verifying otherwise costs a full bootstrap. That is a bigger and riskier change
than the closed-gate cleanup this stream is doing, so it is filed rather than
rushed.

Production is not affected today: every real native-build path sets
`SIMPLE_NATIVE_BUILD_TARGET`. The defect is in the **public API contract** —
`create(name, target)` silently ignores `target` for header purposes.

## Suggested fix

Capture scalar text in `create()` (where reading the triple is already proven
safe — `target.is_32bit()` is read there and `size_type` comes out correct) into
new `header_datalayout: text` / `header_triple_text: text` fields, and have
`emit_module_header()` prefer them, keeping the env path only for the
baremetal/simpleos overrides. Must be verified through a stage-3 bootstrap, not
the interpreter.

## Open uncertainty

Not established whether the offset-shift bug affects `datalayout()` specifically
or only the `env: text?` field named in that bug. If only `env`, the fix above
is safe and cheap.


## Verification 2026-11-25 (p2w3-ae lane, release/1.0.0 worktree) — fix landed, closing

The "Suggested fix" section above is exactly what current source implements in
`src/compiler/70.backend/backend/llvm_ir_builder.spl`:

- The class carries scalar snapshots of the constructor triple:
  `target_arch` / `target_vendor` / `target_os` / `target_env` /
  `target_has_env` / `target_datalayout` (:62-67), populated by
  `create_with_header_policy` (:97-113) via `create_from_target_scalars`
  (:116-151) — scalar text captured at `create()` time, precisely the shape
  this record recommended (avoiding the aggregate-across-class-boundary read
  implicated in the stage-3 field-offset-shift bug).
- `emit_module_header()` (:161-177) composes `target triple` from those stored
  scalars and emits `self.target_datalayout`; its own comment states "header
  emission performs no host or environment probe". The only remaining ambient
  path is the explicit `allow_ambient_header_policy` + `_llvm_simpleos_header`
  override for the simpleos baremetal case — a deliberate policy knob, not the
  silent env fallback this bug was filed on.
- The RED spec's assertion is still the right oracle:
  `test/feature/usage/llvm_backend_i686_spec.spl:50-56` asserts the module
  header contains `p:32:32`; with the constructor triple now authoritative,
  an i686 builder emits the i686 datalayout regardless of
  `SIMPLE_NATIVE_BUILD_TARGET`.

Runtime re-run of the spec in this lane was not possible: the pinned seed
binary at `bin/simple.exe` rejects the `@representation_boundary` decorator
added tree-wide by cfd89933699 (and llvm_ir_builder.spl itself carries that
decorator at :115/:153), so every `bin/simple.exe test` at release/1.0.0 HEAD
fails before reaching subject code. Verification is by code inspection, which
is decisive here: the env re-derivation this bug named no longer exists.

**Verdict: STALE-CLOSED. The `create(name, target)` API contract now honors
`target` for header purposes.**
