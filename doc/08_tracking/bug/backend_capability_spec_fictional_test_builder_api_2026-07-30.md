# backend_capability_spec.spl: 34 commented tests target a never-built capability-check API

- **Filed:** 2026-07-30
- **Severity:** low — dead test scaffolding, not a product regression
- **Status:** open (documented gap, out of scope for lane BCAP `backend-capability-spec-triage`)
- **Found via:** BCAP lane triage of `test/01_unit/compiler/backend/backend_capability_spec.spl`

## Symptom

`test/01_unit/compiler/backend/backend_capability_spec.spl` has only 6 active
`it` blocks; 34 more are commented out. `git log --diff-filter=A` shows the
file has always contained exactly this split, back to its very first commit
(`97a9358145f`, "test-infra: scaffold database + doc generation wiring
(debug required)", 2026-07-01). The 34 were never active and never passing —
commenting them is not a regression.

## Root cause (two independent gaps)

1. **Groups "Backend Capability Detection Accuracy" (9), "Backend Selection
   Logic" (4), "Backend Fallback Behavior" (1) — 14 tests.** They import:
   ```
   use compiler.backend.mir_test_builder.{MirTestBuilder, BackendTarget}
   ```
   and call `builder.vreg(0)`, `builder.const_int(v0, 10)`, `builder.add(...)`,
   `builder.build()` returning an object with `.is_supported(BackendTarget.X)`
   and `.instruction_count()`. **That module does not exist** — there is no
   `mir_test_builder.spl` anywhere under `src/compiler/`, confirmed via
   `find src -iname "mir_test_builder.spl"` (zero hits).

   The only sibling module, `compiler.backend.backend.mir_test_builder_full`
   (`src/compiler/70.backend/backend/mir_test_builder_full.spl`, used
   successfully by `test/01_unit/compiler/backend/backend_basic_spec.spl`,
   `instruction_coverage_spec.spl`, `differential_testing_spec.spl`,
   `mir_instruction_complete_spec.spl`), has a **materially different, lower-
   level API**:
   - `add_const_int(dest: i32, value: i64)` / `add_const_float` / `add_add` /
     `add_mul` / `add_ret` / `add_vec_sum` / `add_gpu_global_id` — no
     `.vreg()` returning a handle, no `.const_int(dest, value)` two-arg call
     matching the commented tests' shape, no `.mul()`, no `.gpu_barrier()`,
     no `.gpu_atomic_add()`, no `.actor_spawn()`, no `.block()`, no
     `.vec_lit()`.
   - `MirTestCase` / `MirTestBuilder` are **pure data classes**: `name`,
     `instructions`, `expected_backends` (the backends the test *author*
     declared expected, via `only_backend`/`only_backends` — never
     independently verified), `description`. **Neither class has an
     `is_supported()` or `instruction_count()` method anywhere.** Confirmed
     by reading the full 259-line file: the only methods are the `add_*`
     builders, `only_backend(s)`, and `build()`.

   In other words: the real capability-VERIFICATION logic these 14 tests
   assume (querying whether a backend genuinely supports an instruction) was
   designed on paper (see this spec file's own "Overview" / "Error Message
   Requirements" doc comment, lines ~102–129) but never implemented anywhere
   in the codebase. `mir_test_builder_full.spl` only *records* what backends
   a test's author expects; it never checks that against real backend
   behavior.

2. **Groups "Backend Error Messages" (6), "Backend Capability Matrix" (9),
   "Capability Documentation" (5) — 20 tests.** Bodies are bare `pass`
   statements with zero `expect`/`assert` calls, e.g.:
   ```simple
   it "provides instruction name in error":
       # Test that error includes the instruction name
       # This would need actual backend execution
       pass
   ```
   These were never implemented test bodies, not silenced assertions.

## Why not fixed in-lane

Building the missing `is_supported()` capability-check API (querying real
backend dispatch tables for MIR-instruction support) is production src work.
Lane BCAP's scope was spec-file + bug-doc only (backend src touches limited
to verified-stale-message confirmation probes for the 2 separately-fixed
active-test failures — see the LLVM string-global fix in this same file).

## Why not converted to `skip()`

Investigated and reverted: `std.spec.skip(...)` (see
`src/lib/nogc_sync_mut/spec/decorators.spl`) is a platform/hardware
**decorator**, not a pass/fail override recognized by the interpreter BDD
runner — real usage (e.g.
`test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl`)
still requires the `it` body to end in a genuine passing `expect()` after
logging the skip reason. A bare `skip(name, reason)` call with no import
resolves to `semantic: function \`skip\` not found` under `bin/simple test`
for a plain `describe`/`it` spec (no `use std.spec.*`). There is no
runner-recognized "marked SKIPPED, excluded from pass/fail count" outcome
for these specs.

## Resolution

Left commented, with an explicit, dated triage header directly above the
block in `backend_capability_spec.spl` (never a silent commented block) —
per the repo's no-silent-skip policy this documents the gap honestly instead
of hiding it.

## To actually fix

1. Implement a real capability-check method on `mir_test_builder_full.spl`'s
   `MirTestCase` (e.g. `is_supported(target: BackendTarget) -> bool`
   querying each backend's real `translate_*`/`emit_unsupported_panic` code
   paths — likely by attempting the same lowering these 6 active tests use
   and checking for a panic/error).
2. Port the 34 commented tests onto the real API (rename `vreg`→raw `i32`,
   `const_int(v,val)`→`add_const_int(v,val)`, drop `.gpu_barrier()`/
   `.actor_spawn()`/`.block()` calls not present in `mir_test_builder_full`
   or add them there first).
3. Fill in the 20 `pass`-only bodies with real assertions once (1) exists.

## Related

- `feedback_when_an_assumption_falls_reaudit_what_was_left` (session memory)
  — a sweep's skipped/commented sites are its unreviewed ones.
