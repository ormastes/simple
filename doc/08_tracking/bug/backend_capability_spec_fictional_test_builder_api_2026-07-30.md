# backend_capability_spec.spl: 34 commented tests target a never-built capability-check API

- **Filed:** 2026-07-30
- **Severity:** low — dead test scaffolding, not a product regression
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  the 14 Group 1/3/4 tests are implemented and wired against real backend
  behavior; the 20 Group 2/5/6 bare-`pass` tests remain open (need real
  assertions written from scratch, not API wiring — separate lane).
- **Found via:** BCAP lane triage of `test/01_unit/compiler/backend/backend_capability_spec.spl`

## Resolution (lane MTB1, 2026-07-30)

Built `src/compiler/70.backend/mir_test_builder.spl` (module
`compiler.backend.mir_test_builder`, resolved via the `backend -> 70.backend`
symlink — NOT `src/compiler/70.backend/backend/`, which resolves to
`compiler.backend.backend.*` and is a different module path) as a thin
`MirTestBuilder`/`MirTestCase`/`BackendTarget` wrapper. `is_supported(target)`
replays the recorded ops against REAL backend entry points instead of a
hardcoded per-instruction table:

- `BackendTarget.LLVM` → `MirToLlvm.translate_binop` / `translate_simd_horizontal`,
  checking the emitted text (+ flushed `string_global_text`) for the real
  `"does not support"` unsupported-panic marker.
- `BackendTarget.Vulkan` → `VulkanBackend.compile_kernel` with a real `MirBody`
  (GPU atomics expand into the real required `GpuSharedAlloc` +
  `GetElementPtr` prerequisite sequence the thin `.gpu_atomic_add(dest, ptr,
  value)` call doesn't itself model).
- `BackendTarget.Cranelift` → a real AOT object-file compile via
  `cranelift_compile_module_direct` (there is no lighter single-instruction
  Cranelift entry point — its `cl_translate_*` helpers need a live builder
  context only a real module compile creates). This succeeded and is stable
  across repeated runs; no fallback to a hardcoded claim was needed.
- `BackendTarget.Interpreter` → `true` unconditionally, as an architectural
  fact (universal fallback every other backend's panic message names as the
  alternative), not a per-instruction guess.

All 14 Group 1/3/4 tests are now active. Two were adapted to a **real**
(not the originally-scaffolded assumed) outcome: "LLVM ... supports SIMD
operations" and "SIMD-heavy code ... prefers LLVM backend" both assumed the
LLVM backend supports SIMD reduction. Reading the real implementation
(`_MirToLlvm/aggregate_intrinsics.spl` `translate_simd_horizontal`) shows it
unconditionally panics `"LLVM backend does not support SIMD operation
{op_name}"` with no other definition overriding it — the LLVM (text) backend
genuinely does not implement SIMD lowering yet. Both tests were renamed and
adapted to assert that real negative outcome (`to_equal(false)`) instead of
the fictional positive one; both also fix a scaffold bug where the vector
register was declared as `vec_val` but referenced via the never-declared
`vec`. "pure arithmetic code ... selects any compiled backend" is wired
exactly as originally scaffolded (Cranelift AND LLVM both asserted true).

Final: `test/01_unit/compiler/backend/backend_capability_spec.spl` —
**Results: 20 total, 20 passed, 0 failed** (6 pre-existing + 14 newly wired),
stable across repeated runs.

Groups 2/5/6 (20 bare-`pass` tests, "Backend Error Messages"/"Backend
Capability Matrix"/"Capability Documentation") remain commented — they have
no assertions to wire, they need to be written from scratch. That work is
unchanged from the original BCAP triage below and is still open.

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

## Verification 2026-08-17 (content classification, fleet lane I)
PARTIALLY FIXED — reduced from 34 dead tests to 20, still STILL-OPEN.
Measured on `test/01_unit/compiler/backend/backend_capability_spec.spl` (529 lines):
- `src/compiler/70.backend/mir_test_builder.spl` now EXISTS.
- the import at :6 (`use compiler.backend.mir_test_builder.{MirTestBuilder, BackendTarget}`) is LIVE, not commented.
- 20 `it "` examples are live and 4 `describe` blocks are live; :189, :205, :216,
  :228 really call `MirTestBuilder.new()`.
- but 20 `# it "` examples inside 3 commented `# describe` blocks remain dead
  scaffolding (236 comment lines total).
So the "never-built API" half of this doc is resolved by content; the dead
scaffolding half is not. Remaining work is to either implement or DELETE the 20
commented examples — per CLAUDE.md, commented-out tests must not be left as
permanent NOTEs. Not done here: `src/compiler/70.backend/**` is explicitly
claimed by a sibling lane in this fleet.
