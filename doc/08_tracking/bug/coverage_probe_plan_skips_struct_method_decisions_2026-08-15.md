## Re-verified 2026-08-17 — reproducer GONE; defect NOT fixed; localized; BLOCKED on a seed rebuild

### 1. The named reproducer no longer exists

`src/lib/nogc_sync_mut/gpu/engine2d/vulkan_presenter.spl` is **not in the tree**
(`find src -name vulkan_presenter.spl` -> no output), and neither
`VulkanEngine2dPresenterReceipt` nor `VulkanEngine2dPresentDamageReceipt` appears
anywhere under `src/` (`grep -rn ... --include=*.spl src/` -> 0 hits). The spec
named in the doc still exists
(`test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl`)
but its subject is gone, so **this bug is unreproducible exactly as written**.
It is NOT thereby fixed — see 2 and 3.

### 2. It is a measurement defect, not a runtime one (confirmed directly)

Minimal probe (struct method, class method, and free `fn`, each with one
identical `if n > 0` decision, each driven through BOTH arms):

```
struct=true  class=true  free=true
structF=false classF=false freeF=false
```

All three declaration kinds execute and branch identically. Nothing is wrong
with struct-method execution — only with what coverage attributes to it. This
matches the doc's P3 severity.

### 3. New finding: `SIMPLE_COVERAGE` on the `run` path writes NOTHING

`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<path> bin/simple run <file>` prints
correct program output, **exits 0, and writes no coverage file at all** — not to
the requested `SIMPLE_COVERAGE_OUTPUT` path, and not to either default
(`build/coverage/coverage.sdn` per `coverage.rs:352`, `.coverage/coverage.sdn`
per `:335`). `find` over all three locations returns 0 files after the run.
A silent no-op that exits 0 is the same failure shape as the filed silent-green
test-runner defect: it cannot be distinguished from "coverage ran and found
nothing". Whatever the fix for the struct-method gap is, this needs to fail
loudly instead.

### 4. Localization — the MIR probe emitter is NOT the culprit

Instrumentation lives in the **Rust seed**, not in pure Simple:

* `src/compiler_rust/driver/src/exec_core.rs:562` — `compiler.set_coverage_enabled(true)`
* `src/compiler_rust/compiler/src/pipeline/codegen.rs:31,56` — `is_coverage_enabled()` -> `.with_coverage(...)`
* `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs` — the probe
  emitters (`emit_decision_probe`, `emit_condition_probe`, `emit_path_probe`,
  `emit_function_entry_probe`)
* `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1767` `lower_function(&mut self, func: &HirFunction)`
  calls `self.emit_function_entry_probe()?;` at **:1824**

That call site is **declaration-kind agnostic** — it fires for every
`HirFunction` with no `struct`/`class`/`impl` discrimination anywhere in the
path. So the gap is NOT "the probe planner skips struct methods" as the title
says. It must be either (a) upstream, in HIR item lowering, if `impl` blocks on
a `struct` do not yield `HirFunction`s at all, or (b) downstream, in report
file/line attribution. Narrowing between (a) and (b) is the next step, and
`src/compiler/50.mir/mir_coverage_probe_admission.spl` is only a validator, not
the builder — do not start there.

### 5. Blocker

Any fix is a **Rust seed change** (`src/compiler_rust/compiler/src/mir/lower/**`
or the HIR item walk) and cannot be verified without a seed rebuild + redeploy.
This lane is barred from building the main compiler, so no fix is attempted
here. Unblock = rebuild the seed, then re-run the section-2 probe and require
the struct row to report the same decision count as the class and free-fn rows.
The title should be corrected to "coverage attributes 0 decisions to struct
methods" once (a) vs (b) is settled.

# Coverage probe plan attributes 0 lines/decisions to executed struct methods

**Date:** 2026-08-15
**Status:** OPEN
**Severity:** P3 — coverage measurement blind spot, not a runtime defect

## Symptom

`src/lib/nogc_sync_mut/gpu/engine2d/vulkan_presenter.spl` struct methods
(`VulkanEngine2dPresenterReceipt.is_valid`,
`VulkanEngine2dPresentDamageReceipt.is_direct_partial_present`) demonstrably
execute under `bin/simple test --coverage` (11 assertions on their results
pass in
test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl),
yet the coverage report attributes **0/91 lines and 0/0 decisions** to the
module — any `@cover` threshold on it fails vacuously.

## Impact

Modules whose logic lives in struct methods (as opposed to free functions or
class methods) cannot be coverage-gated; per-layer coverage campaigns must
skip them, understating real coverage.

## Unblock

Extend the probe plan/runtime store attribution to struct-method bodies, or
document the scope limit in the coverage guide. Cross-check whether class
methods and free functions in the same file attribute correctly (they do in
sibling modules, e.g. vulkan_present_damage_gate.spl 9/9).
