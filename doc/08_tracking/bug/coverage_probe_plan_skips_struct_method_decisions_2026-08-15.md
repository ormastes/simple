## Re-verified 2026-08-17 — reproducer GONE; defect NOT fixed; localized; BLOCKED on a seed rebuild

Status: OPEN (P3) — re-verified 2026-08-17 by EXECUTION (not inspection). Two
changes to the record: coverage output is no longer a silent no-op, and the
defect is NOT struct-specific.

Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(59537240 bytes, 2026-08-17 12:58:51 UTC).

```
$ SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<scratch>/cov.sdn \
    bin/simple run <scratch>/cov.spl
struct=true class=true free=true
structF=false classF=false freeF=false
$ ls -la <scratch>/cov.sdn
-rw-rw-r-- 1 ... 532 Aug 17 13:20 <scratch>/cov.sdn
```

Probe file: struct method, class method and free `fn`, each with one identical
`if n > 0` decision, each driven through BOTH arms.

* **Section 3 above is now STALE** — `SIMPLE_COVERAGE_OUTPUT` on the `run` path
  DOES write a file now (532 bytes, at the requested path).
* **The written report is entirely empty**, and that is the fresh finding:
  `total_files: 0, total_lines: 0, total_functions: 0, total_decisions: 0,
  total_conditions: 0`, with `decision_percent: 100.0` from a 0/0 division.
  The class method and the free function are attributed **zero** as well, so the
  gap is NOT struct-method-specific as the title claims — nothing at all is
  instrumented on the `run` path. The vacuous `100.0%` is the same silent-green
  shape flagged before, just relocated from a missing file to an empty one.
* **Still out of reach in pure Simple, same blocker as before:** all
  instrumentation lives in the Rust seed
  (`src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs`,
  `driver/src/exec_core.rs:562`, `pipeline/codegen.rs`). No `.spl` fix exists;
  `src/compiler/50.mir/mir_coverage_probe_admission.spl` is a validator only.
  Left OPEN with the failing evidence above rather than fixed.

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

## 2026-08-17 triage — BLOCKED in this lane, with the reason

Not closed and not fixed. Scoping pass located the candidate owners
(`src/compiler/10.frontend/core/ast_coverage_inventory.spl`,
`src/compiler/50.mir/mir_coverage_probe_admission.spl`, and the seed's
`src/compiler_rust/compiler/src/interpreter_extern/coverage.rs`); neither
`.spl` file branches on struct-vs-class-vs-free-function at all, which points
attribution at the seed side.

Two concrete blockers, stated rather than worked around:

1. `interpreter_extern/coverage.rs` currently carries ~1,369 lines of
   uncommitted changes from a parallel session in this shared working tree.
   Editing it now would either clobber that work or produce a fix that cannot
   be attributed; and any seed change needs a rebuild to take effect.
2. Confirming a fix requires a real coverage run
   (`SIMPLE_COVERAGE=1 bin/simple test <spec> --no-cache --no-cover-check
   --timeout 1800`), which exceeds this lane's one-process-at-a-time budget.

Unblock: once the seed changes in flight have landed, re-run the
`vulkan_present_damage_gate_branch_coverage_spec.spl` coverage measurement and
attribute struct-method bodies in the probe plan. Severity stays P3.

## Evidence 2026-08-17 (fleet worker A, rust-seed slice)

Content check of `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs`
(3,777 bytes, registered as `mod lowering_coverage;` at `mir/lower/mod.rs:9`):

`grep -n "struct_method\|StructMethod\|impl_method\|methods"` returns **zero
matches**. The probe planner has no struct-method awareness of any kind, so the
gap this doc describes is confirmed present in current source rather than
merely stale prose.

**Verdict: STILL-OPEN, confirmed by content.** Not fixed; this is a measurement
gap (missing instrumentation), not a wrong-answer defect.
**Not proven:** no execution evidence — see "Execution blocked" below.
