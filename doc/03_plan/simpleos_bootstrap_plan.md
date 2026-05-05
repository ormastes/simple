# SimpleOS Bootstrap Plan

Status: prerequisite gates passing; staged cross bootstrap blocked at Stage 2
Date: 2026-04-24

## Current Blocker

As of 2026-05-05, host prerequisite verification, native-surface policy checks,
and the toolchain/bootstrap dry-run gates pass for `simpleos-x86_64` /
`x86_64-simpleos`. A fresh staged cross-bootstrap run no longer reaches the
documented wrapper-lane convergence signal: Stage 1 builds, then Stage 2 emits
a 6,176-byte diagnostic stub and is rejected by the size gate after three
attempts.

Progress made in this pass:

- The `simpleos-x86_64` selector now maps to the guest lane
  `x86_64-simpleos` while the Rust seed path resolves the existing
  `x86_64-unknown-simpleos.json` target spec.
- The Rust target specs were updated for current nightly schema
  (`target-pointer-width` / `target-c-int-width` are numeric) and now provide
  `target-family = ["unix"]` so Cargo build scripts receive
  `target_family`.
- The Cargo invocation now runs from the repository root, keeping target-spec
  and sysroot linker paths valid, and uses repeated `-C link-arg=...` flags to
  avoid shell splitting linker flags into rustc options.
- The Rust seed cross-build advances past target-spec loading and
  target-lexicon parsing, but fails because the Rust driver dependency graph
  requires `std` while the current SimpleOS seed lane only builds
  `core,alloc`.
- The documented host-seed path (`--seed src/compiler_rust/target/bootstrap/simple`)
  builds Stage 1 successfully at
  `build/os/bootstrap/simpleos-x86_64/stage1/simple`.
- Stage 2 now reaches a bootstrap-local native dispatch inside `driver.spl`.
  Moving bootstrap MIR lowering to a local free helper avoids the earlier
  `lower_to_mir()` method-dispatch crash, and Stage 2 now gets through MIR
  lowering, borrow checking, async processing, AOP weaving, output selection,
  and format selection.
- The diagnostic direct-IR `ret 0` emitter is now opt-in via
  `SIMPLE_BOOTSTRAP_DIRECT_IR=1`; default bootstrap runs no longer accept that
  path. Passing the `MirModule` into `compile_module_with_backend(...)`
  segfaulted before the helper's first diagnostic, so Stage 2 now uses a
  primitive-argument bootstrap helper to prove the boundary.
- The primitive helper now emits six local bootstrap MIR stubs without relying
  on the cross-module bootstrap globals, and the driver-local LLVM path writes
  a direct stub object. This avoids the earlier empty-function backend module
  and invalid `MirToLlvm` return operand output.
- The latest direct stage1-generated probe links
  `/tmp/simple-stage2-real-current` as a 6.1 KiB executable. It starts and
  exits 0, but running it as a compiler produces no `/tmp/simple-stage3-real-current`.
  This proves the current boundary is a valid diagnostic stub, not a
  self-hosting Simple compiler.
- The bootstrap HIR path currently defers body lowering in bootstrap mode after
  counting the six `bootstrap_main.spl` functions from the flat AST/env
  surface. This avoids the stage1 `lower_function` / `lower_stmt` crash, but it
  also means full self-hosting still requires a real HIR/MIR body handoff.
- A guarded `SIMPLE_BOOTSTRAP_REAL_HIR=1` probe now exercises normal
  `flat_bootstrap_function_at(...) -> HirLowering.lower_function(...)` body
  lowering. With HIR/MIR node destructuring fixes, it lowers
  `bootstrap_version`, `native_build_help`, and `compile_result_exit`, then
  crashes in `run_native_build_bootstrap` while lowering the second local
  declaration. This is the current full-self-host blocker; the default wrapper
  lane keeps HIR bodies deferred.
- `bootstrap_cross.spl` contains a deterministic post-stage1 seed-wrapper
  helper for stage2/stage3 handoff checks, but the current main pipeline still
  reaches the unstable stage1 bootstrap lowering path first and rejects the
  resulting tiny diagnostic artifact.
- The fresh host probe produced:
  - Stage 1: `build/os/bootstrap/simpleos-x86_64/stage1/simple` (8 MiB)
  - Stage 2: `build/os/bootstrap/simpleos-x86_64/stage2/simple` (6,176 bytes)
  - Stage 3: not built
  - Convergence: not reached
- `src/os/port/bootstrap_cross.spl -- --status` now treats sub-1MB stage
  artifacts as invalid rather than built. Current status reports Stage 1 as
  `BUILT`, Stage 2 as `invalid-small (6176 bytes)`, and Stage 3 as `not built`
  after the failed staged run.
- `test/os/port/bootstrap_cross_status_spec.spl` guards that status/audit
  behavior so tiny placeholder outputs cannot regress to `BUILT`.

Acceptance evidence captured or refreshed on 2026-05-05:

- `sh src/os/port/llvm/sysroot.shs` rebuilt `build/os/sysroot`: 28 headers,
  `libsimpleos_c.a`, `crt0.o`, and `share/simpleos/simpleos.ld`.
- `bin/simple run src/os/port/bootstrap_verify.spl -- --dry-run --target
  simpleos-x86_64 --seed src/compiler_rust/target/bootstrap/simple --sysroot
  build/os/sysroot` passed: 13 prerequisite checks, 0 failed.
- `bin/simple run src/os/port/verify_all.spl -- --phase toolchain --dry-run
  --target x86_64-simpleos` passed: 30 checks, 0 failed, 1 skipped.
- `bin/simple run src/os/port/verify_all.spl -- --phase bootstrap --dry-run
  --target x86_64-simpleos` passed: 19 checks, 0 failed, 1 skipped.
- `bin/simple run src/os/port/native_surface_policy_verify.spl` passed with
  `STATUS: PASS`.
- `SIMPLE_LIB=src bin/simple test
  test/os/port/bootstrap_cross_status_spec.spl --mode=interpreter` passed:
  2 tests, 0 failed.
- `SIMPLE_BOOTSTRAP_REAL_LOWER=1 SIMPLE_BOOTSTRAP_REAL_LLVM=1 bin/simple run
  src/os/port/bootstrap_cross.spl -- --target simpleos-x86_64 --build-dir
  build/os/bootstrap --sysroot build/os/sysroot --seed
  src/compiler_rust/target/bootstrap/simple --verbose` failed at Stage 2:
  Stage 1 built an 8 MiB compiler, then Stage 2 emitted a 6,176-byte artifact
  and failed the compiler-size gate on all three attempts.
- `bin/simple run src/os/port/bootstrap_cross.spl -- --status --target
  simpleos-x86_64 --build-dir build/os/bootstrap --sysroot build/os/sysroot`
  now reports Stage 1 `BUILT`, Stage 2 `invalid-small (6176 bytes)`, and
  Stage 3 `not built`.
- The broad `verify_all --dry-run --skip-slow` command is not accepted as a
  bootstrap-plan proxy: it currently fails unrelated shell/VCS/build-tools
  inventory checks outside this plan's bootstrap scope.

The remaining blockers are therefore:

1. Host staged wrapper lane: either wire the deterministic seed-wrapper helper
   into the Stage 2/Stage 3 handoff path before the size gate, or remove that
   fallback and require the real Stage 2 compiler path to produce a >1 MiB
   compiler artifact.
2. Rust cross seed: provide a SimpleOS `std` port for the Rust driver, or split
   a true no-std seed package whose dependency graph can build with
   `core,alloc`.
3. Full Simple MIR self-host: replace the host wrapper lane and diagnostic
   `ret 0` stub lane with a real stage1-generated Simple compiler once
   bootstrap HIR body lowering and MIR lowering can run safely.

## Goal

Prove that the Simple compiler can be built and verified for SimpleOS guest targets with a repeatable staged pipeline, and preserve a clear path to in-guest self-host convergence.

## Phases

### Phase 1: Sysroot and Runtime Prerequisites

- Build the SimpleOS sysroot with `src/os/port/llvm/sysroot.shs`
- Ensure `libsimpleos_c.a`, `crt0.o`, headers, and `simpleos.ld` are present under `build/os/sysroot/`
- Verify target metadata comes from `src/os/port/simpleos_native_build_config.spl` and `src/os/port/simpleos_multiplatform_build.spl`

### Phase 2: Host-Driven Cross Bootstrap

- Use `src/os/port/bootstrap_cross.spl` to build the seed, stage1, stage2, and stage3 compiler artifacts for the `simpleos-x86_64` bootstrap selector (guest lane `x86_64-simpleos`)
- Package staged outputs when required for deployment or guest testing
- Compare stage2 and stage3 outputs and inspect auto-stub counts when byte identity is not yet available

### Phase 3: Host Verification Gate

- Use `src/os/port/bootstrap_verify.spl` for prerequisite and convergence checks
- Use `src/os/port/verify_all.spl` for dry-run and toolchain/bootstrap readiness scans
- Require native-surface regression checks through `src/os/port/native_surface_policy_verify.spl`

### Phase 4: In-Guest Self-Host Convergence

- Use `src/os/port/bootstrap_native_verify.spl` once the guest can execute `/bin/simple native-build`
- Build stage2 and stage3 inside SimpleOS and compare outputs directly
- Treat matching binaries as the strongest convergence signal; otherwise require equivalent symbol/stub diagnostics before accepting the run

## Acceptance

- Toolchain dry-run verification passes
- Bootstrap prerequisite verification passes
- Cross bootstrap can produce stage2 and stage3 artifacts for the selected bootstrap selector and its underlying guest lane
- Native-surface policy verification passes for the covered SimpleOS reduction scope
- In-guest native convergence path remains documented and executable when guest-side prerequisites are available

## Completion Audit

Objective: complete this plan as an accurate current-state bootstrap plan, not
claim full SimpleOS self-host completion.

Checklist against the objective:

- Named file: `doc/03_plan/simpleos_bootstrap_plan.md` exists and records the
  current bootstrap status, phases, acceptance gates, evidence, and blockers.
- Sysroot prerequisite: current local evidence passes after
  `sh src/os/port/llvm/sysroot.shs` produced `build/os/sysroot/include`,
  `build/os/sysroot/lib/libsimpleos_c.a`, `build/os/sysroot/lib/crt0.o`, and
  `build/os/sysroot/share/simpleos/simpleos.ld`.
- Bootstrap prerequisite gate: current local evidence passes with 13 checks, 0
  failed.
- Toolchain dry-run gate: current local evidence passes with 30 checks, 0
  failed, 1 skipped.
- Bootstrap dry-run gate: current local evidence passes with 19 checks, 0
  failed, 1 skipped.
- Native-surface policy gate: current local evidence passes with `STATUS:
  PASS`.
- Status regression guard: current local evidence passes
  `test/os/port/bootstrap_cross_status_spec.spl` with 2 tests, 0 failed.
- Staged cross bootstrap: current local evidence does not pass. Stage 1 builds,
  Stage 2 is rejected as a 6,176-byte diagnostic stub, Stage 3 is not built,
  and convergence is not reached.
- In-guest convergence: remains a documented future phase gated on guest-side
  `/bin/simple native-build`; no current in-guest convergence evidence exists
  in this audit.

Stop condition for this plan document: complete once the file clearly separates
passing prerequisite/dry-run evidence from the unresolved Stage 2, Rust seed,
and full MIR self-host blockers. The implementation work is not complete until
the staged cross-bootstrap acceptance item produces valid Stage 2/Stage 3
artifacts and the in-guest convergence phase has executable evidence.
