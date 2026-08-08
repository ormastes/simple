# SimpleOS Bootstrap Plan

Status: prerequisite gates passing; staged cross bootstrap blocked at Stage 2
Date: 2026-06-06

## Current Blocker

As of 2026-06-06, host prerequisite verification, native-surface policy checks,
and the toolchain/bootstrap dry-run gates pass for `simpleos-x86_64` /
`x86_64-simpleos`. Seed-wrapper fallback generation has been removed from the
minimal bootstrap CLI and driver bootstrap helper. Bootstrap native-build must
now either produce a real Simple compiler artifact through Simple lowering and
native codegen or fail closed.

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
- The diagnostic direct-IR `ret 0` emitter, driver-local LLVM stub emitter, and
  seed-wrapper emitter now return codegen errors instead of producing successful
  artifacts. `src/app/cli/bootstrap_main.spl` also refuses to generate a C
  seed wrapper.
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
- The remaining Stage 2 path is the real Simple HIR/MIR/native path. If that
  path cannot lower `run_native_build_bootstrap`, the run must fail with a
  compiler error rather than falling back to Rust, seed exec, or diagnostic
  stubs.
- The fresh host probe produced:
  - Stage 1: `build/os/bootstrap/simpleos-x86_64/stage1/simple` (8 MiB)
  - Stage 2: `build/os/bootstrap/simpleos-x86_64/stage2/simple` (6,176 bytes)
  - Stage 3: not built
  - Convergence: not reached
- `src/os/port/bootstrap_cross.spl -- --status` now treats sub-1MB stage
  artifacts as invalid rather than built. Current status reports Stage 1 as
  `BUILT`, Stage 2 as `invalid-small (6176 bytes)`, and Stage 3 as `not built`
  after the failed staged run.
- `test/02_integration/os/port/bootstrap_cross_status_spec.spl` guards that status/audit
  behavior so tiny placeholder outputs cannot regress to `BUILT`.
- `test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl` guards
  the fail-closed policy: no Rust seed path, `execv`, `SIMPLE_BOOTSTRAP_SEED`,
  or `ret i64 0` stub remains in the bootstrap CLI/driver fallback surface.
- `src/app/io/cli_compile_part2.spl` rejects `rust-hosted`, `rust_hosted`,
  and legacy `hosted` runtime bundles before native-build delegation. It now
  preserves delegated `auto`, `simple-core`, and `core-c-bootstrap` lane names
  so pure Simple and C-bootstrap runtime selection remain distinct.
- The Rust native-build implementation now removes the hosted/native_all lane
  as a selectable runtime bundle. `simple-core` links only an ABI-complete pure
  Simple `libsimple_runtime.a`; `core-c-bootstrap` links the C bootstrap
  `libsimple_runtime.a`; removed aliases such as `hosted`, `all`,
  `rust-hosted`, `hosted-runtime`, and `rust-runtime` fail closed. Runtime
  discovery no longer scans `src/compiler_rust/target/**` or
  `SIMPLE_NATIVE_ALL_PATH` for fallback archives.
- `bin/simple_mcp_server` and `bin/simple-interp` now resolve only Simple
  release/self-hosted paths; they no longer search `src/compiler_rust`.

Acceptance evidence refreshed on 2026-06-06:

- `SIMPLE_LIB=src bin/simple check src/app/cli/bootstrap_main.spl
  src/compiler/80.driver/driver_bootstrap.spl` passed.
- `SIMPLE_LIB=src bin/simple check
  test/02_integration/os/port/bootstrap_cross_status_spec.spl
  test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl` passed.
- `SIMPLE_LIB=src bin/simple test
  test/02_integration/os/port/bootstrap_cross_status_spec.spl
  --mode=interpreter --clean` passed: 2 tests, 0 failed.
- `SIMPLE_LIB=src bin/simple test
  test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl
  --mode=interpreter --clean` passed: 2 tests, 0 failed.
- `rg -n "compiler_rust|execv|SIMPLE_BOOTSTRAP_SEED|ret i64 0"
  src/app/cli/bootstrap_main.spl src/compiler/80.driver/driver_bootstrap.spl`
  returned no matches.
- `SIMPLE_LIB=src bin/simple test
  test/02_integration/os/port/runtime_bundle_policy_spec.spl
  --mode=interpreter --clean` passed: 1 test, 0 failed.
- `cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler
  -p simple-driver -p simple-native-all` passed with the existing runtime
  extern-signature/interpreter unused-assignment warnings.
- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler
  runtime_bundle -- --nocapture` passed: 21 matching tests, 0 failed.
- `src/compiler_rust/target/debug/simple native-build --runtime-bundle
  core-c-bootstrap --entry examples/01_getting_started/hello_native.spl
  --source examples -o /tmp/simple_core_c_runtime_probe --backend cranelift
  --clean --strip && /tmp/simple_core_c_runtime_probe` passed and printed
  `Hello World`.
- The tracked `bin/release/x86_64-unknown-linux-gnu/simple` was rebuilt from
  `simple-driver`. `bin/simple native-build --help` now lists only
  `auto, simple-core, core-c-bootstrap`; `--runtime-bundle rust-hosted` and
  `SIMPLE_NATIVE_RUNTIME_BUNDLE=hosted` fail closed; `bin/simple
  native-build --runtime-bundle core-c-bootstrap ...hello_native.spl` builds
  and runs `Hello World`.
- A fake-repo smoke with only `src/compiler_rust/target/release/simple`
  available made `bin/simple_mcp_server` exit 127 with
  `checked Simple release/self-hosted paths only`, proving it did not use the
  Rust fallback.
- `bin/simple-interp --version` returned `Simple Language v1.0.0-beta` through
  the deployed Simple binary.

Earlier acceptance evidence captured or refreshed on 2026-05-05:

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
  test/02_integration/os/port/bootstrap_cross_status_spec.spl --mode=interpreter` passed:
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

1. Full Simple MIR self-host: complete real stage1-generated HIR body lowering
   and MIR lowering for `run_native_build_bootstrap` and the full bootstrap CLI.
2. Native artifact production: make the real Simple backend/link path emit a
   >1 MiB Stage 2 compiler artifact without Rust seed exec or diagnostic stubs.
3. SimpleOS cross seed: keep the cross lane on Simple plus the C/sysroot
   surface; do not revive the Rust seed fallback as a substitute for the real
   Stage 2 compiler path.

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
  `test/02_integration/os/port/bootstrap_cross_status_spec.spl` with 2 tests, 0 failed.
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
