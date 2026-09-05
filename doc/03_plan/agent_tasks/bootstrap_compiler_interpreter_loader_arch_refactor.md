<!-- codex-architecture -->
# Agent Task Breakdown - Bootstrap / Compiler / Interpreter / Loader Refactor

Feature: `bootstrap-compiler-interpreter-loader-arch-refactor`

## Scope

Refactor planning for the bootstrap driver, Simple compiler layer map,
interpreter load path, and loader/SMF path. This is an architecture and
ownership lane first; code edits should stay in their lane-specific plans until
interfaces are agreed.

Current status, 2026-07-06:

- Bootstrap policy is documented in
  `doc/02_requirements/app/build/bootstrap.md`.
- `scripts/bootstrap/bootstrap-from-scratch.sh` already defaults to `dynload`,
  accepts only `dynload` and `one-binary`, and gates cargo behind
  `--full-bootstrap`.
- Dependency tracing is conservative rather than precise: it invalidates the
  native cache on compiler/app/lib source hashes plus AOP, MDSOC/weaving,
  loader, interpreter, execution, library, and native-build `SIMPLE_*` knobs.
- Remaining architecture work is Track B-D below: public compiler layer
  facades, interpreter loader alignment, and shared loader/SMF contracts.
- Current known bootstrap blocker remains stage 2/3 self-host verification
  instability, tracked in
  `doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md`.

Primary areas:

- `scripts/bootstrap/`
- `src/compiler/80.driver/`
- `src/compiler/10.frontend/core/interpreter/`
- `src/compiler/95.interp/`
- `src/compiler/99.loader/`

## Existing Anchors

- `doc/04_architecture/compiler/00_compiler_architecture.md`
- `doc/04_architecture/compiler/bootstrap_build_modes.md`
- `doc/03_plan/runtime/loader_shared_core_refactor.md`
- `doc/03_plan/compiler/bootstrap/simple_seed_loader_restart_plan_2026-06-01.md`
- `doc/07_guide/tooling/pure_simple_tooling.md`

## Non-Goals

- No Rust fallback expansion.
- No full loader merge before shared contracts are proven.
- No interpreter-only grammar fork.
- No third native-build mode beyond `dynload` and `one-binary`.

## Architecture Invariants

- One frontend grammar and AST contract feeds compiler, interpreter, and loader.
- Numbered compiler layers remain the public map; sibling layers use facades or
  extracted common nodes, not private subtree imports.
- Loader and interpreter consume shared contracts for module resolution, SMF
  metadata, diagnostics, and session/cache identity.
- `dynload` is the default rebuild mode; `one-binary` is the conservative
  monolithic mode.
- Dependency tracing must be conservative around AOP/MDSOC weaving, loader ABI,
  interpreter adapters, compiler ABI, and runtime-family boundary changes.
- Rust seed tooling must identify itself with a `WARNING` on direct use and
  must not become the default tool path.

## Work Split

### Track A - Bootstrap / Driver

- Keep normal bootstrap pure-Simple-only: no cargo unless `--full-bootstrap`.
- Keep `scripts/bootstrap/bootstrap-from-scratch.sh` cache invalidation aligned
  with actual native-build source roots and AOP/MDSOC env knobs.
- Owner files: `scripts/bootstrap/`, `src/app/cli/bootstrap_main.spl`,
  `src/compiler/80.driver/`.

### Track B - Compiler Layering

- Review numbered compiler layers for imports that skip public surfaces.
- Extract shared diagnostics, metadata, and resolver contracts upward when two
  siblings need them.
- Owner files: `src/compiler/00.common/`, `src/compiler/80.driver/`,
  `src/compiler/85.mdsoc/`.

### Track C - Interpreter Load Path

- Align interpreter source/module loading with the same resolver and diagnostic
  contracts used by the driver.
- Keep interpreter-specific execution state behind interpreter facades.
- Owner files: `src/compiler/10.frontend/core/interpreter/`,
  `src/compiler/95.interp/`.

### Track D - Loader / SMF Path

- Continue the shared-core loader lane without merging lifecycle and
  compatibility loaders prematurely.
- Extract common SMF, relocation, symbol, and metadata contracts before sharing
  hot-path execution code.
- Owner files: `src/compiler/99.loader/`, `src/compiler/70.backend/linker/`.

### Track E - Verification / Docs

- Keep generated/manual SPipe docs current for touched specs.
- Run focused bootstrap, compiler, interpreter, and loader checks once per
  acceptance criterion; stop after the configured verify/fix cap.

## Agent Ownership

- Sidecar lanes: bootstrap policy explorer, native-build/dependency explorer,
  architecture cross-link explorer.
- Merge owner: main Codex thread.
- Final reviewer: normal/high-capability Codex verification.

## Verification Gates

- `bin/simple check src/app/cli/native_build_main.spl`
- `bin/simple test test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl --mode=interpreter --clean --timeout 60 --sequential`
- `bin/simple test test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl --mode=interpreter --clean --timeout 60 --sequential`
- Focused loader/interpreter specs for any future Track C/D code changes.
- `find doc/06_spec -name '*_spec.spl' | wc -l` must print `0`.

## Stop Conditions

- A proposed shared contract requires crossing private sibling subtrees.
- Stage 2/Stage 3 bootstrap fails without a phase-specific diagnostic.
- AOP or loader ABI changes would make incremental cache reuse ambiguous.
- Verification would require rerunning an already-green check in the same
  session.
