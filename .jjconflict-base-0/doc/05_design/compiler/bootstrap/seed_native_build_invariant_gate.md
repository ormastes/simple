# Phase 3 — seed native-build invariant gate

## The missing invariant

Regression `d312b8e4253` ("defer lazy imports until first use") broke the Rust
seed's ability to native-build **any multi-file `.spl` project**: importing
modules got a fresh/empty instance of the owner module's globals instead of
the shared one, surfacing as `error: semantic: array index out of bounds` /
`expr_tag OOB` while parsing file 1 of a real compile
(`doc/08_tracking/bug/seed_interp_defer_lazy_imports_module_globals_2026-07-24.md`).
Nothing routine caught it; it was found later by manual bisection, and every
redeploy since has depended on keeping a pre-regression seed (`906b85d1420`)
alive as a workaround.

## Does an existing gate already cover this? Not fully — two near-misses, both with real gaps

1. **`candidate_frontend_smoke()`** in
   `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` already
   native-builds a fixture (`fixtures/p2_add.spl`) with a candidate binary and
   asserts stdout. But:
   - It only runs from `bootstrap_stage_sanity()`, called at
     `scripts/bootstrap/bootstrap-from-scratch.sh:724` (stage2) and `:776`
     (stage3) — i.e. only on binaries produced by *already using* the seed to
     compile the pure-Simple tree, and only inside a full bootstrap run (T3
     tier per `.claude/rules/bootstrap.md`, not something run routinely).
   - `p2_add.spl` is a **single file with no imports**. It cannot exercise
     cross-module module-global aliasing — the exact mechanism that broke.
     A seed with this regression could plausibly still pass this check.
2. **`scripts/check/check-nvme-rv32-minimal-live.shs`** genuinely
   native-builds a real multi-module project with the seed (`--source
   "$SRC_DIR"`, `TIMEOUT_SECS=90` per build) and is in fact how this class of
   bug is supposed to be caught per the bug doc's own fix requirement #3. But
   it also boots QEMU, needs a full firmware source tree, costs 90s+ per
   build (two builds + a QEMU boot), and is scoped to the NVMe/rv32 feature —
   not something anyone runs as a general "is the seed still sane" check on
   every push.

Neither is a **cheap, general, routine** gate on the raw seed. This is a real
gap, not a duplicate — so a new gate is justified.

## The new gate

- **Script:** `scripts/check/check-seed-native-build-invariant.shs`
- **Fixture:** `scripts/check/cert/redeploy_gate/fixtures/seed_cross_module/{owner.spl,main.spl}`
  (added alongside, not inside, the existing flat `fixtures/` files since this
  is the first fixture that needs two files). `owner.spl` defines a
  module-level global (`val ITEMS: [i64] = [2, 3]`) behind a plain function;
  `main.spl` does `use owner.owner_items` and prints `xs[0] + xs[1]`, i.e.
  `5` — same expected-output convention as `p2_add.spl`, but crucially spans
  a `use` import, which `p2_add.spl` never exercises.

### What it does
1. Resolves a seed binary (arg 1, default
   `src/compiler_rust/target/bootstrap/simple[.exe]`, relative to repo root).
   **Fails closed** if missing/non-executable — a diagnostic naming the exact
   `cargo build` recipe, not a skip, because a gate that silently no-ops on a
   missing prerequisite is worse than no gate.
2. Runs `SEED native-build --backend cranelift --source <fixture-dir> --entry
   main.spl --mode one-binary -o <tmp>/probe_bin`, bounded by a `timeout`
   (default 60s build / 5s exec / 1s kill-grace, all env-overridable), reusing
   the `timeout`/`gtimeout` lookup already defined in
   `candidate_frontend_admission.shs` (sourced, not duplicated).
3. On build failure: prints the build-log tail and fails with a message
   naming the invariant ("a seed built from this tree cannot native-build a
   .spl file").
4. On build success: executes the probe binary and asserts stdout is exactly
   `5`. A wrong-but-present value fails with a distinct message ("cross-module
   global read is wrong, not merely a build failure") so a future regression
   that corrupts data without erroring is also caught.
5. One `PASS`/`FAIL` line, matching the style of `redeploy_gate.shs`.
   `cranelift` backend by default (no LLVM dependency) to keep it cheap;
   overridable via `SEED_GATE_BACKEND`.

### Runtime cost
- **This script alone, given a pre-built seed:** a couple of seconds
  (cranelift, two tiny files, `--mode one-binary`) — same order of magnitude
  as the existing `p2_add.spl` probe in `candidate_frontend_smoke`.
- **Including a seed build**, which this script deliberately does NOT do
  itself: a `cargo build --profile bootstrap -p simple-driver` is a single
  Rust crate compile — seconds when the seed crate is unchanged (cargo
  no-op), on the order of a minute or so cold/dirty. This is far cheaper than
  a full T3 bootstrap (which additionally self-hosts the entire pure-Simple
  compiler) and cheaper than `check-nvme-rv32-minimal-live.shs`'s 90s+
  firmware build + QEMU boot.

## Where to wire it in

1. **Primary: CI / pre-push path-scoped, mirroring `bootstrap.md`'s own
   `alwaysApply: false` path scope** (`src/compiler_rust/**`,
   `scripts/bootstrap/**`, `build/bootstrap/**`). A step that runs only when
   those paths changed:
   ```
   cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver --features llvm
   sh scripts/check/check-seed-native-build-invariant.shs
   ```
   This directly targets the failure mode: it runs on every change to the
   seed compiler itself, before that seed is trusted for anything downstream,
   without paying for a pure-Simple self-host.
2. **Secondary: inside `bootstrap-from-scratch.sh`, right after `seed_bin` is
   resolved (line ~521), before it is used to build stage2** (the
   `bootstrap_native_build_main` call around line 487). Today the earliest
   seed-sanity check (`bootstrap_stage_sanity`) only runs on the *output* of
   using the seed (stage2/stage3), so a broken seed fails opaquely mid-build
   ("expr_tag OOB") deep in a stage2 log instead of with a clear, named
   diagnostic before any expensive work starts. This is a recommendation, not
   implemented here (out of scope — this lane only delivers the gate script
   and fixture; wiring it into `bootstrap-from-scratch.sh` is a follow-up
   edit to that file, deliberately left to a session that can also run the
   expensive path to confirm it doesn't break the pipeline's control flow).
3. **Not** `bin/simple build check` / general pre-commit — those run on every
   commit regardless of whether `src/compiler_rust` changed, and requiring a
   fresh cargo build of the seed on every commit (even docs-only ones) would
   violate "keep it CHEAP enough to run routinely" in the opposite direction.
   Path-scope it.

## What was validated vs. what remains unproven

**Validated (stub seed, no real cargo/native-build run):**
- Shell syntax (`sh -n`) is clean.
- `REPO_ROOT` path resolution — caught and fixed a real bug: the first draft
  computed `SCRIPT_DIR/..` (one level, landing in `scripts/`) instead of
  `SCRIPT_DIR/../..` (two levels, landing at repo root), which silently
  pointed the default seed path at the wrong tree. Fixed and re-verified.
- Fail-closed on missing seed binary (both default-path and explicit-arg
  cases), with a diagnostic naming the exact build recipe.
- `--help` output.
- Every failure branch, via a stub `simple` script driven by
  `STUB_SCENARIO`: `build_fail` (native-build exits 1, log tail printed),
  `no_output` (native-build exits 0 but writes no file), `probe_crash`
  (probe binary exits nonzero), `probe_wrong` (probe prints `0` instead of
  `5`) — each produces a distinct, correctly-worded `FAIL` line and exit 1.
- The success path (`pass` scenario): stub probe prints `5`, gate prints
  `PASS` and exits 0.
- Absolute vs. relative seed-path argument resolution.
- Temp-directory cleanup via the `trap ... 0` (no leftover
  `seed-native-build-invariant.*` dirs after any run).

**NOT validated (explicitly, per lane rules — no heavy builds, don't compete
with the other lanes doing real seed/bootstrap builds):**
- Whether a **real** seed binary actually native-builds the `owner.spl` /
  `main.spl` fixture correctly today (i.e., whether main currently PASSes).
- Whether `use owner.owner_items` is exactly the right import spelling for a
  two-file `--source <dir>` fixture (modeled on the documented
  `use core.resource_registry.ResourceRegistry` pattern in
  `doc/07_guide/quick_reference/syntax_quick_reference.md`, but not compiled
  against a real seed/compiler).
- Whether this exact fixture would in fact have failed on `d312b8e4253` (the
  bisect log describes the trigger mechanism precisely — deferred lazy
  imports + cross-module module-global reads — but I could not run the
  workaround-seed-vs-HEAD-seed bisect myself to confirm this specific
  two-file repro reproduces it; the real compiler source tree did, per the
  existing bisect table).
- The `cranelift` backend path specifically (candidate_frontend_smoke also
  defaults to cranelift, so this follows precedent, but wasn't exercised here
  since no real seed was built).

**Recommendation for whoever picks this up next:** first real-seed run should
be `sh scripts/check/check-seed-native-build-invariant.shs` against a freshly
`cargo build`'d seed on current `main` (post-workaround-seed fix), confirming
PASS, then temporarily re-checking out the `d312b8e4253`-broken seed tree
(same recipe as the bug doc's own bisect) to confirm this gate FAILs against
it — that closes the loop on "does this gate actually catch the regression it
was written for."
