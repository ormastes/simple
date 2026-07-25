# Stage-4 full-CLI compile "spins forever" — not a hang, a legitimate but
# unbudgeted 662→1278+ file re-compile triggered by the CLI importing the
# compiler's own driver

**Date:** 2026-07-18 · **Lane:** S77 · **Status:** OPEN — diagnosed with a
minimal deterministic repro; root mechanism named; no source fix applied
(see "Why no fix" below)

## Summary

Stage 4 of the bootstrap (the pure-Simple Stage-3 binary compiling the full
CLI, `--entry src/app/cli/main.spl`, `--mode one-binary`) appears to "spin
forever": single CPU-bound thread, RSS growing without a plateau, zero
relevant log output, no `.o` files, for 11+ minutes (prior lanes report up to
~20+ min / 10+ GiB RSS before giving up). This was reproduced twice before
(lane S66) and is well documented in sibling bug docs (see Related, below).

**This lane's finding: it is not an infinite loop.** A minimal, deterministic,
single-import repro (fully isolated from the full 1200s+ command, runs in
~15 min worst case, most of it visibly progressing) shows the process is
doing real, bounded, sequential work — compiling hundreds of legitimate
files one at a time — not spinning in one function. The "spin" is this
sequential compile simply taking far longer than any bounded investigation's
patience/timeout, compounded by zero incremental progress output during the
compile-files phase for long stretches (verbose mode only prints every 10th
file).

## What was refuted

The task brief's leading hypothesis was "entry-closure/dependency scanning
re-visiting modules without memoization or cycle detection" (mirroring the
interpreter module-loader gap S64 found). **This is refuted for both
closure-discovery implementations in this codebase:**

- The pure-Simple closure walker (`src/compiler/80.driver/driver.spl`,
  `load_sources_impl`, lines 479-566) uses a real visited-set
  (`closure_scanned_paths`, a canonical-path bucket-set) and completes in
  49 seconds for the real full-CLI command, reporting `collected=1761
  unique=1278` — i.e. no unbounded re-visiting.
- The Rust closure walker actually used by `native-build`
  (`src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs:816`,
  `discover_reachable_files_with_sources`) is a textbook BFS with a
  `HashSet`-backed `queued`/`seen` visited set (lines 871-880). It is fast and
  correct: it terminates immediately and reports the true reachable set.

Both were measured directly (traced runs below); neither is the bottleneck.

## What actually happens (traced, timestamped evidence)

### 1. The real command, traced end-to-end

Reconstructed exact Stage-4 command from
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
header + `scripts/bootstrap/bootstrap-from-scratch.sh`
`bootstrap_native_build_main()` (lines 464-492), run against the pre-verified
Stage-3 binary (`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
sha256 `daf91ae650...`) with `SIMPLE_COMPILER_TRACE=1` added:

```
[BOOTSTRAP-PHASE] +0ms compile:start
[BOOTSTRAP-PHASE] +0ms phase1:load_sources:start
[BOOTSTRAP-PHASE] +48944ms phase1:load_sources:done n_sources=1761
[BOOTSTRAP-PHASE] +48944ms phase2:parse:start
[BOOTSTRAP-PHASE] +51574ms phase2:parse:closure:sources collected=1761 unique=1278
[BOOTSTRAP-PHASE] +51574ms phase2:parse:file:start src/app/cli/main.spl chars=773
...(25 files parse cleanly, one after another, over the next ~180s)...
[BOOTSTRAP-PHASE] +237115ms phase2:parse:file:start src/app/io/_CliCompile/compile_targets.spl chars=49304
```

The process was still inside that last file (`compile_targets.spl`, 49,304
chars) when its 300s repro cap killed it. Two other files earlier in the same
run showed severe (not merely large) per-character parse cost:
`src/app/t32_cli/mod.spl` (23,640 chars → 30.1s, i.e. ~1.27 ms/char, vs.
~0.15-0.6 ms/char for most other files of similar size) and
`compile_targets.spl` itself (>63s elapsed for 49,304 chars before being
killed, i.e. >1.28 ms/char and climbing). **Both anomalously-slow files sit on
the same import chain** (see next section) — this is the single strongest
piece of evidence tying the isolated repro below to the real full-command
spin.

RSS during this traced run: 489 MB → 3.9 GB in ~61s, → 5.27 GB at 173s → 9.9
GB+ by the time other lanes let it run 11+ minutes (per task brief). Growth
rate *decelerates* over time in the windows actually sampled (not runaway
acceleration), consistent with "compiling many large files, one at a time,
each retaining its own state" rather than a single quadratic operation.

### 2. Minimal deterministic repro (new; this lane)

Bisecting a synthetic 2-line entry file (`use X.{name}` +
`extern fn sys_get_args() -> [text]`) against the Stage-3 binary directly
(`native-build --backend cranelift --entry-closure --threads 1`, no
`--source`, so defaults kick in) gives a clean, minutes-scale, fully isolated
repro:

| import | files discovered | outcome |
|---|---|---|
| `std.nogc_sync_mut.io.env_ops.{env_get}` (leaf module) | 2 | completes in 5.4s |
| `app.io.mod.{eprint}` (57-line facade, `src/app/io/mod.spl`) | 662 | still running (>90s, killed) |
| `compiler.driver.driver.{compiler_driver_create}` (direct) | 662 | still running (>2 min, killed) |

`app.io.mod.{eprint}` was bisected line-by-line: lines 1-53 of the facade all
resolve fast; **line 54, `use app.io.cli_ops.{get_args, exit, ...}`,** is the
exact trigger (53 lines → 8.0s total; 54 lines → >20s and climbing).
`cli_ops.spl` re-exports from `app.io._CliCompile.compile_targets` (line 347),
which — confirmed by direct read —
**imports `compiler.driver.driver` and `compiler.driver.driver_source_loading`
at `src/app/io/_CliCompile/compile_targets.spl:14-18`.**

Isolating `use compiler.driver.driver...` alone reproduces the same
"662 to compile" fallout directly, with real, verifiable progress markers
(`--verbose` output, `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:276-278`
prints every 10th file):

```
Found 662 .spl files
Import map: 16654 unique, 1025 ambiguous function entries, 83 modules with re-exports
Incremental: 0 cached, 662 to compile
  [50/662] compiled     (t≈50s,  RSS 193 MB)
  [100/662] compiled    (t≈123s, RSS 210 MB)
```

RSS trend over this window: 20.6 MB (t=8s) → 170 MB (t=35s) → 193 MB (t=50s)
→ 210 MB (t=123s) — real growth, but **decelerating and roughly linear in
files-compiled**, not exponential. At the observed ~100 files/123s rate, the
full 662-file set extrapolates to ~13.6 minutes for this isolated case alone
— already the same order of magnitude as the reported "11+ minutes and
counting" for the *much bigger* full-CLI closure (1278 unique files, run
under `--low-memory` with the slower LLVM backend rather than this repro's
`cranelift`).

**This is the named mechanism:** `compiler.driver.driver` (the compiler's own
driver module) has a legitimately large transitive import closure — it needs
nearly the whole compiler (parser, HIR, MIR, monomorphize, borrow checker,
trait system, all backends) to function, so a correct BFS from it reaches
~662 files, the same order of magnitude as `bootstrap_main.spl`'s own
663-file closure. `src/app/io/_CliCompile/compile_targets.spl` — a *feature*
file implementing the CLI's `compile`/`native-build` subcommands — imports
that driver module directly, so **any entry that reaches `compile_targets.spl`
effectively doubles its own closure to include most of `src/compiler` a
second time**, on top of whatever it already needed. `main.spl` (the full
CLI) reaches it (via `cli_ops.spl`); `bootstrap_main.spl` (the small,
663-file closure that "compiles fine in 2-5 min") evidently does not, since
it has no `compile`/`native-build` subcommand surface to support.

## Named root cause

- **File/lines:** `src/app/io/_CliCompile/compile_targets.spl:14-18` —
  `use compiler.driver.driver (compiler_driver_create, ...)` and
  `use compiler.driver.driver_source_loading.{...}`.
- **Mechanism:** not a loop bug. The CLI's own `compile`/`native-build`
  subcommand implementation embeds the compiler's driver as a library
  dependency, so compiling the full CLI's entry closure necessarily
  recompiles (a close approximation of) the whole compiler a second time,
  sequentially, one file at a time, via
  `compile_entries_sequential` (`src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:244-288`),
  each file going through the Rust-native `simple_parser` + codegen path
  against a large (16,654-entry, 1,025-ambiguous) cross-module import map
  built by `build_import_map`
  (`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:223`).
- **Why it looks infinite:** at roughly 0.3-1.2s/file (this lane measured
  ~1.2s/file under `cranelift`/`--threads 1`; the real bootstrap's own
  stage2/stage3 logs show ~0.33s/file under `--backend llvm` for the smaller
  663-file closure) times ~1278-2020 files in the real command, total wall
  time lands in the 10s-of-minutes range — well past every bounded
  investigation window used across the many prior lanes on this bug (most
  capped at 3-15 min), and RSS keeps climbing the whole time because the
  work is real and ongoing, not stuck. "No plateau, zero log output" simply
  reflects that `--verbose` progress prints only every 10th file and the
  bootstrap wrapper's own phase markers only cover phase 1/2 (source
  loading/parsing), not this per-file native-build compile loop.
- Two anomalously slow individual files sit directly on this same import
  chain in the real traced run (`t32_cli/mod.spl` at ~1.27 ms/char,
  `compile_targets.spl` itself at >1.28 ms/char and climbing before kill) —
  both far slower per-character than the ~0.15-0.6 ms/char baseline seen for
  every other file in the same run. This is noted as an open, unconfirmed
  lead (see Follow-ups) rather than folded into the named mechanism above.

## What remains hypothesis, not proof

- Why the *real* full command (LLVM backend, `--low-memory`, `--threads 2`,
  single-thread-observed) is reported at 10+ GiB RSS / 20+ min with **no
  plateau in sight**, vs. this lane's isolated cranelift/threads=1 repro
  showing bounded, decelerating, roughly-linear growth toward a ~13-15 min
  finish for a same-order-of-magnitude file count. Candidates, unconfirmed:
  - `--low-memory` may disable/reduce the incremental object cache or force
    additional serialization not present in this lane's fresh-cache repro
    (this lane always saw `Incremental: 0 cached` — expected for a
    brand-new cache dir, not evidence either way for the real run's
    pre-populated `build/bootstrap/native_cache`, which already held 1,327
    cached objects at the start of this investigation).
  - Per-file cost may scale worse than linearly as the ambiguous-symbol
    import map grows (1,025 ambiguous names here); not measured at multiple
    closure sizes to confirm superlinearity vs. this lane's single data
    point.
  - Concurrent system load: this machine was running at least one other
    lane's full bootstrap (`/tmp/simple-font-publish-20260717/...
    current-stage3.../simple native-build ... --entry src/app/cli/main.spl`,
    observed live via `ps` during this investigation) plus other native-build
    smoke-matrix probes throughout this session, which may inflate wall-clock
    measurements for all parties.
- Whether `main.spl`'s real closure (1278 unique files, `--source
  src/compiler --source src/app --source src/lib --source
  examples/10_tooling`) double-compiles `driver.spl`'s ~662-file
  sub-closure from scratch, or correctly reuses the bulk-loaded copies —
  not instrumented in this lane.

## Why no source fix in this lane

Per the standing incremental-builds-only order and per task item 5/6: no
"clearly correct and scoped" fix is evident. The candidates above
(cache-key/`--low-memory` interaction, ambiguous-symbol-map superlinearity)
are unconfirmed and would need a stage2/stage3 rebuild plus a full-size
closure run to verify — expensive, and risky to attempt on a guess per the
standing order not to destabilize other lanes' shared build state. This is
therefore filed as a precisely-named, reproducible bug rather than patched
blind.

## Reproduction (self-contained, ~15 min worst case)

```sh
cd /home/ormastes/dev/wt_s58
printf 'use compiler.driver.driver.{compiler_driver_create}\nextern fn sys_get_args() -> [text]\n' > /tmp/only_driver.spl
timeout 900 env SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap" \
  build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build \
  --backend cranelift --runtime-bundle core-c-bootstrap --verbose \
  --entry /tmp/only_driver.spl --entry-closure --threads 1 \
  --cache-dir /tmp/only_driver_cache -o /tmp/only_driver_out
```

Expect: `Found 662 .spl files`, `Import map: 16654 unique, 1025 ambiguous
function entries, 83 modules with re-exports`, `Incremental: 0 cached, 662 to
compile`, then `[N0/662] compiled` progress lines roughly every 10-15s.
Contrast with `use std.nogc_sync_mut.io.env_ops.{env_get}` in the same
harness, which discovers only 2 files and completes in ~5s.

## Follow-ups for the next lane

1. Confirm/deny the `t32_cli/mod.spl` / `compile_targets.spl` per-char parser
   outlier (>1.27 ms/char vs. ~0.3 ms/char baseline) as a second, independent
   contributing factor — bisect `compile_targets.spl` internally (it did not
   yield to a simple line-count prefix bisection in this lane; first 100
   lines already reproduced a hang, but that block already contains the
   `compiler.driver.driver` import, confounding the two hypotheses).
2. Verify whether `build/bootstrap/native_cache` (already 1,327 objects at
   the start of this investigation) is actually hit for `driver.spl`'s
   closure when compiling `main.spl` in Stage 4, or whether a cache-key
   mismatch forces a cold recompile of files Stage 3 already built.
3. Confirm real parallelism: this lane and the task brief both observed a
   single CPU-bound thread despite `--threads 2` (script default) / `--threads
   8` (task brief); check whether `--low-memory` or
   `SIMPLE_BOOTSTRAP_STAGE4=1` forces `self.config.parallel = false` in
   `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`.

## Related

- `doc/08_tracking/bug/native_build_stage4_pre_object_spin_2026-07-13.md`
- `doc/08_tracking/bug/stage4_entry_closure_duplicate_parse_2026-07-17.md`
- `doc/08_tracking/bug/macos_stage4_full_cli_low_memory_runaway_2026-07-17.md`
- `doc/08_tracking/bug/bootstrap_stage1_entry_closure_spin_oom_2026-07-17.md`
  (superseded/different bug — Rust seed stage1, not Stage-4)
- `doc/08_tracking/bug/cpu_simd_direct_fill_full_bootstrap_stage4_spin_2026-07-08.md`
