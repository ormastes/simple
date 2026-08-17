# Feature Expert: Native Build

## What this is
Compilation of Simple source code to native binaries: the `bin/simple native-build` pipeline, encompassing closure discovery, native codegen, C FFI linkage, symbol resolution, and runtime library integration for host platforms.

## Source of truth
- **Observability:** Environment knobs for progress + diagnostics:
  - `SIMPLE_COMPILER_TRACE=1` — detailed phase transitions
  - `SIMPLE_COMPILER_PHASE_PROFILE=1` — per-phase timings
  - `--log off` controls **guest-kernel logging, NOT build verbosity**
  - Per-line flush now landed (see `doc/08_tracking/bug/simpleos_harness_silent_native_build_2026-07-26.md`)

## Code map
| File | Role |
|---|---|
| `src/compiler/80.driver/driver_native_build.spl` | Entry point, closure discovery, codegen dispatch |
| `src/compiler/80.driver/native_build_closure.spl` | Recursive import tracer (plain `use` only, NOT `export use` shims) |
| `src/compiler/70.backend/backend_llvm.spl` | LLVM codegen backend selection |
| `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` | Cranelift JIT backend (host-arch detection: `host_arch()`) |

Specs: `test/01_unit/compiler/80.driver/driver_native_build_spec.spl`.

## Cache: incremental persistence (2026-07-26)
- **Index now writes to disk every 5 modules** — timeout no longer loses work
  (`doc/08_tracking/bug/native_build_cache_never_written_on_timeout_2026-07-26.md`)
- **Seed-lane cache identity quirk:** pre-stage4 seed binaries have an uncacheable
  identity (cache validation fails on seed-compiled artifacts; rebuild after
  stage4 redeploy)
- **Zero-hash never accepted:** compile-options mismatch triggers plain cache miss →
  rebuild (not a silent fallback)

## Standalone target-product boundary (2026-08-11)

Office and similar products are independent native targets, not requests to
rebuild the compiler. Use an explicitly supplied, provenance-admitted Phase 3
compiler through `scripts/check/build-office-standalone-target.shs`; its cache
and output live under `build/standalone/`. The wrapper rejects missing, stale,
symlinked, seed, and unreceipted inputs, preserves strict no-stub guards, and
does not initiate any bootstrap stage. The product receipt is target evidence
only, never a Stage 4 deploy, SPipe runner, or release substitute.

For general feature-build selection, provider/SCI projections, compatibility
receipts, and typed bootstrap reasons, use
`doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`. A path
under `src/compiler/**` does not independently require bootstrap.
That guide also permits explicitly admitted Stage 2/3 binaries for focused
compiler/interpreter/loader work. Admission records path/hash/stage/provenance
and supported commands, uses isolated output/cache, and fails closed. Keep the
result stage-scoped; it is not a Stage 4, general SPipe/docgen/test, release,
convergence, DDC, or cross-host claim.

## Known open defects (2026-07-26)
| Bug | Scope | Link |
|---|---|---|
| LLVM-lane nil-self miscompile | Native-compiled code crashes on nil-receiver | `native_build_nil_receiver_crash_2026-07-25.md` |
| Parser ~100cps collapse | Native-build lane only, full project parse halts | `native_build_parser_100cps_regression_2026-07-26.md` |
| Nested-call `.replace` resolution | Bare string method in nested calls rebinds to wrong receiver | `native_build_nested_replace_method_resolution_2026-07-26.md` |

## Closure discovery limitation
The recursive tracer (`.spl` → closure) follows plain `use` imports only — does NOT
traverse `export use` shims. If re-exporting driver or lowering modules, closure must
be assembled manually or tracer extended.

## Runtime linkage (hosted paths)
**Critical:** `SIMPLE_RUNTIME_PATH` env var **MUST** be set to seed target directory
for hosted native-build linking. The `--runtime-path` CLI flag alone does NOT set the
env var. Host-side wrappers must explicitly pass both:
```
SIMPLE_RUNTIME_PATH="path/to/seed/target" bin/simple native-build ...
```
Hosted link backfills `rt_*` externs from `libsimple_native_all.a` only if the env var
points to correct seed target.

## Freestanding linkage: the fabricated-stub gate (2026-08-04)
On `--target x86_64-unknown-none` the link refuses to invent symbols it cannot find:
```
Build failed: freestanding link would FABRICATE 3 symbol(s) not in the baseline
for entry '<entry>': rt_find, rt_native_cmp, rt_string_partition.
These get weak bodies that return 0, which silently corrupts every caller.
```
Baseline: `config/freestanding_fabricated_stub_baseline.sdn`. The gate runs
**pre-`--gc-sections`**, over the object set — so a symbol can trip it and still be
absent from the final ELF once its callers are collected.

**Do not re-baseline to get past it.** `SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1` exists
but a weak 0-returning body is a silent wrong answer at every call site (a `find` that
reports "match at index 0", a comparator that says "equal"). Implement the symbol in
`examples/09_embedded/simple_os/arch/<arch>/boot/baremetal_stubs.c`.

Diagnosing *where* a fabricated name comes from: the names are emitted by the
pure-Simple codegen's erased-receiver redirect (`rt_<recv>_<method>` / bare
`rt_<method>`), so they exist in **no** source file — grep will find nothing. Instead
`nm -u` the kept objects (the failed link leaves them at `native-objects-*/`) to map
symbol → module, e.g. `rt_string_partition` → `lib__log` → `line.partition(" ")` in
`src/lib/log.spl`. A symbol referenced by nearly every object (as `rt_native_cmp` was)
is a codegen-level emission, not one caller's mistake. Binary-grepping the compiler
itself distinguishes stage3 emission from seed emission.

Host-runtime parity is a real, currently-latent gap: `src/runtime/runtime_native.c` and
the Rust runtime still lack these three, so the same erased-receiver path would fail to
link hosted. Precedent for doing it in both: `rt_text_cmp_any`.

## Update Rule
After native-build defects, closure-discovery changes, or cache logic shifts, refresh
this skill with new open-bug links and concrete gotchas.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`

## Flags that decide whether a build finishes (2026-08-17)

`native-build` is fast or effectively unbounded depending on four flags. The
canonical set lives in `scripts/bootstrap/bootstrap-from-scratch.sh`
(`bootstrap_native_build_main`); copy it rather than composing your own.

| Flag | Omitting it costs |
|---|---|
| `--cache-dir <dir>` | **Everything.** No cache to reuse → full cold recompile of the compiler + LLVM import graph on every attempt. The #1 cause of "bootstrap never finishes". |
| `--low-memory` | Single-worker enforcement. Without it, workers each own a full LLVM Context/optimizer and the host OOMs (see below). |
| `--mode one-binary` | Wrong artifact shape for a stage build (default is `dynload`). |
| `--runtime-bundle core-c-bootstrap` | Runtime resolution falls back and can fail late. |

`--threads` note from the built-in help: default is all CPUs, but the **llvm
backend clamps to at most 4** because each worker owns a full LLVM
Context/optimizer, so unclamped parallelism balloons memory. `--low-memory`
overrides `--threads` to a single worker. Raising `--threads` does not speed up
the module-loading phase at all — that phase is serial, so a stage that looks
stuck at 100% of one core with no codegen output is normal, not hung.

## Reading a stalled build correctly

`native-build` (parent) → `timeout` wrapper → `native_build_worker.spl`
(grandchild). The parent **sleeps in `futex_wait` by design**. Always measure
the grandchild: healthy is elapsed ≈ CPU time with RSS ~2.9 GB. Measuring the
parent shows ~0% CPU and reads as "CPU-starved", which is a misdiagnosis.

## `timed out after Ns` may be an OOM kill

`earlyoom` on this host runs `--prefer ^(simple|rustc|cc1|...)` — it targets
`simple` first, at ~10% free memory. When it SIGTERMs the worker, the parent
reports `native-build worker timed out after 14400s before producing a binary`
regardless of actual elapsed time (observed at 7 minutes of a 4-hour budget).
Always cross-check `journalctl -u earlyoom` before raising `--timeout`.
