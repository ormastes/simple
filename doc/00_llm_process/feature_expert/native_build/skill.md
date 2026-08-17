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

## Cached render entry closure blocker (2026-08-14)

The sparse DrawIR 8K carrier uses the admission-gated
`CachedRenderEntryClosureV1` workflow in
`doc/07_guide/ui/rendering/cached_render_entry_closure.md`. Keep Stage 4
candidate construction, candidate admission, deployment, deployed hash lineage,
carrier build, and carrier execution separate. An exit-0 native-build with no
fresh artifact is failure, even when current source contains a missing-output
guard. The unadmitted `release/.../simple` artifact currently exhibits that
failure; do not call it deployed pure-Simple without provenance, essential-smoke,
and deploy receipts. Open bug:
`doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md`.

## Phase snapshots for side-lane native builds (2026-08-17)

Never build or test against `bin/simple` or an in-place stage output while a
bootstrap is running — both get replaced under you. Pin to an immutable
lineage-named snapshot under `build/phase_snapshots/`
(`phase1_<t1>_phase2_<t2>/simple`; see its README). New fix landed = new
generation; in-flight tasks finish on their pinned lineage. The bootstrap
build owns CPU/memory: run native-build side lanes `nice`d with <=2 concurrent
test processes — earlyoom kills `simple` first (a 3.1 GB worker died at 9.97%
free), so an OOM kill can masquerade as a codegen crash. For sweep-style
find-and-fix, go per-directory under `timeout` and drop to per-file on crash;
fixes landed in the source tree get compiled into later stages for free.
Runtime parity note: `rt_file_atomic_write` now exists in the Rust staticlib
(`src/compiler_rust/native_all/src/lib.rs:1155`).

Standing test rule (2026-08-17): every native-build bug fix ships a spec
reproducing the exact defect plus a generalization spec probing similar
problems nearby, both cited in the bug doc. A fix without its reproducing
spec is not done.
## Per-phase run-to-end loop and evidence bar (2026-08-17)

A phase build runs to completion and yields a full error census; the landed
binary is snapshotted immutably with lineage naming before any verification
claim references it; verification runs in a parallel niced lane attempting all
tool builds (even when some fail) plus the test suites with that snapshot; the
next phase starts on the newest available binary, waiting when a rebuild is in
flight. The build owns CPU/memory — test lanes drop to 1 concurrent process
when free RAM is low (2026-08-17: earlyoom killed `jobs=8` stage workers under
~14 test lanes, forcing `jobs=2`; session-measured, unfiled).

Evidence bar addition: exit 0 from `bin/simple test <spec>` is not a pass —
~1897 warning lines with no result line and exit 0 is a measured shape
(`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`).
Require a results/count line, else INCONCLUSIVE plus a `bin/simple run` repro.
This is the same failure family as the exit-0 native build with no fresh
artifact above.

## Per-lane private build caches (2026-08-17)

Concurrent bootstrap lanes (phase-1 seed, phase-2 stage, phase-3 self-host,
phase-4 full CLI, census, tool builds) may run DIFFERENT compiler binaries over
the SAME source tree. Both engines' native-build cache scope keys now carry a
**lane** axis on top of the compiler identity they already had:
`SIMPLE_CACHE_SCOPE=<name>`, or `--cache-scope <name>` on the Rust
native-build / native-all CLIs. Unset ⇒ `default` (previous behaviour).

Entries are partitioned by a scope-derived DIRECTORY, so a cross-scope lookup
cannot name an out-of-scope entry — the miss is structural, not a hash compare.
Each cache dir records its owner in a `.cache_scope` marker; check ownership
without running a compiler via `scripts/check/check-cache-scope-ownership.shs
<cache-dir> <lane>` (PASS/FAIL/ERROR, `--selftest`). `bootstrap-from-scratch.sh`
gives each stage `build/bootstrap/native_cache/<lane>/` and refuses fail-closed
to build against another lane's cache; `resume-stage3-from-admitted.sh` fences
its stage2/stage3 dirs the same way.

- Design: `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`
- Rust: `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`
  (`cache_lane`, `cache_scope_segment`, `cache_dir`, `object_cache_key`)
- Pure Simple: `src/compiler/80.driver/driver_build/incremental.spl`
  (`native_build_cache_lane`, `native_build_cache_scope_key`)
- Specs: `test/01_unit/compiler/cache/per_lane_cache_scope{,_prevention}_spec.spl`
- NOT changed: dependency-aware partial rebuild (`interface_digest_of`,
  `simple.sdn` traversal, `SmfManifest` load-verification remain uncalled).
