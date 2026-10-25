# Feature Expert: Native Build

## Bootstrap failure collection

Collect failures across independent entries and test shards using bounded lanes. Bind caches to phase, producer, and entry; retain compatible outputs and invalidate narrowly. Record grouped bug IDs, exact reproductions, and similar regressions. Follow the
[shared collection policy](../../../07_guide/tooling/bootstrap_failure_collection.md) for terminal statuses, budgets,
cache preservation, and bug evidence. This is agent workflow guidance; it does
not change runner behavior.

## What this is
Compilation of Simple source code to native binaries: the `bin/simple native-build` pipeline, encompassing closure discovery, native codegen, C FFI linkage, symbol resolution, and runtime library integration for host platforms.

## Source of truth
- **Observability:** Environment knobs for progress + diagnostics:
  - `SIMPLE_COMPILER_TRACE=1` — detailed phase transitions
  - `SIMPLE_COMPILER_PHASE_PROFILE=1` — per-phase timings
  - `SIMPLE_HIR_ABI_INTERFACE_TRACE=1` — per-module `[abi-interface]` typed-ABI digest lines (off by default; encoding every module's ABI costs ~190 s per ~600 modules, so it is no longer implied by `SIMPLE_COMPILER_PHASE_PROFILE`)
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

## Trait receivers and unresolved method calls (2026-10-20)
- `class X with Trait:` is a trait implementation (HirImpl + vtable +
  `trait_impls`), recorded only when the class defines every abstract method;
  `imports.rs` is the more permissive side so a mismatch fails the link.
  Methods in a separate `impl X:` block are not counted (both sides agree).
- An `Option<Trait>` payload binding (`Some(x)`, `if val x = opt`) keeps the
  declared trait (`FunctionContext.optional_trait_payloads`) and lowers to
  `MethodCallVirtual`.
- A bare trait-method link symbol with no definition is refused by
  `generate_stub_object` (escape `SIMPLE_ALLOW_INTERNAL_STUBS=1`).
  Fixture: `test/native/cross_unit_trait_dispatch`.
- Open (see the bug doc): Cranelift AOT still emits `rt_function_not_found`
  (nil, exit 0) for an unresolved bare call on an `Any` receiver; trait-typed
  FIELD receivers reach it too, so it cannot be refused yet. An `Any`
  receiver whose bare method several classes define binds the first
  `import_map` entry.

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

## HIR shard adoption and streaming parse receipts (2026-10-19)

- Read `[hir-cache] hits= misses=` (and now `[hir-cache] adopted= lowered=`,
  printed by the main build before the summary) to judge whether the shard
  pre-pass was adopted. The `[build] phase=hir ... cached=` field was a literal
  0 on the streaming route until 2026-10-19 and misread as "re-lowered".
- `phase2:surface:file:parse-start` is emitted BEFORE the front-end cache is
  consulted: it is not a cold-parse count. Use `[frontend-cache] hits= misses=
  parses=` (now printed by every process on the streaming route too) and
  `[parse-shard] done ... parses= claimed=`; `claimed=0` on every shard means
  the shards did not partition.
- Hit cost matters at scale: 2702 HIR hits cost ~196 ms each (decode + a
  redundant full re-encode) = 9 min serial. A hit now decodes once; the
  store-side stability gate plus the checksum carry the admission.
- Record: `doc/08_tracking/bug/phase4_hir_adoption_reported_cached0_and_parse_shards_unpartitioned_2026-10-19.md`.

## Stage 4 live projection is in-process on Linux (2026-10-20)

`stage4_live_runtime_requests` (`native_project/linker.rs`) no longer runs
`cc -Wl,-r -Wl,--gc-sections`. Only LLD collects sections under `-r`.
mold 2.42 and ld.bfd accept the flags and keep everything (775 -> 1564
`rt_`/`spl_` on the Phase 4 CLI), which caused false "no archive owner"
errors. `native_project/live_projection.rs` walks the section/relocation
graph instead. On the kept 2793-input set it equals lld's undefined set
exactly (782). Trap: a mold-linked binary still lists dead-code UND entries
in `.symtab`, so check `nm -D -u`, not `nm -u`. Bug:
`doc/08_tracking/bug/stage4_live_projection_mold_ignores_gc_sections_2026-10-20.md`.

## Phase 3 manual continuation traps (2026-10-25)

Recipe: [Phase 3 manual continuation](../../../07_guide/tooling/bootstrap_failure_collection.md#phase-3-manual-continuation-recipe-measured-2026-10-25).
Miscompile catalog: [Stage 2 native miscompile classes](../../../07_guide/compiler/robustness/stage2_native_miscompile_classes.md).

- Never edit a worktree during its build: bootstrap snapshots source, and a
  mid-run cherry-pick aborts admission.
- `--source src/os` is required on the Phase 3 native-build argv since
  `3dc4d69a57c`.
- Memory: runs 27b-d used 20 MIR workers under the 110G cap and ended rc=143 (27d
  with free memory near 7G); run 27e used 16 and finished. Observed
  worker `rss_max` 6.5-7.8 GiB in the mon27 logs; see
  `stage2_compiler_tests_frontend_shard_rss_2026-10-25.md` for shard RSS.
- Phase-1 failure reasons print AFTER the `[ERROR] phase 1 FAILED` line; read
  below it, not above.
- Stage 3 built from `bootstrap_main.spl` is the bootstrap CLI only
  (`compile`/`native-build`). A release needs a full-CLI Phase 3 link.
- User policy: release goes Phase 3 -> Phase 3 (the working Phase 3 compiler
  rebuilds itself and picks up the compiler-side fixes); no full bootstrap.
- With < 30 go-to-end failures, compile the missing modules by hand and link
  with trap stubs; the in-process bypass (positional `native-build`, no
  `--entry`/`--source`) skips the worker child.
- `bootstrap_main` crashes while printing any error (int-boxed text); read it
  with gdb `x/s ($x0>>3)`.

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

### Worker runtime selection recovery (2026-08-16)

The lightweight owner `src/app/cli/native_build_main.spl` must never revive an
implicit Rust-seed or unchecked `bin/simple` worker fallback. Runtime candidates
come only from existing `SIMPLE_BINARY`, `SIMPLE_BIN`, and the invoking
executable, in that priority order. Canonical paths under
`src/compiler_rust/target/` are rejected. An empty selection returns nonzero
before environment export or process spawn.

Pure policy lives with staged compiler identity in
`src/app/cli/bootstrap_identity.spl`. Behavioral coverage is
`test/03_system/check/cached_render_entry_closure_runtime_selection_spec.spl`;
its manually synchronized mirror is under `doc/06_spec/03_system/check/` until
an admitted full CLI can run test/maintenance/docgen. Do not use the known-bad
`release/` artifact or any Rust seed to turn `TEST_BLOCKED` into PASS. This
criterion does not authenticate arbitrarily renamed binaries and does not
admit Stage 4, build the render carrier, or prove 8K execution.
