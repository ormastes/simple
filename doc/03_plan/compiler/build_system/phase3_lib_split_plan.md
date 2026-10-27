# Phase-3 library split plan — static archives per meaning-group

**Status:** proposed, 2026-10-27. Scope: **static archives only** (dynamic
libraries are a later phase; no ACs for them here). Lane: `work/p3-lib-split-plan`
-> `release/1.0.0`.
**Owner lanes referenced:** backend-dylib `aff21a6c79560e123` (stdlib static
archive + `targets.sdn include/group`), archive naming `a0691336904320eac`,
generic instances `abe15091455222b01`, phase-3 build runner `a6f9eac584e655c6c`.

## 0. Problem

Phase 3 today is **one** whole-program `native-build` of the bootstrap entry
(`src/app/cli/bootstrap_main.spl`) over 1,531 modules drawn from
`src/compositions/kernel_llvm`, `src/compositions/cuda_disabled`, `src/plugins`,
`src/compiler`, `src/app`, `src/lib` (stage2.exe, `x86_64-pc-windows-gnu`,
llvm-mingw): parallel HIR, then whole-program mono, MIR, objgen, link
(`scripts/bootstrap/bootstrap-from-scratch.sh:4355-4395`,
`SIMPLE_BOOTSTRAP_STAGE3=1`, `SIMPLE_CACHE_SCOPE=stage3`). One failure costs
~25 min and leaves 0 objects; run 7, killed mid-MIR, lost everything. The
post-mono streaming design (`doc/05_design/compiler/perf/per_module_stream_to_object_v1.md`)
confirms *mono is whole-program by construction* — so the unit that bounds a
failure must become a **library group** with its own mono, not a module.

Goal: N static archives built in dependency order, each a checkpoint, the exe
linked against them; `simple build` gains library targets as a general,
pure-Simple capability and phase 3 is its first consumer.

## 1. Groups by meaning (measured import graph)

### 1.1 Measurement

Graph derived from `use` statements, BFS from `bootstrap_main.spl` plus every
module under the two compositions (which overlay the `compiler.*`/`plugins.*`
namespace, e.g. `src/compositions/kernel_llvm/compiler/driver/bootstrap_k1_selected.spl`
= `compiler.driver.bootstrap_k1_selected`). Resolver: `compiler.<layer>` ->
`src/compiler/NN.<layer>` (`compiler.core` -> `10.frontend`), `std.X` -> alias
over `src/lib/<category>/X`, `_Capsule/` dirs transparent, compositions first.
Script: scratch `p3graph.js` (to be ported to pure Simple in PR-5 as
`src/app/build/targets/group_graph.spl`). Result on `C:/dev/simple` main
(2026-10-27): **1,133 resolved modules**, 90 distinct unresolved module names
(434 import lines, mostly `compiler.core.tokens`/`compiler.core.types` and
std-alias ambiguities). The gap to stage2's 1,531 is those unresolved std
modules and their transitive std closure — they all fall in the `std` group, so
the group *structure* is unaffected; PR-5's pure-Simple tool must reproduce the
1,531 count from the driver's own resolver (AC-1).

### 1.2 Group table (v1: 7 archives + 1 exe)

| # | Group / archive | Members (dir globs; file overrides in §1.4) | Modules (closure) | Depends on (archives) | Rationale |
|---|---|---|---|---|---|
| 1 | `std` | `src/lib/**` (all categories; the four std categories `common`, `nogc_sync_mut`, `nogc_async_mut`, `sffi` form one SCC: 64/6/24/5 edges both ways) | 247 resolved (+~400 unresolved std) | — | One archive, exactly what the dylib lane's `stdlib_static.sdn` already defines; splitting std/core vs std/io is **not** supported by the graph (cycle). |
| 2 | `compiler-front` | `src/compiler/00.common`, `10.frontend`, `15.blocks` | 162 | std | Lexer/parser/AST/tokens/diagnostics/cache contracts (`00.common/cache_contract`). `compiler.core` *is* `10.frontend`. |
| 3 | `compiler-hir` | `20.hir`, `25.traits`, `30.types`, `35.semantics` | 140 | front, std | hir<->types<->semantics are mutually recursive (27/3, 5/4 edges) — one archive. |
| 4 | `compiler-mono` | `40.mono` | 31 | hir, front, std | Whole-program specializer; separate so the linker-side lazy instantiator (group 6) can depend on it. |
| 5 | `compiler-mir` | `50.mir`, `55.borrow`, `60.mir_opt` | 128 | mono, hir, front, std | Lowering + borrow + opt; mir->mir_opt is one-way inside. |
| 6 | `compiler-codegen` | `70.backend`, `90.tools` | 40 | mir, mono, hir, front, std | Backends, linker wrapper, SMF, lazy instantiation (`70.backend/linker/lazy_instantiator.spl` -> `40.mono`). |
| 7 | `compiler-driver` | `80.driver`, `85.mdsoc`, `99.loader`, `src/compositions/kernel_llvm/**`, **`src/plugins/**` + `src/compositions/cuda_disabled/**` (v1 only)** | 276 + 43 | codegen, mir, mono, hir, front, std | Pipeline, caches, bootstrap API. Plugins are folded in for v1 because `driver_aot_pipeline.spl -> plugins/backend_vhdl/driver/driver_aot_vhdl_output.spl` and plugins -> driver (5 edges) form a 2-cycle; splitting `plugins-backends` out via the existing `backend_port` is a follow-up (not an AC here). |
| 8 | exe `simple-bootstrap` | `src/app/cli/bootstrap_main.spl` closure in `src/app/**` (`app/cli`, `app/io`, `app/compiler_entrypoint`, `app/build`, `app/bug`, `app/optimize`, `app/startup`) | 66 | all archives | Thin entry; the full CLI (`src/app/cli/_CliMain/main_and_help.spl`) is a second exe target over the same archives (Stage 4). |

Dependency edges between groups (measured, forward only after §1.4):
driver->std 592, driver->front 345, driver->hir 240, mir->hir 203, exe->std 192,
hir->front 165, front->std 141, mono->hir 122, mir->front 94, driver->mir 88,
mono->front 79, driver->mono 59, mir->std 55, exe->driver 54, hir->std 47,
codegen->std 33, codegen->front 27, driver->codegen 23, codegen->hir 16,
codegen->mir 7, codegen->mono 5, mir->mono 1.

Order (topological): std < front < hir < mono < mir < codegen < driver < exe.

### 1.3 Cycles found (fine-grained SCC over 41 directory units)

1. `lib/common | lib/nogc_sync_mut | lib/nogc_async_mut | lib/sffi` — kept as
   one archive (std).
2. One giant SCC containing every compiler layer, `app/cli`, `app/io`,
   `app/build`, `app/compiler_entrypoint`, `app/optimize`, `lib/scv` and all
   plugins. Broken by the 46 back-edges below (24 files).

### 1.4 Back-edges and how each is broken

| Back-edge (count) | Files | Fix |
|---|---|---|
| mono -> driver (10), hir -> driver (6) | `40.mono/mono_archive_{body_input,registration,current_body,registration_types,registration_identity}_v1.spl`, `20.hir/archive/interface_action_archive.spl`, `20.hir/import_materialization/{state,materializer}.spl` import `80.driver/cache/{hir_body_typecheck_lease_v1,hir_owned_artifact_cache_v1,hir_mono_archive_consumer_v1,package_tldr_metadata,package_archive_types,pinned_archive_capability}.spl`, `80.driver/driver_hir_cache.spl` | Move those 7 cache-contract modules to `src/compiler/00.common/cache_contract/` (where `generic_tldr_view_v1.spl` already lives); update `use compiler.driver.cache.X` -> `compiler.common.cache_contract.X`. Pure move, no logic. (PR-6) |
| std -> exe (11) | `lib/scv/{compile_snapshot,store,shadow_write,native_shadow,stabilize,shadow,integrity,journal,maintenance}.spl` import `app.io.mod`/`app.io.file_ops`/`app.io.cli_ops` | Replace with `std.io_runtime` equivalents (`file_read/file_write/file_exists/dir_create_all`, process ops). 11 import lines. (PR-7) |
| mir -> codegen (4) | `50.mir/_MirLoweringExpr/*.spl -> 70.backend/gpu_intrinsics.spl`; `60.mir_opt/mir_opt_integration.spl -> 70.backend/feature_caps.spl` | Membership override: both tables belong to `compiler-mir` (`feature_caps` has 8 backend + 5 mir_opt importers; placing it in mir keeps all importers at or above). (config only, PR-5) |
| front -> hir (6), front -> codegen (4), front -> mir (1) | `00.common/compiler_services.spl` (-> hir_types, backend_port, backend_types), `00.common/compilation_context.spl` (-> `90.tools/aop.spl`), `00.common/driver_core_types.spl` (-> `70.backend/backend_types.spl`), `00.common/runtime_value_v1.spl` (-> hir_definitions, hir_types, mir_types), `00.common/_Attributes/decl_attrs.spl` (-> `30.types/type_layout.spl`), `00.common/assurance/representation_manifest_v1.spl` + `10.frontend/core/representation_declarations_v1.spl` (-> `35.semantics/symbol_id/stable_id.spl`) | Overrides: `compiler_services.spl` -> `compiler-driver` (sole importer is the driver, 1 edge); `compilation_context.spl` + `90.tools/aop.spl` -> `compiler-hir` (importers: mono 3, backend 3, driver 2); `driver_core_types.spl` + `70.backend/backend_types.spl` -> `compiler-front` (importers hir 5, backend 5, driver 44, app, plugins) **if** `backend_types.spl` has no hir imports — the graph tool decides, else `compiler-hir`; `runtime_value_v1.spl` -> `compiler-mir`; `30.types/type_layout.spl` and `35.semantics/symbol_id/stable_id.spl` -> `compiler-front` (leaf ID/layout modules). All verified fail-closed by AC-1. |
| codegen -> driver (2), mir -> driver (1) | `70.backend/linker/obj_taker.spl -> 99.loader/loader/compiler_sffi.spl`; `70.backend/linker/linker_context.spl -> 80.driver/pipeline_fn.spl`; `60.mir_opt/optimizer_kernel_contract.spl -> 80.driver/cache/action_key.spl` | Overrides: `action_key.spl` -> `compiler-front` (it is the pure key/digest module; `interface_digest_of` belongs low anyway), `compiler_sffi.spl` -> `compiler-front`, `pipeline_fn.spl` -> `compiler-codegen`. |
| codegen -> mono (5), mir -> mono (1) | linker lazy instantiator, `switch_operators_calls.spl -> monomorphize_integration.spl` | Not back-edges once mono < mir < codegen (order above). |
| driver <-> plugins (1 / 5) | see table row 7 | Fold plugins into `compiler-driver` for v1. |

After these, the grouped graph has **no SCC of size > 1** (verified with the
same script using the §1.2 map; the overrides are checked again by AC-1 once
the pure-Simple tool exists).

## 2. std group: reuse `config/build/stdlib_static.sdn`

`config/build/` today holds only `submodule_inventory.sdn` and (release tip
`25cdeee5d5d`) `cpu_tiers.sdn`. **`stdlib_static.sdn` does not exist yet** — it
is on the dylib lane's unpushed branch `work/stdlib-static-archive` together
with `scripts/build/build-stdlib-static.shs`, the artifact
`libsimple_std-<semver>-<triple>-<tier>.a` + `.lib.sdn` sidecar and the
`native-build --std-archive` flag. This plan **does not duplicate** it:
`config/build/phase3_libs.sdn` does `include: config/build/stdlib_static.sdn`
and the `std` group has no member list of its own. Until that PR lands, PR-2's
fixture uses two tiny libs; the phase-3 config is blocked on it (dependency
noted in §10).

## 3. `simple build` first-class library targets

### 3.1 What exists (pure Simple, full CLI only)

- `src/app/build/cli_entry.spl` — `build` subcommand; `--target <name>`,
  `--explain`; bare `build` prints help (seed parity).
- `src/app/build/targets/build_targets.spl` — `BuildTarget{name,kind,entry,output,deps}`,
  kinds `binary|library|shared|test`, parser for `build.sdn`/`targets.sdn`
  (`//pkg:label` names), DFS cycle check `validate_targets`.
- `src/app/build/targets/targets_cli.spl` — loads `<root>/build.sdn` then
  `targets.sdn`; `run_target_execution`, `run_target_explain`. Root
  `targets.sdn` exists (3 targets: configc, provider_cli, provider_cli_native).
- `src/app/build/targets/target_executor.spl` — dependency-first execution,
  `library` -> `--emit-archive`, `shared` -> `--emit-shared`, candidate file +
  atomic publish, per-target `build/target_cache/<name>`, dependency artifacts
  passed via `--input-manifest` (`publish_dependency_manifest_layer_v1`,
  consumed at `src/app/cli/native_build_main.spl:2282`).
- Driver: `--emit-archive` -> `find_archive_portable()`
  (`70.backend/backend/llvm_capability.spl`: `SIMPLE_AR`, then `llvm-ar-NN`,
  `llvm-ar`, `ar`, `lib.exe`) in `80.driver/driver_aot_native_output.spl:3196-3238`.
- Interface identity: `80.driver/cache/action_key.spl:184 interface_digest_of`
  (`simple/interface/v1`), SIF `iface-digest`, SMF manifest rows;
  `80.driver/driver_build/incremental.spl:98 needs_recompile` (one-hop, **never
  called**); `src/compiler/simple.sdn` / `src/app/simple.sdn` `dependencies:`
  (display only). TLDR interface stubs: `20.hir/hir_lowering/module_surface_from_tldr_v1.spl`.
- Bootstrap stage binaries (`bootstrap_main.spl`) expose only `compile` and
  `native-build` (with `--emit-object|--emit-entry-object|--emit-archive|--emit-shared`,
  `--cache-dir`, `--input-manifest`). The full-CLI `simple build` is the
  orchestrator and spawns the stage binary per target.

### 3.2 Gaps (each is a PR)

| Gap | Where | PR |
|---|---|---|
| G1 `multiple-link-dependencies-unsupported` (`target_executor.spl:219-233`): one archive provider, executables only | ordered link list = reverse topological order of `deps` closure; libraries may depend on libraries | PR-2 |
| G2 `_target_action_digest` returns `""` = Unknown -> every run rebuilds (`target_executor.spl:262`) | digest = sha256 of (own-member source hashes, `interface_digest_of` of each dep's `.lib.sdn` exports, tool identity `native_build_cache_scope_key`); reuse when equal; body-only change in a dep changes its archive hash but not its iface digest -> dependents relink only | PR-3 |
| G3 no group membership model: a target has one `entry` | `members:` (dir globs + `+file`/`-file` overrides) on `library` targets; driver `native-build --members-manifest <file>` builds exactly that set with group-scoped mono and emits one archive | PR-5 |
| G4 no sub-configs / `include` / `group` | **from dylib lane** (`work/targets-include-group`): `include: <path>`, `group <name>: default: bool`; phase 3 = `config/build/phase3_libs.sdn` included from root `targets.sdn` as `group phase3` (default false); `simple build phase3` = `simple build --group phase3` | PR-4 (dep) |
| G5 consumers re-lower dependency HIR | `.lib.sdn` sidecar names the archive's TLDR dir; driver `--dep-interface <sidecar>` builds `ModuleSurface` from TLDR stubs (`module_surface_from_tldr_v1`) and never parses dep bodies | PR-8 |
| G6 no checkpoints / resume / result file / go-to-end across targets | `build/phase3/result.sdn` always written (trap on exit), per-target status, `--resume` skips targets whose receipt verifies | PR-9 |
| G7 serial only | admission: run independent targets concurrently while free RAM >= 24 GB reserve (`host.sdn` jobs, existing memory admission `native_build_memory_admission_refusal_v1`) | PR-10 |

## 4. Archive naming / versioning (to-confirm with `a0691336904320eac`)

Follow the dylib lane scheme as-is:
`build/targets/<group>/libsimple_<group>-<semver>-<triple>-<tier>.a` plus
`libsimple_<group>-<semver>-<triple>-<tier>.lib.sdn` sidecar, e.g.
`libsimple_compiler_front-1.0.0-rc.1-x86_64-pc-windows-gnu-x86-64-v3.a`.
`<semver>` from the package `simple.sdn` version (`1.0.0-rc.1`), `<triple>` the
target triple, `<tier>` a `cpu_tiers.sdn` level (`src/lib/common/cpu_tier/tier_id.spl`).
Sidecar fields (proposed): `schema: simple-lib/v1`, `group`, `semver`, `triple`,
`tier`, `archive_sha256`, `iface_digest` (fold of member `interface_digest_of`),
`members: [module ids]`, `tldr_dir`, `deps: [{group, iface_digest}]`,
`producer` (compiler identity). Group names use `_`; targets use `//phase3:<group>`.
**Open:** whether `<tier>` is part of the name for non-SIMD archives, and
whether `.lib` is wanted on Windows besides `.a` (llvm-mingw links `.a`).

## 5. Interface boundaries

A consumer group compiles against the dependency's **TLDR / interface
summary** (`.lib.sdn -> tldr_dir`), never its HIR: `module_surface_from_tldr_v1`
builds stubs (headers + layouts, bodies `pass`), fails closed on any
`fallback|` row. Fallback (for v1 only, measured and reported): if a dep module
has fallback rows, the consumer may load that module's HIR from the dep's
HIR cache; AC-8 counts such loads and the target is **zero** for phase 3.
Interface change detection = `iface_digest` in the sidecar (G2).

## 6. Generic instances across archives (lane `abe15091455222b01`)

Per group mono is group-scoped. Instances a consumer needs from a dependency's
templates are (a) recorded in the consumer's TLDR `generic-spec` list
(`generic_specialization_list_v1`), (b) unioned by
`80.driver/cache/generic_instance_build_plan_v1.spl` (P-G5), and (c) built as
instance objects before the exe link by
`driver_build/generic_instance_object_producer_v1.spl` (P-G7) into one
`libsimple_instances-...a` link input; duplicates are deduped by the instance
cache key `(producer, ConcreteTldrKey)`, with COMDAT/weak as the linker-level
backstop. The existing link-time `lazy_instantiator.spl` remains the fallback
for a missing instance and must report it (AC-9). Dependency: P-G6 consumer
bug `doc/08_tracking/bug/generic_instance_plan_has_no_consumer_pg6_2026-10-25.md`.

## 7. Small exe

Target `//phase3:simple_bootstrap` (`kind: binary`, `entry:
src/app/cli/bootstrap_main.spl`, `depends: compiler_driver, compiler_codegen,
compiler_mir, compiler_mono, compiler_hir, compiler_front, std`): only the 66
`app/**` closure modules are compiled by the exe action; everything else comes
from archives in reverse topological order. Stage 4 adds
`//phase3:simple_cli` (`entry: src/app/cli/_CliMain/main_and_help.spl`) over
the same archives.

## 8. Failure isolation, checkpoints, parallelism, result file

- Each archive is a checkpoint: receipt = sidecar + archive sha256; `--resume`
  reuses verified receipts (never by file existence alone).
- Go-to-end: a failed group marks itself FAILED and blocks only its dependents
  (status BLOCKED, with the blocking group named); independent groups continue.
- `build/phase3/result.sdn` is written on every exit path (success, failure,
  kill signal handled in the orchestrator, timeout): per group `status`,
  `wall_ms`, `peak_rss`, `archive`, `iface_digest`, `reused|rebuilt`, first
  error line, resume command.
- Parallelism: independent ready groups run concurrently while
  `free_ram - sum(estimated_peak) >= 24 GB`; otherwise serial. The orchestrator
  kills only PIDs it spawned.

## 9. Spec plan (modern SSpec, manual-first, `# @req AC-n`)

Files (new):
- `test/02_integration/app/build/multi_lib_targets_spec.spl` — fixture under a
  temp root: `liba` (2 modules), `libb` (2 modules, depends liba), exe
  (depends libb, liba). Steps: build all -> 3 artifacts, `llvm-ar t` lists
  objects (AC-3/4); touch a body in libb -> `rebuilt=2 reused=1` (libb +
  relink) (AC-5); change an exported signature in liba -> all three rebuild;
  run exe prints expected (AC-4). `@req AC-3 AC-4 AC-5`.
- `test/01_unit/app/build/group_graph_spec.spl` — membership globs/overrides,
  acyclic verdict, fail-closed on a planted cycle (AC-1).
- `test/01_unit/app/build/lib_sidecar_spec.spl` — sidecar round trip, iface
  digest stability on body edit, change on signature edit (AC-7/AC-8).
- `test/02_integration/app/build/phase3_result_resume_spec.spl` — inject a
  failing module into one fixture lib: result file written, dependents BLOCKED,
  independents PASS; kill own child after first archive -> resume reuses it
  (AC-11/12).
- `test/03_system/build/phase3_lib_split_hosts_spec.spl` — one `it` per host
  (Windows, Linux, macOS, FreeBSD, SimpleOS) with the evidence command in
  §AC-14; unreachable host = BLOCKED row with owner + resume command, never
  skipped, never PASS.
Style: user-voice docstrings, outcome-named `it`, `step("...")`, built-in
matchers only, capture evidence rows (`result.sdn` text), as in
`test/01_unit/app/build/action_identity_spec.spl`.

## 10. PR breakdown (Haiku-sized, in order)

| PR | Content | Depends |
|---|---|---|
| PR-1 | this plan | — |
| PR-2 | `simple build` static-lib targets + link-against-libs: G1 (ordered multi-provider link, library->library deps), driver accepts N `--input-manifest` archives; `multi_lib_targets_spec.spl` (AC-3, AC-4) | — |
| PR-3 | G2 incremental reuse via source + iface digest; relink-only on body change; spec rows AC-5 | PR-2 |
| PR-4 | `config/build/phase3_libs.sdn` (groups of §1.2, `include: stdlib_static.sdn`), root `targets.sdn` `group phase3`, `simple build phase3` alias (AC-2, AC-6) | dylib lane `work/targets-include-group`, `work/stdlib-static-archive` |
| PR-5 | G3 `members:` + overrides; `group_graph.spl` (pure-Simple port of p3graph) + `simple build --explain-groups`; `group_graph_spec.spl` (AC-1) | PR-2 |
| PR-6 | move 7 HIR-archive cache-contract modules `80.driver/cache -> 00.common/cache_contract` (§1.4 row 1) | — |
| PR-7 | `lib/scv` drops `app.io` imports (§1.4 row 2) | — |
| PR-8 | G5 `.lib.sdn` sidecar + `--dep-interface` TLDR consumption, `lib_sidecar_spec.spl` (AC-7, AC-8) | PR-3, naming confirm |
| PR-9 | G6 result file, per-group checkpoints, `--resume`, go-to-end; `phase3_result_resume_spec.spl` (AC-11, AC-12) | PR-4 |
| PR-10 | G7 parallel groups with 24 GB reserve (AC-13) | PR-9 |
| PR-11 | generic-instance union + instance archive before exe link (AC-9) | lane `abe15091455222b01` P-G6/P-G7 |
| PR-12 | exe target `//phase3:simple_bootstrap` (AC-10) + hosts spec (AC-14) | PR-8..11 |
| PR-13 | final verification run + timing record (AC-15, AC-16) | build runner `a6f9eac584e655c6c` |

## 11. Time estimates (basis stated)

Basis: today's run reaches mid-MIR at ~25 min over 1,531 modules with parallel
HIR (user-reported); whole build extrapolates to ~35-40 min, i.e. ~1.4 s/module
amortized. Fixed per-process startup ~1 min (stage2 + cache admission).
- **First archive:** `compiler-front` (162 modules, needs only std TLDR):
  ~162 x 1.4 s + 1 min ≈ **5-6 min**. `std` in parallel (~650 modules) ≈ 15 min.
- **Exe link:** parallel (3-4 lanes within the 24 GB reserve): critical path
  std (15) -> front/hir/mono/mir/codegen chain on TLDR interfaces overlaps with
  std -> driver (276, ~7 min) -> instance fill + link (~2 min) ≈ **20-25 min**.
  Serial fallback ≈ 40 min, but every finished archive survives a kill.
- A one-group failure now costs that group's time (≤ 7 min for driver) instead
  of 25 min and 0 objects. Measured values go into `result.sdn` (AC-16).

## 12. Landing and final verification

Each PR: `work/<topic>` -> PR -> `release/1.0.0` (vcs rules; admission check
fires on `gh pr edit`). Final verification = a real phase-3 lib-split run
driven by `simple build phase3` on the release tip, coordinated with the build
runner `a6f9eac584e655c6c` (never touching the live run under `C:/dev/p3new`),
evidence: `build/phase3/result.sdn`, archive list with sizes, exe
`--version` + hello-world compile/link/run.

## Acceptance criteria

- **AC-1 Groups measured and acyclic.** `bin/simple build --explain-groups config/build/phase3_libs.sdn` prints per-group module counts, inter-group edge counts, `closure_modules=1531` (± the driver's own resolver count), `cycles: 0`, exit 0; a planted back-edge yields `cycles: 1`, exit 1 (`group_graph_spec.spl`).
- **AC-2 std reuse.** `grep -n 'include: config/build/stdlib_static.sdn' config/build/phase3_libs.sdn` matches; `grep -c 'src/lib' config/build/phase3_libs.sdn` = 0.
- **AC-3 Library target emits an archive via llvm-ar on every host.** `bin/simple build --target //fixture:liba` creates `build/targets/.../liba….a`; `llvm-ar t <archive>` lists one object per member; `SIMPLE_AR` unset.
- **AC-4 Link against multiple libraries in dependency order.** exe with `depends: libb, liba` (libb depends liba) builds and runs (`exe` prints `ok`); `target-error: multiple-link-dependencies-unsupported` no longer exists in `target_executor.spl` (`grep -c` = 0).
- **AC-5 Incremental rebuild of changed libs only.** After a body edit in libb: summary line `rebuilt=2 reused=1`; after no edit: `rebuilt=0 reused=3`; after a signature edit in liba: `rebuilt=3`.
- **AC-6 Per-group sub-config and alias.** `bin/simple build phase3 --explain` lists the 7 archives + exe in topological order from `config/build/phase3_libs.sdn` included via root `targets.sdn` `group phase3`.
- **AC-7 Archive naming + sidecar.** every phase-3 artifact matches `libsimple_<group>-<semver>-<triple>-<tier>\.(a|lib\.sdn)$`; sidecar has `schema`, `archive_sha256` equal to `sha256sum` of the archive, `iface_digest` (64 hex) — scheme confirmed by `a0691336904320eac` before PR-8 merges.
- **AC-8 Consumers compile against TLDR, not HIR.** with `SIMPLE_BUILD_TRACE=1`, a consumer group's log has `dep-interface: <group> tldr=<digest>` per dependency and `dep-hir-load: 0`; modules lowered == group member count.
- **AC-9 Generic instances complete before link.** `llvm-nm --undefined-only <exe-pre-link objects>` after the instance archive is added shows no mangled template instance; result.sdn `instances: planned=N built=N lazy_fallback=0`.
- **AC-10 Small exe.** the exe action compiles only `app/**` closure modules (result.sdn `exe.modules_compiled` ≤ 70) and links 7 archives (+ instance archive); exe `--version` runs.
- **AC-11 Failure isolation + go-to-end report.** with one group poisoned: other independent groups PASS, dependents BLOCKED naming the blocker, `build/phase3/result.sdn` present, exit code non-zero.
- **AC-12 Checkpoint resume.** kill (own PID) after the first archive's receipt; `simple build phase3 --resume` reports that group `reused`, result.sdn from the killed run exists with `status: killed`.
- **AC-13 Parallel groups under reserve.** with ≥ 24 GB free, result.sdn shows overlapping `start/end` for independent groups; with `SIMPLE_BUILD_RESERVE_GB=10000` it runs serially and logs the refusal reason.
- **AC-14 All hosts.** `phase3_lib_split_hosts_spec.spl` has one row per host; evidence: Windows local run; Linux `sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --smoke` or a Linux host; FreeBSD `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`; SimpleOS via the real-firmware QEMU lane (board-runnable rule); macOS on a mac host with `llvm-ranlib` applied to Mach-O archives. Archives use llvm-ar on every host (COFF via llvm-mingw, ELF, Mach-O); paths/process spawning host-neutral; no host-specific literals in `config/build/*.sdn` (`grep -E 'C:|/usr/' config/build/phase3_libs.sdn` empty). A host nobody can reach is a visible BLOCKED row with owner + resume command — never skipped, never PASS.
- **AC-15 Specs green.** `bin/simple test test/02_integration/app/build/multi_lib_targets_spec.spl test/01_unit/app/build/group_graph_spec.spl test/01_unit/app/build/lib_sidecar_spec.spl test/02_integration/app/build/phase3_result_resume_spec.spl` all PASS; each spec carries `# @req AC-n`.
- **AC-16 Timing recorded.** final run's result.sdn has `first_archive_wall_ms` and `exe_link_wall_ms`; report compares with §11 (first archive ≤ 6 min, exe ≤ 25 min parallel) and files a perf bug if exceeded.
- **AC-17 Landed on release/1.0.0.** all PRs merged (`git log origin/release/1.0.0 --oneline | grep -c 'p3-lib-split'` ≥ 13) before the final run; final run evidence attached to PR-13.

## Open coordination questions

1. `aff21a6c79560e123`: ETA of `work/targets-include-group` and
   `work/stdlib-static-archive`; exact `group`/`include` grammar and `.lib.sdn`
   field set so PR-4/PR-8 reuse them verbatim.
2. `a0691336904320eac`: confirm `libsimple_<group>-<semver>-<triple>-<tier>` for
   non-std archives, `_` in group names, `<tier>` presence, Windows `.a` only.
3. `abe15091455222b01`: is P-G7 (`generic_instance_object_producer_v1`) the
   link input to depend on, or should the exe action call the plan directly?
4. `a6f9eac584e655c6c`: window for the final run; stage2 identity to use;
   whether the run must use `SIMPLE_CACHE_SCOPE=stage3` or a new `phase3-libs`
   scope (cache-scope ownership guard).
5. Directory fan-out: `doc/03_plan/compiler/` is already over the 10-file
   limit; `check-directory-fanout.shs` is baseline-relative and may flag this
   file — move to `doc/03_plan/compiler/build_system/` if it does.
