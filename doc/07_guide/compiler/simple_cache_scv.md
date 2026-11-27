# Simple compiler cache and SCV — developer guide

**TL;DR.** Every public compiler route (`compile`, `build`, `run`, `test`,
`native-build`, `mcp`, `lsp`, `query`) first *admits* its sources: the
checkout's `src`/`test` trees are inventoried, frozen into an immutable
snapshot under `build/scv/snapshots/<revision_id>/`, and published to child
workers through `SIMPLE_SCV_*` environment variables. Only sources in that
frozen snapshot may be compiled. Admission failure prints one
`SCV-E-<KIND>: <reason>` line on stderr and exits 1; there is no silent
fallback. The per-artifact caches (frontend parse, HIR, MIR, runtime object,
native build) are keyed on top of that snapshot identity. The content-addressed
"cache v2" and the `VirtualSourceStoreV1` contract exist as code but are not
yet wired into normal builds, and the per-file src→obj pipeline is opt-in and
off by default. All paths below are repo-relative; `CC` means
`src/compiler/00.common/cache_contract`.

Related guides: [semantic_build_cache.md](semantic_build_cache.md) (cache v2
status), [scv_retained_source_observations_v1.md](scv_retained_source_observations_v1.md),
[../tooling/buildrunner_scv_source_session_v1.md](../tooling/buildrunner_scv_source_session_v1.md),
[../tooling/scv_readonly_gateway_v1.md](../tooling/scv_readonly_gateway_v1.md).
Design rationale: [../../01_research/compiler/cache/global_content_addressed_cache_audit_2026-07-24.md](../../01_research/compiler/cache/global_content_addressed_cache_audit_2026-07-24.md).

---

## 1. Two things called "SCV"

| Name | What it is | Where |
|---|---|---|
| SCV, the VCS app | *Simple Code Versioning*: a content-addressed repository under `.scv/` with its own CLI (`init`, `snapshot`, `parse-gate`, `parse-index`, `fsck`, ...) | `src/app/scv/main.spl:175-284`; path layout `src/lib/scv/core.spl:3-42`; parser cache spec [`../../06_spec/02_integration/app/scv_parser_cache_spec.md`](../../06_spec/02_integration/app/scv_parser_cache_spec.md) |
| SCV compile snapshot (this guide) | The compiler's frozen source inventory under `build/scv/`, shared code in `src/lib/scv/compile_*.spl`, consumed by `src/app/compiler_entrypoint/` | `src/lib/scv/compile_source_inventory_core.spl:340` (`compile_source_inventory_checkout_cache_root_v1` returns `<checkout>/build/scv`) |

The rest of this guide is about the second one. `SIMPLE_CACHE` never
relocates an admitted snapshot (`compile_source_inventory_core.spl:319-320`).

## 2. The model

### 2.1 Source authority

`src/app/compiler_entrypoint/source_authority.spl` owns the snapshot.

- `struct CompilerSourceAuthorityV1` (`:29`): `valid`, `reason`,
  `snapshot: ScvCompileSnapshotV1`, `source_inventory_digest`,
  `inventory_generation`.
- `struct ScvCompileSnapshotV1` (`src/lib/scv/compile_snapshot_values_v1.spl:13`):
  `revision_id`, `commit_id`, `tree_id`, `inventory_digest`,
  `inventory_count`, `snapshot_root`, `provenance_path`, `receipt_path`,
  `source_drifted`.
- `compiler_source_authority_acquire_v1(root, cache_root, source_roots, cold_init)`
  (`:149`) resolves the requested `--source` selectors
  (`compiler_source_authority_selectors_v1`, see 2.3), refreshes the
  inventory (`compiler_inventory_refresh_traced_cost_v1`,
  `src/app/compiler_entrypoint/inventory_events.spl:976`), acquires or reuses
  a snapshot (`scv_compile_snapshot_acquire_cost_v1`,
  `src/lib/scv/compile_snapshot.spl:588`), checks every requested root has
  rows in the frozen snapshot (`:204-215`), and validates the binding.
  On the very first build in a checkout (no event cursor yet) it auto
  cold-inits `src`, `test` and `examples/10_tooling` (`:177-183`).
- `compiler_source_authority_publish_v1` (`:278`) exports the admitted
  generation to the environment, root last:
  `SIMPLE_SCV_REVISION_ID`, `SIMPLE_SCV_COMMIT_ID`, `SIMPLE_SCV_TREE_ID`,
  `SIMPLE_SCV_INVENTORY_DIGEST`, `SIMPLE_SCV_SOURCE_INVENTORY_DIGEST`,
  `SIMPLE_SCV_INVENTORY_GENERATION`, `SIMPLE_SCV_SOURCE_DRIFTED`,
  `SIMPLE_SCV_SNAPSHOT_ROOT` (`:285-292`). Any failed setter clears the
  partial record.
- `compiler_source_authority_open_published_v1(root)` (`:262`) is what
  workers call: it re-opens exactly the published generation via
  `scv_compile_snapshot_open_v1` (`src/lib/scv/compile_snapshot.spl:180`)
  and never refreshes CURRENT.
- `compiler_source_authority_inventory_v1` (`:38`) returns the admitted
  inventory rows by reading `<snapshot_root>/SCV_COMPILE_INVENTORY`
  (`:45-46`).

### 2.2 Admission (entrypoint)

`compiler_entrypoint_admit_v1(source_roots)`
(`src/app/compiler_entrypoint/admission.spl:89`) is the gate every public
CLI verb passes through (`src/app/cli/_CliMain/main_and_help.spl:385-393`;
`test` admits `["src", "test"]`, everything else `["src"]`). It clears stale
bindings, acquires the authority, then binds the package-module index to the
snapshot (`compiler_entrypoint_binding_generation_v1`, `:36`) and publishes.
The result `CompilerEntrypointAdmissionV1` (`:21`) carries `snapshot_root`,
`revision_id`, `index_digest`, `inventory_generation`.

`native-build` has its own coordinator path
(`run_native_build_worker`, `src/app/cli/native_build_main.spl:1843`) that
publishes authority once before spawning shards (`:1915-1930`) so children
do not repeat cold inventory admission; HIR-only shard warming re-opens the
published generation and fails with `SCV-E-HIR-ADMISSION` otherwise
(`:2037-2042`).

Do not confuse this with `ReaderAdmissionEpochV1`
(`CC/reader_admission_epoch_v1.spl:1`): that is the cache-contract parity
rule (`reader_admission_epoch_admits_v1` = even epoch, `:5`;
`reader_admission_epoch_gc_closed_v1` = odd, `:8`) for cache readers vs GC,
unrelated to source admission.

### 2.3 Derived compositions

`src/app/compiler_entrypoint/derived_composition.spl`. Only selectors of the
form `build/.../compositions/cuda-*` are "derived" roots
(`compiler_cuda_composition_selector_v1`, `:124`); they are mapped back to
canonical source records via `compiler_cuda_composition_root_v1` (`:80`) and
never form a new inventory family (`:1-3`). Any other build-tree selector
(for example `native-build build/hw/hello.spl`) is an ordinary exact
selector that is auto-admitted into the inventory before freezing
(`:120-123`, `compiler_inventory_admit_extra_roots_v1` called from
`source_authority.spl:190`).

### 2.4 Virtual source store

`CC/virtual_source_store_v1.spl` defines a **read-only** trait
`VirtualSourceStoreV1` (`:68`) with `list`, `stat`, `read`, `page`
(`:69-72`). Every call takes a `SummaryAuthV1` (`:10`: `root_digest`,
`session_digest`, `capability_digest`, `capability_admission_receipt`,
`request_epoch`, `expires_epoch`) and a snapshot id. The only kind served is
`VirtualSourceKindV1.PublicSummary` (`:7`). There is no register/write API:
virtual sources are rendered public summaries, not raw files.

Consumers are typed (`VirtualSourceConsumerKindV1`:
`CompilerCli`, `Mcp`, `SimpleLspMcp`, `SPipe`,
`CC/virtual_source_consumer_v1.spl:6`) and installed per process with
`install_virtual_source_consumers_v1(store, auth, snapshot)`
(`CC/virtual_source_read_registry_v1.spl:44`) / cleared with
`clear_virtual_source_consumers_v1()` (`:50`); the compiler reads through
`compiler_virtual_source_read_registered_v1(uri, max_bytes)` (`:119`). The
gateway facade `CacheGatewayV1` (`CC/cache_gateway_v1.spl:27`) exposes it as
`virtual_source_store()` (`:33`); the concrete adapter is
`src/compiler/80.driver/cache/summary/summary_store_v1.spl:288`.

### 2.5 Snapshot identity and cache keys

- `CompileSnapshotV1` (`CC/snapshot_contract_v1.spl:66`) is the full cache
  identity: `source_entries`, `resolution_witnesses`, `negative_candidates`,
  `directory_generations`, `generated_inputs`, `configuration_digest`,
  `target_layout_digest`, `compiler_owner_digest`, `runtime_digest`,
  `provider_manifests`, `toolchain_component_digests`. It has no id field;
  its id is `canonical_compile_snapshot_digest_v1`
  (`CC/canonical_cache_codec_v1.spl:695`).
- Hash domains (NUL-terminated prefixes): `simple.source.v1`
  (`canonical_cache_codec_v1.spl:329`), `simple.compile.snapshot.v1`
  (`:698`), `simple.cas.object.v1` (`:245`). Algorithm ids:
  `HASH_ALGO_SHA256_V1 = 1`, `HASH_ALGO_BLAKE3_V1 = 2`, ...
  (`CC/hash_algorithm_registry_v1.spl:19-25`).
- Object kinds: source blob 1, compile snapshot 2, public summary 3, file
  AST 4, semantic read set 5 (`canonical_cache_codec_v1.spl:15-19`).

### 2.6 The caches that actually run today

| Cache | Key / location | Switch | Code |
|---|---|---|---|
| Legacy incremental | `.build_cache.sdn` in project root; per-function MIR in `.build/mir_cache/` | always | `class BuildCache` `src/compiler/80.driver/driver_build/incremental.spl:1162` |
| Frontend parse cache | scoped by `SIMPLE_CACHE_SCOPE`; dir `SIMPLE_FRONTEND_CACHE_DIR` | `SIMPLE_FRONTEND_CACHE=0` disables | `src/compiler/10.frontend/frontend_parse_cache.spl:124-127`, `frontend_shared_parse_cas_v1.spl:203` |
| HIR cache | identity folded from the frontend scope; dir `SIMPLE_HIR_CACHE_DIR` | `SIMPLE_HIR_CACHE=0` disables | `src/compiler/80.driver/driver_hir_cache.spl:118-135` |
| Runtime object cache | `SIMPLE_RT_OBJ_CACHE`, `SIMPLE_RT_OBJ_CACHE_DIR` | env | `src/compiler/70.backend/backend/runtime_compiler.spl:556,582` |
| Native build cache | `SIMPLE_NATIVE_BUILD_CACHE_DIR`, default `machine_cache_root()/native-build/v1` | env | `src/compiler/70.backend/build_native.spl:49`, `driver_aot_native_output.spl:892` |
| Machine cache root | `SIMPLE_CACHE` overrides `{host_cache_base()}/v1/projects/{ns}` | env | `src/compiler/80.driver/cache/cache_root.spl:32-35` |
| Cache v2 (CAS + action identity) | shadow compare only | `SIMPLE_CACHE_V2_SHADOW=1` | `src/compiler/80.driver/cache/integration/shadow_mode.spl:56`; see [semantic_build_cache.md](semantic_build_cache.md) |

Workers read the admitted epoch from the `SIMPLE_SCV_*` variables
(`src/compiler/80.driver/driver_admitted_epoch.spl:38-39`), so every cache
above sits beneath one frozen source generation per build.

### 2.7 Per-file src→obj: partial, opt-in, default off

- The file-worker pipeline is selected by `SIMPLE_FILE_WORKERS=1`
  (`NATIVE_FILE_WORKERS_ENV_V1`,
  `src/compiler/80.driver/driver_build/native_file_worker_v1.spl:42`); the
  single source of truth for the default is
  `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "0"` (`:47`), and
  `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` forces the single-object route (`:85`).
- The three-payload compiled execution contract is closed:
  `three_payload_compiled_execution_available_v3()` returns `false`
  (`CC/three_payload_execution_v3.spl:270`) with blocker
  `owned_parser_state_profile_and_semantic_pipeline_unavailable` (`:273`);
  only parse preflight is available (`:247-249`).
- Plan and design: `doc/03_plan/compiler/build_system/true_per_file_src_to_obj_plan.md`,
  `doc/05_design/compiler/incremental_build/true_per_file_pipeline_v1.md`.

## 3. Using it

### 3.1 From the CLI / compiler

Nothing to opt into: `bin/simple build|run|test|native-build ...` admits
automatically. Knobs:

| Knob | Effect | Code |
|---|---|---|
| `--refresh-source-authority` (native-build) | force a new generation instead of inheriting `SIMPLE_SCV_SNAPSHOT_ROOT`; rejected inside internal workers | `native_build_main.spl:1755-1775` |
| `SIMPLE_SCV_INVENTORY_COLD_INIT=1` | full cold inventory (list + commit `src`, `test`, `examples/10_tooling`, `source_authority.spl:180-183`) instead of event refresh | `admission.spl:101`, `native_build_main.spl:1923` |
| `--source DIR` (native-build) | explicit finite roots; required for root-level entries | `src/app/io/_CliCompile/native_build_closure.spl:177` |
| `SIMPLE_INVENTORY_TRACE_ATTEMPT=<token>` | emit inventory/snapshot cost trace | `source_authority.spl:184-186` |
| `SIMPLE_SCV_STRICT_COLD_ENTRY` | strict cold-entry handling in the source pipeline | `src/compiler/80.driver/driver_source_pipeline_loading.spl:406` |
| `SIMPLE_SCV_FREEZE_FALLBACK` | entry-closure fallback when freeze refuses | `native_build_closure.spl:301` |

Inside a worker, `env_get("SIMPLE_SCV_SNAPSHOT_ROOT")` tells you which
generation you are compiling; the frozen rows are
`$SIMPLE_SCV_SNAPSHOT_ROOT/SCV_COMPILE_INVENTORY`.

### 3.2 From BuildRunner

There is no `class BuildRunner`; the manager is a set of V1 structs in
`src/app/buildrunner/`. SCV is an opt-in **source-only** session:

- `--scv-session FILE` (`src/app/buildrunner/scv_cli_options_v1.spl:11`)
  with `run`, `verify` or `verify-settled`.
- `build_runner_scv_session_open_v1(run, config, plan_path, require_existing)`
  (`src/app/buildrunner/scv_session_v1.spl:80`) acquires the compiler
  source authority once under the manager lock, adapts the snapshot
  (`CompileSnapshotV1Adapter`) and persists `state/scv-session.sdn` (`:82`);
  reopening uses the saved pointer and never refreshes CURRENT (`:1`).
- Admission digests: `BuildRunnerScvAdmissionV1`,
  `build_runner_scv_bind_v1` / `build_runner_scv_revalidate_v1`
  (`src/app/buildrunner/scv_admission_v1.spl:14,196,212`).

The sidecar format, accepted task shape and refusals are in
[../tooling/buildrunner_scv_source_session_v1.md](../tooling/buildrunner_scv_source_session_v1.md).

## 4. Refusal codes (`SCV-E-*`)

The codes are stderr prefixes written by app-layer code, not enum values
(`CC/errors_v1.spl` holds the typed cache/summary/provider/snapshot error
enums instead). Exit code is 1.

| Code | Emitted at | Meaning |
|---|---|---|
| `SCV-E-ADMISSION: <reason>` | `main_and_help.spl:340,393`; `native_build_main.spl:1848,1915,1921,1927,1930`; `bootstrap_main.spl:248,254,257,409` | entrypoint or coordinator admission failed; `<reason>` is from the tables below |
| `SCV-E-HIR-ADMISSION: <reason>` | `native_build_main.spl:2041` | HIR-shard warming could not re-open the published generation |
| `SCV-E-SOURCE-AUTHORITY: <reason>` | `native_build_closure.spl:201,220,223` | entry-closure computation could not acquire/publish authority |
| `SCV-E-ENTRY: ...` | `native_build_closure.spl:177,179,239` | root-level entry without `--source`; entry outside admitted root; entry absent from frozen inventory |
| `SCV-E-SNAPSHOT: <reason>` | `native_build_closure.spl:196` | snapshot open failed |
| `SCV-E-SOURCE: ...` | `native_build_closure.spl:245` | source root absent from frozen inventory |

Reason strings you will meet after `SCV-E-ADMISSION:`:

| Reason | Source | What to do |
|---|---|---|
| `source-inventory-scope-unsupported` | `source_authority.spl:165,170`; `derived_composition.spl:131` | the selector is not under `src`/`test`/`examples/10_tooling` or a valid extra root; pass a relative `--source` inside the checkout |
| `source-inventory-root-empty: requested --source root '...'` | `source_authority.spl:208-213` | root has no `.spl`/`simple.sdn` rows, or listing is stale: delete `build/scv/source-inventory` and `build/scv/snapshots`, rerun |
| `snapshot-source-owner-mismatch`, `snapshot-source-manifest-unreadable`, `snapshot-source-manifest-mismatch`, `snapshot-source-count-mismatch`, `snapshot-source-membership-mismatch`, `source-inventory-generation-mismatch` | `source_authority.spl:42-47,81-88,135-143` | inherited `SIMPLE_SCV_*` env does not match the snapshot on disk; unset them or use `--refresh-source-authority` |
| `snapshot-authority-env-publish-failed`, `snapshot-authority-env-clear-failed`, `source-authority-env-publish-failed`, `source-authority-env-clear-failed` | `native_build_main.spl:1915,1930`; `admission.spl:91,154` | `env_set` failed; environment is not writable |
| `repository-root-unavailable` | `admission.spl:99` | cwd is not an absolute plain checkout path |
| `package-index:stale-graph-rebuild-required` | `admission.spl:111-113` | package-module index bound to another snapshot; set `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`. (`cold-rebuild-pending` is *not* a refusal: admission succeeds with that reason string, `:156`.) |
| `git-event-refresh-failed`, `git-event-source-unavailable`, `inventory-*` (`inventory-absent`, `inventory-pointer-invalid`, `inventory-publication-digest-mismatch`, ...) | `src/lib/scv/*.spl`, `inventory_events.spl` | the incremental git-event refresh or the inventory store is broken; `SIMPLE_SCV_INVENTORY_COLD_INIT=1` rebuilds it |

## 5. Debugging

1. Read the first `SCV-E-*` line. Tools strip a leading `error: ` and treat
   only an exact `SCV-E-ADMISSION:` line start as an authority failure
   (`builder_compiler_admission_diagnostic_v1`,
   `src/app/bootstrap_builder/compiler_admission_diagnostic.spl:4-13`), so
   quoted mentions in test output are not failures.
2. Check inherited state: `env | grep SIMPLE_SCV_`. A stale
   `SIMPLE_SCV_SNAPSHOT_ROOT` from a parent shell makes every child re-open
   a dead generation. Unset the eight variables listed in 2.1 or run
   `native-build --refresh-source-authority`.
3. Inspect the snapshot: `ls build/scv/snapshots/`, then
   `head $SIMPLE_SCV_SNAPSHOT_ROOT/SCV_COMPILE_INVENTORY`.
4. Reset: `rm -rf build/scv/source-inventory build/scv/snapshots` (the
   recovery advice baked into `source_authority.spl:212`), then rerun with
   `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
5. Cost: `SIMPLE_INVENTORY_TRACE_ATTEMPT=debug` prints inventory and
   snapshot nanoseconds (`source_authority.spl:184-196`).

## 6. Testing

Run one spec with `bin/simple test <relative path>` from the repo root
(an absolute path runs nothing and still exits 0; trust only the
`SPEC FILE VERDICT ... executed=N` line).

- Source authority: `test/01_unit/app/compiler_entrypoint/source_authority_spec.spl`
  (imports `compiler_source_authority_acquire_v1`, `_publish_v1`,
  `_open_published_v1`, `:2-7`), `scv_auto_admit_spec.spl` (auto cold-init
  and fail-closed on mutation before freeze),
  `derived_composition_spec.spl`, `cuda_composition_selector_spec.spl`,
  `inventory_root_coverage_spec.spl`, `cold_rebuild_admission_spec.spl`.
- Diagnostic parsing: `test/01_unit/app/bootstrap_builder/compiler_admission_diagnostic_spec.spl`;
  entry-closure refusals: `test/01_unit/app/io/_CliCompile/native_build_entry_closure_scv_fallback_spec.spl`.
- Snapshot library: `test/01_unit/lib/scv/compile_snapshot_*_spec.spl`
  (alias selection, byte reads, parent creation, reclamation, retention,
  revision reuse, source roots).
- Cache contract: `test/01_unit/compiler/cache/cache_contract_codec_spec.spl`,
  `summary_store_v1_spec.spl`, `summary_store_byte_paging_spec.spl`,
  `three_payload_worker_execution_v3_spec.spl`;
  `test/02_integration/compiler/cache/virtual_summary_registration_protocol_spec.spl`.
- Cache v2 and the Lean gate: see [semantic_build_cache.md](semantic_build_cache.md).

To provoke a refusal by hand, point `native-build --source` at a directory
that holds no `.spl` or `simple.sdn` files and read the `SCV-E-ADMISSION:`
reason against the table in section 4; the exact reason depends on whether
the selector resolves (`source-inventory-scope-unsupported`) or resolves to
an empty root (`source-inventory-root-empty`).
