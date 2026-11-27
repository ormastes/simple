# Configured library mode: native qualification plan

Status: **NOT_RUN**. Source candidate only. No verified Phase3 compiler is available for this change. No compiler, helper, linker or runtime has been launched for these cases. Source inspection is not stage parity or native qualification.

## Contract

The operator selects `--library-mode=nogc-sync-mut` (or the split value form), not a physical family source root. The normalized semantic token is request-owned `CompileOptions.library_mode`; it derives existing `gc_off` and `allowed_families`. The eight `gc|nogc` ? `sync|async` ? `mut|immut` combinations are accepted. Only `noalloc-async-mut` maps to the existing no-allocation owner. Unsupported tokens, missing values and duplicate flags fail with attributable `LIBRARY_MODE_*` diagnostics.

No mode preserves prior behavior, including nonempty legacy target allowlists. It does not select a global NoGC default. No new application-specific configuration or environment selector is introduced. Existing project/target code can populate the same typed field; this patch adds the native CLI transport because no current project configuration carries the hosted concurrency choice into this worker path. Runtime-tier, host CPU and runtime/provider admission remain separate.

Generic `std.X` and its existing canonical `lib.X` spelling select the configured owner plus shared common. Explicit physical-owner imports retain owner coherence. An app-selected NoGC `std.X` and an explicit GC owner's internal `std.X` use separate private registry coordinates; authored imports and defining-module names remain unchanged. Selected missing owners or exports cannot fall back to another family. Platform/composition facades already selected by exact declared roots remain authoritative.

## Executable specifications

| Specification | Authored cases | Boundary | Executed / failed / blocked / not run |
|---|---:|---|---|
| `test/01_unit/compiler/library_mode_policy_v1_spec.spl` | 6 | Actual policy parser, restrictions, legacy digest, invocation identity | 0 / 0 / 0 / 6 |
| `test/02_integration/compiler/library_mode_selection_spec.spl` | 6 | Actual filesystem resolver, logical-owner provenance, same-source interleaved keys | 0 / 0 / 0 / 6 |
| `test/02_integration/compiler/library_mode_cache_io_spec.spl` | 2 | Actual on-disk HIR store/load, wrong-mode header refusal, recipe codec | 0 / 0 / 0 / 2 |
| `test/02_integration/compiler/library_mode_frozen_surfaces_spec.spl` | 3 | Actual parser, frozen aliases, HIR/common re-export, retained no-import declaration replay | 0 / 0 / 0 / 3 |

Total: **17 authored, 0 executed, 0 passed, 0 failed, 17 NOT_RUN**. These tests import production owners. The cache case must run in a fresh process with a newly created private `SIMPLE_HIR_CACHE_DIR`, normal admitted frontend/compiler scope and `SIMPLE_TEST_LIBRARY_MODE_CACHE_IO=1`; missing prerequisites fail the case. It stores distinct real HIR modules, reads both, rejects wrong-mode and legacy-header requests, revisits the first mode, and deletes only the three entries it owns after success. Failure artifacts remain available. Recipe-only descriptors are explicitly not admission evidence.

## Native owner/value matrix

Use `test/fixtures/compiler/library_mode_selection`; ordinary entries are under `src/app`, and the common library root is `src/lib`. The generic entry prints the physical owner name, its distinct value, and a shared-common value reached through named plus wildcard re-exports. All rows below are **NOT_RUN**. A failed row is retained and stops dependent retries; do not replace it with a helper-only pass.

| Row | Entry | Mode | Cache | Required observable result |
|---|---|---|---|---|
| N1 | `entry.spl` | split `--library-mode nogc-sync-mut` | fresh private A | exit 0; stdout `nogc_sync_mut:101:404` |
| N2 | `entry.spl` | same | warm A | same stdout; actual compatible HIR hit receipts |
| N3 | `entry.spl` | inline `--library-mode=gc-sync-mut` | same A | `gc_sync_mut:202:404`; no NoGC body reuse |
| N4 | `entry.spl` | `nogc-sync-mut` | same A after N3 | original stdout and compatible mode-A hits |
| N5 | `mixed_entry.spl` | `nogc-sync-mut` | private B | `nogc_sync_mut:101|gc_sync_mut:202|404` |
| N6 | `internal_entry.spl` | `nogc-sync-mut` | private C | explicit async owner remains `nogc_async_mut:303` |
| N7 | `missing_owner.spl` | `nogc-sync-mut` | private D | nonzero; `LIBRARY_MODE_OWNER_MISSING`; no executable |
| N8 | `missing_symbol.spl` | `nogc-sync-mut` | private E | nonzero; `LIBRARY_MODE_SYMBOL_MISSING`; another loaded family's same symbol cannot rescue it |
| N9 | `lib/gc_sync_mut/project/src/app/ancestor_entry.spl` (relative to fixture root) | `nogc-sync-mut` | private F | `nogc_sync_mut:101`; unrelated checkout ancestors cannot select GC |

For N9 use its full table entry path instead of the ordinary `src/app/<entry>` path.

N1?N4 are sequential in one isolated cache namespace, with compiler/runtime/source/provider identity unchanged. Preserve per-row cache summaries and mode-bound entry headers/keys; timestamps alone are not cache evidence. The frozen-surface specification separately exercises same-process replay and changed-mode refusal. Native N5 must use the real body/replay path where available; record whether it actually did, not an inferred pass from its stdout.

The command shape, after root admission and a resource slot, is:

```text
<admitted-P3> native-build test/fixtures/compiler/library_mode_selection/src/app/<entry> --source test/fixtures/compiler/library_mode_selection --source test/fixtures/compiler/library_mode_selection/src/lib --source src/providers/windows_native/lib --source src/app --source src/lib --source src/os --source src/compiler --library-mode <mode> --target x86_64-pc-windows-msvc --threads 1 --runtime-path <matching-admitted-runtime> -o <private-row-output>
```

`<...>` values are mandatory coordinator substitutions from actual verified artifacts, never paths that count as admission by their spelling. Select the backend and runtime invocation syntax from that producer's verified admission recipe. Do not silently substitute another runtime or use Rust seed, helper direct linking, physical-family `--source`, or reduced guards.

Before any row: pin producer SHA256, source commit and clean owned diff, exact SCV authority/inventory digest, matching runtime/provider receipt hashes, target/backend, source roots, argv and private cache roots. Require that compiler's actual Hello compile/run and normal admission. Commit fixture sources before publishing immutable source authority. Limits: 5,859,375 KiB enforced process-tree memory, 600 s compile, 15 s product run, one native compiler at a time. Capture independent process-tree peak, exits, elapsed time, stdout/stderr, cache counts and terminal quiescence. Never increase caps or repeat an unchanged failed build. Native GC rows require an admitted runtime/provider that supports the chosen GC semantics.

## Byte compatibility and transport review

- Parent native CLI parses once, excludes the value from entry-path parsing, publishes a mode-bound closure policy digest, and forwards original argv.
- Slim parse worker reparses the same token, sets typed options, and uses the same closure selection. Native worker sets the same three fields.
- Ordinary source closure and frozen alias replay pass the same retained logical importer owner to physical selection and the private alias helper. Physical importer directories are used only for legacy/relative lookup. The configured policy does not scan path ancestors; only leading logical `std.<family>` or `lib.<family>` identifies an internal owner.
- Surface builders/registries carry explicit mode through import/export freezing and body replay; HIR lowerers carry it into selected-export diagnostics. Replay compares requested mode to the retained frozen registry before reconstruction, then compares the new registry against both. The no-import corpus regression mutates only the request mode, so refusal cannot be caused by missing imports.
- HIR cache key/header/parser-binding/load/store arguments are optional and default empty; no process-global selector exists. Private body custody checks request/input mode equality before acceptance.
- Empty mode preserves old closure policy digest bytes, HIR key/header framing, options/no-op/prelower/MIR/weave identities, and existing mono recipe v1?v4 bytes. Configured-only recipe v5 serializes and validates mode. Actual cache identities bind nonempty mode.
- Inactive NBO1 payload code is unchanged; it is not evidence for active worker transport.

Source-only review is required before integration. Core/library/MCP smoke and actual native fixture execution remain pending behind the verified compiler gate; this document does not waive those checks.

## Review correction cycle 2

P1: configured selection previously scanned arbitrary `lib/<family>` path ancestors while scoped aliases used a logical module owner. The corrected resolver takes separate physical location and retained logical owner arguments; missing/path-shaped logical contexts fail with `LIBRARY_MODE_IMPORT_CONTEXT_INVALID`. The fixture layout now uses real `src/app` and `src/lib` canonical namespaces, and a hostile-ancestor application is checked through the actual parent owner collector, resolver and preclosed alias APIs.

P2: replay formerly compared only a newly constructed ctx-derived mode. It now refuses a mismatch against the pre-existing retained registry before any replay; the no-import regression tests that exact provenance boundary. Both findings are source-corrected pending independent rereview and native execution, not marked verified by this document. The canonical native CLI help now lists `--library-mode`.
