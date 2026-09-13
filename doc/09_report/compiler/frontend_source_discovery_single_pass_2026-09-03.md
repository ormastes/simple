# Frontend source-discovery fixed-cost profile — 2026-09-03

## Scope

This audit profiled the fixed costs reachable before parsing in tiny
parse/check/SMF production commands, then inspected repeated repository scans,
module discovery, configuration parsing, registry construction, and semantic
passes. The implementation change is intentionally limited to one proven
source-discovery cost and does not alter parser, semantic, diagnostic, module
alias, or source ordering behavior.

## Runtime profile status

The installed self-hosted executable was
`/Users/ormastes/simple/bin/release/macos-arm64/simple` (`Simple v1.0.0-rc.1`).
One attempt per lane produced the following non-authoritative observations:

| Lane | Wall | Peak RSS | Semantic result |
|---|---:|---:|---|
| run tiny source | 20 ms | 10.41 MiB | rejected: `Error running` |
| check tiny source | 10 ms | 10.39 MiB | rejected: lint/format subprocess exit `-1` |
| compile tiny SMF | 20 ms | 10.39 MiB | rejected: `Compilation failed` |

These rows measure only the failing process floor and are not compile-speed
claims. The optimizer invocation also failed at startup. See
`doc/08_tracking/bug/simple_frontend_profile_runtime_unavailable_2026-09-03.md`.

## Audit result

- Entry-closure source content/import/sibling scanning already has a build-local
  normalized-path cache.
- Native module lookup already uses indexed/bucketed structures in current
  compilation paths.
- Project SDN parsing is not on the observed compiler-driver call graph, so no
  speculative cache was added.
- Registry retention and semantic-pass convergence have existing dedicated
  owners; this change does not duplicate them.
- Directory source collection performed one complete exclusion classification
  in the directory loop, then recursively called `_driver_collect_sources` for
  every accepted file and repeated the classification.

## Change

`src/compiler/80.driver/driver_source_loading.spl` now:

1. classifies each recursively walked candidate exactly once;
2. directly loads accepted files through `_driver_load_bulk_source_file`;
3. reads `SIMPLE_NATIVE_BUILD_ENTRY` once per directory instead of once per
   accepted file while preserving the shared entry-scan cache;
4. retains every prior exclusion, source read, module-name, alias, and ordering
   rule;
5. exposes a diagnostic-only classification counter reset with the existing
   build-local scan counters.

The five-file fixture contains three accepted Simple files, one excluded
`check.spl`, and one non-Simple file.

| Implementation | Candidate classifications | Selected modules |
|---|---:|---:|
| former recursive redispatch | 8 | 3 |
| single-pass dispatch | 5 | 3 |

This removes 37.5% of classification operations in the fixture. For a directory
with `N` accepted Simple files and `M` rejected candidates, the classification
count changes from `2N + M` to `N + M`; filesystem traversal remains O(files).

## Evidence

- `test/05_perf/compiler_frontend/source_discovery_single_pass_spec.spl`: 1/1
  PASS. Its exact count is mutation-sensitive: restoring recursive accepted-file
  dispatch changes the expected five operations to eight.
- `test/01_unit/compiler/driver/driver_collect_sources_single_definition_spec.spl`:
  8/8 PASS.
- `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`:
  15/15 PASS.
- Optimizer attempted once; unavailable runtime, no optimizer claim.

## Remaining profiling work

Rebuild an admitted self-hosted runtime from current sources, then rerun valid
tiny parse/check/SMF lanes with frontend phase counters. Until then, no wall-time
comparison against Go, C, Rust, or Python is valid.
