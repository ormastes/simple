# Frozen Package Compilation System Test Plan

## Status

Design only. Planned executable spec:
`test/03_system/app/compiler/feature/explicit_dependency_closure_compilation_spec.spl`.
Planned generated/manual evidence:
`doc/06_spec/03_system/app/compiler/feature/explicit_dependency_closure_compilation_spec.md`.

No `.spl` spec is created in this handoff.

## Test strategy

Use hermetic fixture workspaces with 25, 250, and 1,000 packages, unrelated
source forests, import diamonds, cycles, generated packages, variants, and a
fake read-only Git event adapter. Instrument every filesystem/process access and
snapshot/catalog/action receipt. Run serial and bounded-parallel variants.

## Shared SPipe vocabulary

Required step text:

- `step("Freeze the workspace into an admitted SCV snapshot")`
- `step("Seed an admitted package index")`
- `step("Request one package build")`
- `step("Inspect closure and access receipts")`
- `step("Mutate the live worktree during the build")`
- `step("Create the next SCV snapshot")`
- `step("Crash publication at a named boundary")`
- `step("Restart and recover the previous generation")`
- `step("Compare serial and parallel artifacts")`

Required helpers:

- `setup_scv_package_workspace_fixture`
- `freeze_scv_snapshot`
- `run_package_compile`
- `read_package_access_receipt`
- `assert_no_recursive_scan`
- `assert_snapshot_only_reads`
- `assert_user_state_unchanged`
- `mutate_live_worktree`
- `inject_package_metadata_fault`
- `read_package_index_generation`
- `read_scv_provenance_receipt`

Until implemented, every scenario/helper placeholder must call
`fail("explicit dependency-closure compilation scenario not implemented")`.
Placeholder passes, `pass_todo`, and tautological expectations are forbidden.

## Fixture topology

```text
app -> api -> model -> util
    -> ui  -> model
cycle_a <-> cycle_b <-> cycle_c
generated_consumer -> generated_api
variant_consumer -> tagged_provider
unrelated/0001..N/*.spl
```

Each package has comment-only, private-body, export, layout, initializer,
provider, import-resolution, generated-input, and configuration mutation forms.

## Functional scenarios

| ID | Scenario and assertions | Trace |
|---|---|---|
| ST-001 | Compile invocation automatically freezes before first discovery; receipt ordering proves freeze precedes catalog read. | REQ-001 |
| ST-002 | All post-freeze source reads use snapshot paths; injected live-root read fails `SCV-E-SNAPSHOT-READ-ESCAPE`. | REQ-002 |
| ST-003 | Successful compile changes only `build/scv/`; source/docs/config mtimes, Git index checksum, HEAD/refs/locks, and SCV workspace revision remain equal. | REQ-003 |
| ST-004 | Git checkout/merge/editor events quietly refresh owned inventory; success emits no console text and leaves a receipt. | REQ-004, REQ-017 |
| ST-005 | Event overflow produces named reconciliation receipt; unavailable reconciliation fails without recursive compiler scan. | REQ-004 |
| ST-006 | Catalog generation rejects wrong SCV revision/inventory and accepts the matching immutable generation. | REQ-005 |
| ST-007 | TLDR/SMF round trip preserves every required section and rejects duplicate/reordered/tampered sections. | REQ-006 |
| ST-008 | Comment edit changes content digest but not export/initializer/provider digests. | REQ-007 |
| ST-009 | Requested `app` reaches exactly explicit imports; a 100,000-file unrelated forest yields zero opens/listings/metadata reads. | REQ-008 |
| ST-010 | Clean warm build opens zero source; one dirty package opens exactly its frozen source set. | REQ-009 |
| ST-011 | Comment/whitespace edit reparses changed package and invalidates zero dependents. | REQ-010 |
| ST-012 | Private-body edit rebuilds producer; only explicit body consumers invalidate. | REQ-010 |
| ST-013 | Export/layout change invalidates exact typed reverse closure. | REQ-010 |
| ST-014 | Initializer/provider changes propagate only through matching reverse projections. | REQ-010 |
| ST-015 | Action/archive hit binds exact SCV revision and semantic dependency fold; one changed input rejects hit. | REQ-011 |
| ST-016 | Three-package cycle compiles/publishes once as one deterministic SCC. | REQ-012 |
| ST-017 | Independent SCCs execute concurrently, at most once, while commit and diagnostics remain canonical. | REQ-013 |
| ST-018 | Build tags/target/provider variants produce distinct catalog/action namespaces. | REQ-014 |
| ST-019 | Generated action writes only internal blob; generated digest participates in consumer action. | REQ-014 |
| ST-020 | Crash matrix before/after seal/rename/pointer exposes old or complete new generation, never partial state. | REQ-015 |
| ST-021 | Concurrent edit during build cannot alter active artifact/action/diagnostic; drift schedules or rejects a separate next build. | REQ-016 |
| ST-022 | Snapshot GC preserves active leases, removes only expired owned data, and emits bounded receipt. | REQ-016 |
| ST-023 | Daemon reuses decoded catalog/summary across 20 builds without stale generation reuse. | REQ-017 |
| ST-024 | Remote hit is rehashed/readmitted; corruption/network failure falls back locally without discovery widening. | REQ-018 |
| ST-025 | Empty-cache bootstrap freezes explicit roots, opens only reached closure, and publishes first admitted catalog. | REQ-019 |
| ST-026 | Cutover checker proves CLI/driver broad closure walkers cannot execute in package mode. | REQ-020 |

## Integrity fault matrix

Run ST-006/ST-007/ST-015 with truncated file, wrong schema, stale generation,
wrong revision, wrong target/toolchain/options, replayed receipt, digest mismatch,
unsafe path, symlink escape, duplicate package ID, reordered edge, missing archive,
and incomplete SCC. Every case must fail before reuse with one stable code.

## Crash boundaries

Inject faults after staging create, content write, inventory write, summary write,
archive write, self-seal, fsync, generation rename, pointer temporary write,
pointer rename, lease create/release, and GC quarantine move. Verify owned-path
containment and idempotent one-pass recovery.

## Performance and NFR evidence

| Evidence | Gate |
|---|---|
| Snapshot access receipt | live-worktree reads 0 after admission |
| Discovery access receipt | recursive scans 0; unrelated opens/metadata 0 |
| Source-open receipt | clean 0; dirty exact source-set bound |
| Graph metrics | reads ≤ `2V + E + 1`; planning O(V+E); each SCC once |
| Determinism matrix | serial/parallel, cold/warm, path-relocated outputs equal |
| Git/SCV state manifest | index/HEAD/refs/locks/workspace revision and developer mtimes equal |
| Crash matrix | old or complete new generation only |
| Benchmark matrix | warm ≤25%; private/comment ≤35%; bootstrap regression ≤10% |
| Memory matrix | parallel RSS ≤110%; 20-build daemon growth ≤5% |
| Console capture | successful automatic operation emits zero lines |

## Acceptance procedure

1. Build fixtures and baseline current `--entry-closure` once.
2. Run each functional scenario once in interpreter and deployed self-hosted
   runtime where supported.
3. Run integrity/crash matrices once with deterministic fault names.
4. Run performance/RSS evidence on an otherwise idle host and retain raw receipts.
5. Generate the manual from the executable spec only after all assertions are
   real and green.
6. Verify requirement/NFR traceability and absence of `.spl` specs under
   `doc/06_spec`.

## Exit criteria

All REQ-001..020 and NFR-001..012 have positive and negative evidence; no stub,
hidden full scan, live fallback, user-state mutation, nondeterministic artifact,
or unreceipted recovery remains.
