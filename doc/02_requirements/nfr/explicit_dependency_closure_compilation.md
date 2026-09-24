# Explicit Dependency-Closure Compilation NFRs

## Selection

Balanced production targets are selected, with correctness/count gates taking
precedence. The user authorized a 10% target or a better assigned value; this
document selects materially stronger warm-build targets while retaining a 10%
maximum-regression bootstrap guard.

## Non-functional requirements

### NFR-001 — Snapshot isolation

After freeze admission: live-worktree source opens = 0; Git/SCV user-state
writes = 0; active-snapshot mutations = 0. Concurrent edits shall not change any
artifact, diagnostic, action ID, or receipt of the active build.

### NFR-002 — No hidden scans

Requested-package compilation shall execute 0 recursive source-tree discovery
walks, open 0 unrelated `.spl` files, and read 0 unrelated package summaries.
Any cold/overflow reconciliation shall be separately named and receipted.

### NFR-003 — Source-open bound

For an admitted clean catalog, source opens = 0. Otherwise source opens shall be
exactly the frozen source sets of dirty, missing, incompatible, corrupt, or
selected packages—never repository-size dependent when closure and dirty sets
are fixed.

### NFR-004 — Graph complexity

Closure planning shall be O(V + E) over reached packages/import edges. Catalog
and header reads shall be no more than `2 * V + E + 1`. Each package/SCC action
shall be scheduled no more than once per build.

### NFR-005 — Determinism and reproducibility

For fixed snapshot, options, toolchain, and target, serial/parallel and
cold/warm builds shall produce byte-identical normalized artifacts, catalog
records, action IDs, and diagnostics. Absolute workspace path changes shall not
change them.

### NFR-006 — Integrity

Truncated, reordered, replayed, tampered, symlink-aliased, wrong-revision,
wrong-generation, wrong-target, wrong-toolchain, wrong-options, or digest-invalid
metadata shall be rejected before reuse with one stable reason code.

### NFR-007 — Atomicity and recovery

At every injected crash boundary, restart shall expose either the previous
admitted snapshot/catalog or the complete new one, never a partial state.
Recovery and GC shall modify only `build/scv/` and complete in bounded time over
owned staging/lease records.

### NFR-008 — Parallel bounds

Worker count shall be configurable and bounded. Parent-authoritative commit order
shall be canonical. Parallel execution shall not increase max RSS above 110% of
the admitted serial baseline at the default worker count.

### NFR-009 — Performance

On representative 25-, 250-, and 1,000-package fixtures:

- clean warm wall time ≤ 25% of current `--entry-closure` baseline;
- one private-body/comment edit wall time ≤ 35% of baseline;
- p95 metadata read ≤ 64 KiB per reached package;
- bootstrap/source-led closure wall time and RSS regress ≤ 10% from the admitted
  current baseline;
- 20 warm daemon builds grow RSS by ≤ 5% after steady state.

### NFR-010 — Quiet observability

Successful automatic event refresh, freeze, cache hit, and cleanup shall produce
no default console output. Every operation shall emit bounded internal receipts.
Failure/drift diagnostics shall be concise, deterministic, and identify revision,
package, reason code, and recovery action without dumping source contents.

### NFR-011 — Write containment

Automated filesystem writes shall be confined to ignored `build/scv/`. Tests
shall prove unchanged content, mode, mtime, index checksum, refs, HEAD, SCV user
workspace revision, and lock inventory for all developer-owned paths/state.

### NFR-012 — Remote trust boundary

Remote cache data is untrusted until local digest/schema/action/revision
admission. Network failure shall degrade to local immutable execution without
changing semantics or widening discovery.
