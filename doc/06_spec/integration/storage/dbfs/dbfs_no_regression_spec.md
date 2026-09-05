# dbfs_no_regression_spec

> DBFS Hosted Seam Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_no_regression_spec

DBFS Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_no_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Hosted Seam Specification

Runs the same hosted mount-table contract as FAT32 so DBFS stays compatible
with shared filesystem regression coverage.

## Scenarios

### DBFS hosted seam — mount and stat

#### DBFS volume mounts without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_mount_root_is_dir(mt, "/data")
```

</details>

#### stat on DBFS root returns is_dir=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_mount_root_slash_is_dir(mt, "/data")
```

</details>

### DBFS hosted seam — readdir and open

#### readdir on DBFS root returns a stable empty-or-better listing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_readdir_on_root_is_stable(mt, "/data")
```

</details>

#### open on a DBFS path returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_open_returns_handle(mt, "/data/README.TXT")
```

</details>

#### read on DBFS returns empty content rather than erroring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_read_returns_empty_or_better(mt, "/data/README.TXT")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `078ef191829eb64ff3b499412defc7e2a5942bbe0657e690b05a13e8ac4f30d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `078ef191829eb64ff3b499412defc7e2a5942bbe0657e690b05a13e8ac4f30d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `078ef191829eb64ff3b499412defc7e2a5942bbe0657e690b05a13e8ac4f30d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/storage/dbfs/dbfs_no_regression_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_no_regression_spec.md (current)
findings: 11 blockers: 1
  narrative=80 structure=60 oracle=50
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/integration/storage/dbfs/dbfs_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'DBFS volume mounts without error' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'stat on DBFS root returns is_dir=true' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:40:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'readdir on DBFS root returns a stable empty-or-better listing' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/storage/dbfs/dbfs_no_regression_spec.spl:44:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'open on a DBFS path returns a valid handle' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
