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
| Source | `test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Hosted Seam Specification

Runs the same hosted mount-table contract as FAT32 so DBFS stays compatible
with shared filesystem regression coverage.

## Scenarios

### DBFS hosted seam — mount and stat

#### DBFS volume mounts without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- DBFS volume mounts without error


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DBFS volume mounts without error")
val mt = make_dbfs_mounted()
assert_mount_root_is_dir(mt, "/data")
```

</details>

#### stat on DBFS root returns is_dir=true

- stat on DBFS root returns is_dir=true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stat on DBFS root returns is_dir=true")
val mt = make_dbfs_mounted()
assert_mount_root_slash_is_dir(mt, "/data")
```

</details>

### DBFS hosted seam — readdir and open

#### readdir on DBFS root returns a stable empty-or-better listing

- readdir on DBFS root returns a stable empty-or-better listing


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("readdir on DBFS root returns a stable empty-or-better listing")
val mt = make_dbfs_mounted()
assert_readdir_on_root_is_stable(mt, "/data")
```

</details>

#### open on a DBFS path returns a valid handle

- open on a DBFS path returns a valid handle


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("open on a DBFS path returns a valid handle")
val mt = make_dbfs_mounted()
assert_open_returns_handle(mt, "/data/README.TXT")
```

</details>

#### read on DBFS returns empty content rather than erroring

- read on DBFS returns empty content rather than erroring


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read on DBFS returns empty content rather than erroring")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `69a35f38382f334e1b4d9f568807b6620a38572d8ff22d897ca38148a47aa81d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `69a35f38382f334e1b4d9f568807b6620a38572d8ff22d897ca38148a47aa81d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `69a35f38382f334e1b4d9f568807b6620a38572d8ff22d897ca38148a47aa81d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_no_regression_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/storage/dbfs/dbfs_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DBFS volume mounts without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stat on DBFS root returns is_dir=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'readdir on DBFS root returns a stable empty-or-better listing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
