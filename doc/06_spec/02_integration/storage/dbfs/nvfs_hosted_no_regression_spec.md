# nvfs_hosted_no_regression_spec

> NVFS Hosted Seam Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_hosted_no_regression_spec

NVFS Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVFS Hosted Seam Specification

Runs the same hosted mount-table contract as FAT32 so NVFS can share the
filesystem regression seam used by FAT32 and DBFS.

## Scenarios

### NVFS hosted seam — mount and stat

#### NVFS volume mounts without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- NVFS volume mounts without error


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS volume mounts without error")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val mt = make_nvfs_mounted()
assert_mount_root_is_dir(mt, "/nvfs")
```

</details>

#### stat on NVFS root returns is_dir=true

- stat on NVFS root returns is_dir=true


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stat on NVFS root returns is_dir=true")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val mt = make_nvfs_mounted()
assert_mount_root_slash_is_dir(mt, "/nvfs")
```

</details>

### NVFS hosted seam — readdir and open

#### readdir on NVFS root returns a stable empty-or-better listing

- readdir on NVFS root returns a stable empty-or-better listing


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("readdir on NVFS root returns a stable empty-or-better listing")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val mt = make_nvfs_mounted()
assert_readdir_on_root_is_stable(mt, "/nvfs")
```

</details>

#### open on an NVFS path returns a valid handle

- open on an NVFS path returns a valid handle


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("open on an NVFS path returns a valid handle")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val mt = make_nvfs_mounted()
assert_open_returns_handle(mt, "/nvfs/README.TXT")
```

</details>

#### read on NVFS returns empty content rather than erroring

- read on NVFS returns empty content rather than erroring


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read on NVFS returns empty content rather than erroring")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val mt = make_nvfs_mounted()
assert_read_returns_empty_or_better(mt, "/nvfs/README.TXT")
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

- Canonical SPipe generation for source `c483fd1a7fdb65af28b6ed53f7b5b4beab0e9313f6b03fdb2bc1a35717f33993`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c483fd1a7fdb65af28b6ed53f7b5b4beab0e9313f6b03fdb2bc1a35717f33993`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c483fd1a7fdb65af28b6ed53f7b5b4beab0e9313f6b03fdb2bc1a35717f33993`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
