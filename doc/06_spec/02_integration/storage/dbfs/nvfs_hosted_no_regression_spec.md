# nvfs_hosted_no_regression_spec

> Verifies the nvfs hosted no regression behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_hosted_no_regression_spec

Verifies the nvfs hosted no regression behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the nvfs hosted no regression behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### NVFS hosted seam — mount and stat

#### NVFS volume mounts without error

- Verify: NVFS volume mounts without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_NVFS_HOSTED_NO_REGRESSI-001
step("Verify: NVFS volume mounts without error")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mt = make_nvfs_mounted()
assert_mount_root_is_dir(mt, "/nvfs")
```

</details>

#### stat on NVFS root returns is_dir=true

- Verify: stat on NVFS root returns is_dir=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_NVFS_HOSTED_NO_REGRESSI-001
step("Verify: stat on NVFS root returns is_dir=true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mt = make_nvfs_mounted()
assert_mount_root_slash_is_dir(mt, "/nvfs")
```

</details>

### NVFS hosted seam — readdir and open

#### readdir on NVFS root returns a stable empty-or-better listing

- Verify: readdir on NVFS root returns a stable empty-or-better listing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_NVFS_HOSTED_NO_REGRESSI-001
step("Verify: readdir on NVFS root returns a stable empty-or-better listing")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mt = make_nvfs_mounted()
assert_readdir_on_root_is_stable(mt, "/nvfs")
```

</details>

#### open on an NVFS path returns a valid handle

- Verify: open on an NVFS path returns a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_NVFS_HOSTED_NO_REGRESSI-001
step("Verify: open on an NVFS path returns a valid handle")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mt = make_nvfs_mounted()
assert_open_returns_handle(mt, "/nvfs/README.TXT")
```

</details>

#### read on NVFS returns empty content rather than erroring

- Verify: read on NVFS returns empty content rather than erroring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_NVFS_HOSTED_NO_REGRESSI-001
step("Verify: read on NVFS returns empty content rather than erroring")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ebc911ba24e1ea17c209dc48b69268d7f5e1c8c3de3fd7639fe6d0f6ec08bb6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ebc911ba24e1ea17c209dc48b69268d7f5e1c8c3de3fd7639fe6d0f6ec08bb6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ebc911ba24e1ea17c209dc48b69268d7f5e1c8c3de3fd7639fe6d0f6ec08bb6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
