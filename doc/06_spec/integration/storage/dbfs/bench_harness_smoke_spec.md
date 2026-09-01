# bench_harness_smoke_spec

> BenchHarness Smoke Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bench_harness_smoke_spec

BenchHarness Smoke Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/bench_harness_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

BenchHarness Smoke Specification

Quick sanity checks for BenchResult and percentile helpers.
Verifies harness infrastructure compiles and basic math is correct.

## Scenarios

### BenchHarness — smoke (metadata storm, 10 files)

#### metadata_storm over DBFS completes for 10 files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- metadata_storm over DBFS completes for 10 files
   - Expected: i equals `10`
   - Expected: post_stat.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("metadata_storm over DBFS completes for 10 files")
val drv = DbFsDriver.new_hosted()
val paths: [text] = [
    "/smoke_0", "/smoke_1", "/smoke_2", "/smoke_3", "/smoke_4",
    "/smoke_5", "/smoke_6", "/smoke_7", "/smoke_8", "/smoke_9"
]
var i: i64 = 0
for path in paths:
    drv.open_path(Path(raw: path), OpenFlags.create_write()).unwrap()
    drv.unlink_path(path).unwrap()
    i = i + 1
expect(i).to_equal(10)
val post_stat = drv.stat("/smoke_5")
expect(post_stat.is_err()).to_equal(true)
```

</details>

#### BenchResult write_amplification returns 0 when logical_bytes=0

- BenchResult write_amplification returns 0 when logical_bytes=0
   - Expected: r.write_amplification() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("BenchResult write_amplification returns 0 when logical_bytes=0")
val r = BenchResult(
    workload_name: "test", driver_name: "x",
    p50_us: 0, p99_us: 0, bytes_written: 0, logical_bytes: 0,
    recovery_time_us: 0, mount_time_us: 0, rss_kib: 0, cache_hit_ratio: 0,
)
expect(r.write_amplification()).to_equal(0)
```

</details>

#### percentile of sorted list returns correct element

- percentile of sorted list returns correct element
   - Expected: p50 >= 50 and p50 <= 60 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("percentile of sorted list returns correct element")
val data: [i64] = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
val p50 = percentile(data, 50)
expect(p50 >= 50 and p50 <= 60).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `0a44a65249a9c9c2d2bec7b81df3fd1d79ae9c1c1e10f417f494033bc61656a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a44a65249a9c9c2d2bec7b81df3fd1d79ae9c1c1e10f417f494033bc61656a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a44a65249a9c9c2d2bec7b81df3fd1d79ae9c1c1e10f417f494033bc61656a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/storage/dbfs/bench_harness_smoke_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/bench_harness_smoke_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/bench_harness_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/bench_harness_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/bench_harness_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/bench_harness_smoke_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'metadata_storm over DBFS completes for 10 files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/bench_harness_smoke_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BenchResult write_amplification returns 0 when logical_bytes=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/bench_harness_smoke_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'percentile of sorted list returns correct element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
