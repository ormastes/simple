# bench_comparison_spec

> Bench Comparison Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bench_comparison_spec

Bench Comparison Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/bench_comparison_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Bench Comparison Specification

Validates that the benchmark harness includes FAT32, RamFS in all
4 workloads and that the POSIX baseline runner produces BenchResult
with p50/p99 metrics for comparison reporting.

## Scenarios

### Bench Harness — FAT32 coverage

#### AC-6: make_fat32_table returns a MountTable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-6: make_fat32_table returns a MountTable
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: make_fat32_table returns a MountTable")
val mt = make_fat32_table()
val r = mt.stat("/fat32")
val ok = r.is_ok()
expect(ok).to_equal(true)
```

</details>

#### AC-6: FAT32 driver name present in run_all results

- AC-6: FAT32 driver name present in run_all results


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: FAT32 driver name present in run_all results")
val results = run_all()
val names = results.map(fn(r: BenchResult) -> text: r.driver_name)
expect(names).to_contain("fat32")
```

</details>

### Bench Harness — RamFS coverage

#### AC-6: make_ramfs_table returns a MountTable

- AC-6: make_ramfs_table returns a MountTable
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: make_ramfs_table returns a MountTable")
val mt = make_ramfs_table()
val r = mt.stat("/ramfs")
val ok = r.is_ok()
expect(ok).to_equal(true)
```

</details>

#### AC-6: RamFS driver name present in run_all results

- AC-6: RamFS driver name present in run_all results


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: RamFS driver name present in run_all results")
val results = run_all()
val names = results.map(fn(r: BenchResult) -> text: r.driver_name)
expect(names).to_contain("ramfs")
```

</details>

### Bench Harness — workload completeness

#### AC-6: run_all includes metadata_storm workload

- AC-6: run_all includes metadata_storm workload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_all includes metadata_storm workload")
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("metadata_storm")
```

</details>

#### AC-6: run_all includes append_heavy_log workload

- AC-6: run_all includes append_heavy_log workload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_all includes append_heavy_log workload")
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("append_heavy_log")
```

</details>

#### AC-6: run_all includes random_overwrite workload

- AC-6: run_all includes random_overwrite workload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_all includes random_overwrite workload")
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("random_overwrite")
```

</details>

#### AC-6: run_all includes mmap_read_mostly workload

- AC-6: run_all includes mmap_read_mostly workload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_all includes mmap_read_mostly workload")
val results = run_all()
val wl = results.map(fn(r: BenchResult) -> text: r.workload_name)
expect(wl).to_contain("mmap_read_mostly")
```

</details>

### POSIX Baseline — runner produces results

#### AC-6: run_posix_metadata_storm returns BenchResult with p50

- AC-6: run_posix_metadata_storm returns BenchResult with p50


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_posix_metadata_storm returns BenchResult with p50")
val r = run_posix_metadata_storm()
expect(r.p50_us).to_be_greater_than(0)
```

</details>

#### AC-6: run_posix_append_log returns BenchResult with p99

- AC-6: run_posix_append_log returns BenchResult with p99


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_posix_append_log returns BenchResult with p99")
val r = run_posix_append_log()
expect(r.p99_us).to_be_greater_than(0)
```

</details>

#### AC-6: run_posix_random_overwrite returns BenchResult

- AC-6: run_posix_random_overwrite returns BenchResult
   - Expected: name equals `posix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_posix_random_overwrite returns BenchResult")
val r = run_posix_random_overwrite()
val name = r.driver_name
expect(name).to_equal("posix")
```

</details>

#### AC-6: run_posix_mmap_read returns BenchResult

- AC-6: run_posix_mmap_read returns BenchResult
   - Expected: name equals `posix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_posix_mmap_read returns BenchResult")
val r = run_posix_mmap_read()
val name = r.driver_name
expect(name).to_equal("posix")
```

</details>

### Bench Comparison — report shape

#### AC-6: run_all results contain p50_us and p99_us fields

- AC-6: run_all results contain p50_us and p99_us fields
   - Expected: has_p50 is true
   - Expected: has_p99 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: run_all results contain p50_us and p99_us fields")
val results = run_all()
val first = results[0]
val has_p50 = first.p50_us >= 0
val has_p99 = first.p99_us >= 0
expect(has_p50).to_equal(true)
expect(has_p99).to_equal(true)
```

</details>

#### AC-6: POSIX baseline included alongside Simple drivers

- AC-6: POSIX baseline included alongside Simple drivers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: POSIX baseline included alongside Simple drivers")
val results = run_all()
val names = results.map(fn(r: BenchResult) -> text: r.driver_name)
expect(names).to_contain("posix")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `33d159b9e8acdb88288501f2969c73c2e0f863f235deb125846e64f5f6cc875e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33d159b9e8acdb88288501f2969c73c2e0f863f235deb125846e64f5f6cc875e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33d159b9e8acdb88288501f2969c73c2e0f863f235deb125846e64f5f6cc875e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/bench_comparison_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/bench_comparison_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/bench_comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/bench_comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/bench_comparison_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: make_fat32_table returns a MountTable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/bench_comparison_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: FAT32 driver name present in run_all results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/bench_comparison_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: make_ramfs_table returns a MountTable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
