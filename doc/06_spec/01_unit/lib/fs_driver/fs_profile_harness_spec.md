# Fs Profile Harness Specification

> Tests covering fs_bench_harness, time_function, create_benchmark_suite, add_benchmark.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Profile Harness Specification

## Scenarios

### fs_bench_harness

### time_function

#### AC-1: returns elapsed microseconds greater than zero for RamFS open

- AC-1: returns elapsed microseconds greater than zero for RamFS open


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds greater than zero for RamFS open")
val elapsed = time_function("ramfs_open")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for RamFS open

- AC-1: returns elapsed microseconds within reasonable range for RamFS open


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds within reasonable range for RamFS open")
val elapsed = time_function("ramfs_open")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for RamFS stat

- AC-1: returns elapsed microseconds greater than zero for RamFS stat


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds greater than zero for RamFS stat")
val elapsed = time_function("ramfs_stat")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for RamFS stat

- AC-1: returns elapsed microseconds within reasonable range for RamFS stat


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds within reasonable range for RamFS stat")
val elapsed = time_function("ramfs_stat")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for RamFS close

- AC-1: returns elapsed microseconds greater than zero for RamFS close


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds greater than zero for RamFS close")
val elapsed = time_function("ramfs_close")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for RamFS close

- AC-1: returns elapsed microseconds within reasonable range for RamFS close


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds within reasonable range for RamFS close")
val elapsed = time_function("ramfs_close")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for FAT32 parse

- AC-1: returns elapsed microseconds greater than zero for FAT32 parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds greater than zero for FAT32 parse")
val elapsed = time_function("fat32_parse_superblock")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for FAT32 parse

- AC-1: returns elapsed microseconds within reasonable range for FAT32 parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds within reasonable range for FAT32 parse")
val elapsed = time_function("fat32_parse_superblock")
expect elapsed < 1000000
```

</details>

#### AC-1: returns elapsed microseconds greater than zero for FAT32 fat_search_long

- AC-1: returns elapsed microseconds greater than zero for FAT32 fat_search_long


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds greater than zero for FAT32 fat_search_long")
val elapsed = time_function("fat32_fat_search_long")
expect elapsed > 0
```

</details>

#### AC-1: returns elapsed microseconds within reasonable range for FAT32 fat_search_long

- AC-1: returns elapsed microseconds within reasonable range for FAT32 fat_search_long


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns elapsed microseconds within reasonable range for FAT32 fat_search_long")
val elapsed = time_function("fat32_fat_search_long")
expect elapsed < 1000000
```

</details>

### create_benchmark_suite

#### AC-1: creates a suite with a non-empty name

- AC-1: creates a suite with a non-empty name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: creates a suite with a non-empty name")
val suite = create_benchmark_suite("ramfs_suite")
expect suite.name == "ramfs_suite"
```

</details>

#### AC-1: new suite has zero recorded timings

- AC-1: new suite has zero recorded timings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: new suite has zero recorded timings")
val suite = create_benchmark_suite("empty_suite")
expect suite.count == 0
```

</details>

### add_benchmark

#### AC-1: adds a timing entry and increments count

- AC-1: adds a timing entry and increments count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: adds a timing entry and increments count")
val suite = create_benchmark_suite("test_suite")
val suite2 = add_benchmark(suite, "ramfs_open", 42)
expect suite2.count == 1
```

</details>

#### AC-1: recorded timing value matches inserted value

- AC-1: recorded timing value matches inserted value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: recorded timing value matches inserted value")
val suite = create_benchmark_suite("test_suite")
val suite2 = add_benchmark(suite, "ramfs_open", 99)
expect suite2.last_timing == 99
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/fs_profile_harness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fs_bench_harness, time_function, create_benchmark_suite, add_benchmark.
- fs_bench_harness
- time_function
- create_benchmark_suite
- add_benchmark

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f7125b5ae3542ea0b1197cd5f945f0b3cd34642269d01f3855e5b7dac2ece11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f7125b5ae3542ea0b1197cd5f945f0b3cd34642269d01f3855e5b7dac2ece11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f7125b5ae3542ea0b1197cd5f945f0b3cd34642269d01f3855e5b7dac2ece11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/fs_driver/fs_profile_harness_spec.spl
mirror: doc/06_spec/01_unit/lib/fs_driver/fs_profile_harness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/fs_driver/fs_profile_harness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/fs_driver/fs_profile_harness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/fs_driver/fs_profile_harness_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns elapsed microseconds greater than zero for RamFS open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/fs_driver/fs_profile_harness_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns elapsed microseconds within reasonable range for RamFS open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/fs_driver/fs_profile_harness_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns elapsed microseconds greater than zero for RamFS stat' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
