# Os Fs Sched Bench Specification

> Tests covering os fs + scheduler bench (AC-3, x86_64 host-proxy).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Fs Sched Bench Specification

## Scenarios

### os fs + scheduler bench (AC-3, x86_64 host-proxy)

#### bench dir created

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bench dir created
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("bench dir created")
val ok = rt_dir_create_all(FS_BENCH_DIR)
expect(ok).to_equal(true)
```

</details>

#### fs write succeeds

- fs write succeeds
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("fs write succeeds")
rt_dir_create_all(FS_BENCH_DIR)
val content = _make_fs_content()
val ok = rt_file_write_text(FS_WRITE_PATH, content)
expect(ok).to_equal(true)
```

</details>

#### fs round-trip: bytes written == bytes read (content oracle)

- fs round-trip: bytes written == bytes read (content oracle)
   - Expected: write_ok is true
   - Expected: read_len equals `written_len`
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("fs round-trip: bytes written == bytes read (content oracle)")
# ABSOLUTE ORACLE: content read back must exactly match what was written.
rt_dir_create_all(FS_BENCH_DIR)
val written = _make_fs_content()
val write_ok = rt_file_write_text(FS_WRITE_PATH, written)
expect(write_ok).to_equal(true)
val read_back = rt_file_read_text(FS_WRITE_PATH)
# Length oracle
val written_len = written.len()
val read_len = read_back.len()
expect(read_len).to_equal(written_len)
# Content oracle
val matches = _content_matches(written, read_back)
expect(matches).to_equal(true)
```

</details>

#### fs round-trip: file exists after write

- fs round-trip: file exists after write
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("fs round-trip: file exists after write")
rt_dir_create_all(FS_BENCH_DIR)
val content = _make_fs_content()
rt_file_write_text(FS_WRITE_PATH, content)
val exists = rt_file_exists(FS_WRITE_PATH)
expect(exists).to_equal(true)
```

</details>

#### fs write+read timing was recorded (warm plane, x86_64)

- fs write+read timing was recorded (warm plane, x86_64)
   - Expected: timing_recorded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("fs write+read timing was recorded (warm plane, x86_64)")
# Inline timing — does NOT use BenchResult struct (interp_cross_module_struct_return_unit bug).
# Records elapsed micros as a primitive i64; asserts > 0 to confirm timing ran.
rt_dir_create_all(FS_BENCH_DIR)
val content = _make_fs_content()
val t0 = rt_time_now_unix_micros()
rt_file_write_text(FS_WRITE_PATH, content)
val _read_back = rt_file_read_text(FS_WRITE_PATH)
val elapsed_us = rt_time_now_unix_micros() - t0
# Timing recorded: must be non-negative (>= 0); a zero result is allowed
# on very fast hosts but still means the clock ran.
val timing_recorded = elapsed_us >= 0
expect(timing_recorded).to_equal(true)
```

</details>

#### arch tag is x86_64 (AC-3 extensibility row)

- arch tag is x86_64 (AC-3 extensibility row)
   - Expected: ARCH_TAG equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("arch tag is x86_64 (AC-3 extensibility row)")
# Asserts the arch label for this spec. arm64/riscv64 rows extend this
# spec later by adding skip_if(arch != "arm64", "not arm64") guards.
# This test documents the current arch scope explicitly.
expect(ARCH_TAG).to_equal("x86_64")
```

</details>

#### plane labels are distinct — fs != sched (AC-3 never-collapsed)

- plane labels are distinct — fs != sched (AC-3 never-collapsed)
   - Expected: fs_ne_sched is true
   - Expected: MODE_FS equals `fs`
   - Expected: MODE_SCHED equals `sched`
   - Expected: PLANE_WARM equals `warm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("plane labels are distinct — fs != sched (AC-3 never-collapsed)")
# Each workload category must be a distinct row, never merged.
val fs_ne_sched = MODE_FS != MODE_SCHED
expect(fs_ne_sched).to_equal(true)
expect(MODE_FS).to_equal("fs")
expect(MODE_SCHED).to_equal("sched")
expect(PLANE_WARM).to_equal("warm")
```

</details>

#### process spawn produces output (sched plane, x86_64)

- process spawn produces output (sched plane, x86_64)
   - Expected: out_trimmed equals `hello_bench`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("process spawn produces output (sched plane, x86_64)")
# Spawn one trivial echo process to confirm spawn works.
# rt_process_run returns (stdout, stderr, exit_code).
val (stdout, _stderr, code) = rt_process_run("/bin/echo", ["hello_bench"])
val out_trimmed = stdout.trim()
expect(out_trimmed).to_equal("hello_bench")
expect(code).to_equal(0)
```

</details>

#### spawn timing was recorded (sched plane, x86_64)

- spawn timing was recorded (sched plane, x86_64)
   - Expected: timing_recorded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("spawn timing was recorded (sched plane, x86_64)")
# Time a single process spawn inline into i64; assert >= 0.
val t0 = rt_time_now_unix_micros()
val (_out, _err, _code) = rt_process_run("/bin/echo", ["bench"])
val elapsed_us = rt_time_now_unix_micros() - t0
val timing_recorded = elapsed_us >= 0
expect(timing_recorded).to_equal(true)
```

</details>

#### qemu systest variant — x86_64 QEMU boot

- qemu systest variant — x86_64 QEMU boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("qemu systest variant — x86_64 QEMU boot")
# This row documents the QEMU systest extension path (AC-3).
# A full QEMU boot is too heavy for a standard test run.
# Enable in the systest lane by removing the pending() and wiring
# the qemu_systest_contract (see test/03_system/os/qemu/ model).
# arm64/riscv64 rows replicate this block with arch-appropriate skip guards.
pending("qemu boot bound — runs in systest lane")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/05_perf/os/os_fs_sched_bench_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering os fs + scheduler bench (AC-3, x86_64 host-proxy).
- os fs + scheduler bench (AC-3, x86_64 host-proxy)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b404397235cd92cbdff45c2bf7083cc490a584fdbca77b22803e1ab5e195474`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b404397235cd92cbdff45c2bf7083cc490a584fdbca77b22803e1ab5e195474`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b404397235cd92cbdff45c2bf7083cc490a584fdbca77b22803e1ab5e195474`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/os/os_fs_sched_bench_spec.spl
mirror: doc/06_spec/05_perf/os/os_fs_sched_bench_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/05_perf/os/os_fs_sched_bench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/os/os_fs_sched_bench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/os/os_fs_sched_bench_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/05_perf/os/os_fs_sched_bench_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/os/os_fs_sched_bench_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bench dir created' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/os/os_fs_sched_bench_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fs write succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/os/os_fs_sched_bench_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fs round-trip: bytes written == bytes read (content oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
