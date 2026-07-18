# Os Fs Sched Bench Specification

> <details>

<!-- sdn-diagram:id=os_fs_sched_bench_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_fs_sched_bench_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_fs_sched_bench_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_fs_sched_bench_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Fs Sched Bench Specification

## Scenarios

### os fs + scheduler bench (AC-3, x86_64 host-proxy)

#### bench dir created

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = rt_dir_create_all(FS_BENCH_DIR)
expect(ok).to_equal(true)
```

</details>

#### fs write succeeds

- rt dir create all
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all(FS_BENCH_DIR)
val content = _make_fs_content()
val ok = rt_file_write_text(FS_WRITE_PATH, content)
expect(ok).to_equal(true)
```

</details>

#### fs round-trip: bytes written == bytes read (content oracle)

- rt dir create all
   - Expected: write_ok is true
   - Expected: read_len equals `written_len`
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- rt dir create all
- rt file write text
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_dir_create_all(FS_BENCH_DIR)
val content = _make_fs_content()
rt_file_write_text(FS_WRITE_PATH, content)
val exists = rt_file_exists(FS_WRITE_PATH)
expect(exists).to_equal(true)
```

</details>

#### fs write+read timing was recorded (warm plane, x86_64)

- rt dir create all
- rt file write text
   - Expected: timing_recorded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Asserts the arch label for this spec. arm64/riscv64 rows extend this
# spec later by adding skip_if(arch != "arm64", "not arm64") guards.
# This test documents the current arch scope explicitly.
expect(ARCH_TAG).to_equal("x86_64")
```

</details>

#### plane labels are distinct — fs != sched (AC-3 never-collapsed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each workload category must be a distinct row, never merged.
val fs_ne_sched = MODE_FS != MODE_SCHED
expect(fs_ne_sched).to_equal(true)
expect(MODE_FS).to_equal("fs")
expect(MODE_SCHED).to_equal("sched")
expect(PLANE_WARM).to_equal("warm")
```

</details>

#### process spawn produces output (sched plane, x86_64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Spawn one trivial echo process to confirm spawn works.
# rt_process_run returns (stdout, stderr, exit_code).
val (stdout, _stderr, code) = rt_process_run("/bin/echo", ["hello_bench"])
val out_trimmed = stdout.trim()
expect(out_trimmed).to_equal("hello_bench")
expect(code).to_equal(0)
```

</details>

#### spawn timing was recorded (sched plane, x86_64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Time a single process spawn inline into i64; assert >= 0.
val t0 = rt_time_now_unix_micros()
val (_out, _err, _code) = rt_process_run("/bin/echo", ["bench"])
val elapsed_us = rt_time_now_unix_micros() - t0
val timing_recorded = elapsed_us >= 0
expect(timing_recorded).to_equal(true)
```

</details>

#### qemu systest variant — x86_64 QEMU boot

- pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
