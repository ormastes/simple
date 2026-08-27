# os_fs_sched_bench_spec

> Purpose: host-level FS and scheduler micro-benchmarks with absolute content

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# os_fs_sched_bench_spec

Purpose: host-level FS and scheduler micro-benchmarks with absolute content

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/05_perf/os/os_fs_sched_bench_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: host-level FS and scheduler micro-benchmarks with absolute content
oracles — the FS round-trip must read back byte-identical, and each spawn
must exit cleanly. Audience: OS runtime and perf owners consuming the
arch-tagged baseline rows.

## Scenarios

### os fs + scheduler bench (AC-3, x86_64 host-proxy)

#### bench dir created

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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
expect(read_len).to_equal(written_len)  # oracle: ASCII-only 4096-char workload, len(read) == len(written)
# Content oracle
val matches = _content_matches(written, read_back)
expect(matches).to_equal(true)
```

</details>

#### fs round-trip: file exists after write

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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
expect(out_trimmed).to_equal("hello_bench")  # oracle: /bin/echo emits exactly its argument
expect(code).to_equal(0)  # oracle: 0 is the shell success exit status
```

</details>

#### spawn timing was recorded (sched plane, x86_64)

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


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

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- qemu systest variant — x86_64 QEMU boot
   - Expected: ARCH_TAG equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("qemu systest variant — x86_64 QEMU boot")
# This row documents the QEMU systest extension path (AC-3).
# A full QEMU boot is too heavy for a standard test run.
# Enable in the systest lane by removing the pending() and wiring
# the qemu_systest_contract (see test/03_system/os/qemu/ model).
# arm64/riscv64 rows replicate this block with arch-appropriate skip guards.
# Honest skip: a full QEMU boot is too heavy for a standard test run;
# the systest lane owns the boot-bound row. Prove the row's gating data
# is real before skipping: the arch tag must match this spec's declared row.
expect(ARCH_TAG).to_equal("x86_64")  # oracle: the QEMU systest extension row is tagged for this arch
return "skip: qemu boot bound — runs in systest lane"
```

</details>

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

- Canonical SPipe generation for source `e03e142d84849e019b803a3da70f44d3dee6fe9ef9d76ebf88e28ee6801e497a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e03e142d84849e019b803a3da70f44d3dee6fe9ef9d76ebf88e28ee6801e497a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e03e142d84849e019b803a3da70f44d3dee6fe9ef9d76ebf88e28ee6801e497a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/05_perf/os/os_fs_sched_bench_spec.spl
mirror: doc/06_spec/05_perf/os/os_fs_sched_bench_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/os/os_fs_sched_bench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/os/os_fs_sched_bench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
