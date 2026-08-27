# Runtime Timestamp Owner Source Specification

> Tests covering hosted timestamp provider ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Timestamp Owner Source Specification

## Scenarios

### hosted timestamp provider ownership

#### records and subtracts the Windows progress reset epoch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records and subtracts the Windows progress reset epoch
   - Expected: source.split("g_progress_start_nanos = rt_time_now_nanos();").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records and subtracts the Windows progress reset epoch")
val source = rt_file_read_text("src/runtime/runtime_timestamp.c") ?? ""
expect(source).to_contain("static int64_t g_progress_start_nanos = 0;")
expect(source.split("g_progress_start_nanos = rt_time_now_nanos();").len() - 1).to_equal(2)
expect(source).to_contain("int64_t elapsed_nanos = rt_time_now_nanos() - g_progress_start_nanos;")
expect(source).to_contain("if (elapsed_nanos <= 0) return 0.0;")
expect(source).to_contain("return (double)elapsed_nanos / 1000000000.0;")
expect(source.contains("return (double)rt_time_now_nanos() / 1000000000.0;")).to_be(false)
```

</details>

#### uses a floor-day remainder for negative sub-second timestamps

- uses a floor-day remainder for negative sub-second timestamps
   - Expected: rt_timestamp_get_hour(-1) equals `23`
   - Expected: rt_timestamp_get_minute(-1) equals `59`
   - Expected: rt_timestamp_get_second(-1) equals `59`
   - Expected: rt_timestamp_get_microsecond(-1) equals `999999`
   - Expected: rt_timestamp_get_hour(0) equals `0`
   - Expected: rt_timestamp_get_microsecond(1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses a floor-day remainder for negative sub-second timestamps")
expect(rt_timestamp_get_hour(-1)).to_equal(23)
expect(rt_timestamp_get_minute(-1)).to_equal(59)
expect(rt_timestamp_get_second(-1)).to_equal(59)
expect(rt_timestamp_get_microsecond(-1)).to_equal(999999)
expect(rt_timestamp_get_hour(0)).to_equal(0)
expect(rt_timestamp_get_microsecond(1)).to_equal(1)
```

</details>

#### keeps the bootstrap SFFI timestamp owner floor-based

- keeps the bootstrap SFFI timestamp owner floor-based
   - Expected: compiler_gen.split("micros.div_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: compiler_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: app_gen.split("micros.div_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: app_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1 equals `3`
   - Expected: app_time equals `lib_time`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the bootstrap SFFI timestamp owner floor-based")
val source = rt_file_read_text("src/app/sffi_gen.templates/bootstrap_sffi.txt") ?? ""
expect(source).to_contain("micros.div_euclid(86_400_000_000)")
expect(source).to_contain("micros.rem_euclid(86_400_000_000)")
expect(source.contains("let secs = micros / 1_000_000")).to_be(false)

val compiler_gen = rt_file_read_text("src/compiler/90.tools/sffi_gen/specs/time_mod.spl") ?? ""
val app_gen = rt_file_read_text("src/app/ffi_gen.specs/time_mod.spl") ?? ""
expect(compiler_gen.split("micros.div_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(compiler_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(app_gen.split("micros.div_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(app_gen.split("micros.rem_euclid(86_400_000_000)").len() - 1).to_equal(3)
expect(compiler_gen.contains("chrono::")).to_be(false)
expect(app_gen.contains("chrono::")).to_be(false)

val workspace_gen = rt_file_read_text("src/compiler/90.tools/sffi_gen/sffi_gen_workspace.spl") ?? ""
expect(workspace_gen.contains("chrono = ")).to_be(false)

val app_time = rt_file_read_text("src/app/io/time_ops.spl") ?? ""
val lib_time = rt_file_read_text("src/lib/nogc_sync_mut/io/time_ops.spl") ?? ""
expect(app_time).to_equal(lib_time)
expect(app_time).to_contain("use common.time_utils.{timestamp_get_year")
expect(app_time.contains("val _ = micros")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted timestamp provider ownership.
- hosted timestamp provider ownership

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b0e70cffe3812f008f5adf55059e8fb6f08562fe18163cb9538573c37534273`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b0e70cffe3812f008f5adf55059e8fb6f08562fe18163cb9538573c37534273`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b0e70cffe3812f008f5adf55059e8fb6f08562fe18163cb9538573c37534273`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records and subtracts the Windows progress reset epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a floor-day remainder for negative sub-second timestamps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/runtime_timestamp_owner_source_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the bootstrap SFFI timestamp owner floor-based' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
