# Non Optional Nil Return Contract Specification

> Tests covering non-optional return contract — stdlib wrappers stay total, non-optional return contract — nogc_sync_mut nil-forwarding wrappers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Non Optional Nil Return Contract Specification

## Scenarios

### non-optional return contract — stdlib wrappers stay total

#### file_read_lines on an unreadable path returns Err

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- file_read_lines on an unreadable path returns Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_read_lines on an unreadable path returns Err")
assert_true(file_read_lines("/nonexistent/definitely/not/here.txt").is_err())
```

</details>

#### file_read_lines on a directory path returns Err

- file_read_lines on a directory path returns Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_read_lines on a directory path returns Err")
assert_true(file_read_lines("/").is_err())
```

</details>

#### channel try_recv on an empty channel returns nil through an optional

- channel try_recv on an empty channel returns nil through an optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel try_recv on an empty channel returns nil through an optional")
# rt_channel_try_recv returns nil when no value is queued; try_recv is
# declared `-> Any?` so the nil is contract-valid rather than fatal.
val ch = channel_new()
assert_true(ch.try_recv() == nil)
```

</details>

#### channel try_recv by id on an empty channel returns nil

- channel try_recv by id on an empty channel returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel try_recv by id on an empty channel returns nil")
val id = channel_new_id()
assert_true(channel_try_recv_by_id(id) == nil)
```

</details>

#### channel try_recv still delivers a sent value after a nil poll

- channel try_recv still delivers a sent value after a nil poll


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel try_recv still delivers a sent value after a nil poll")
val ch = channel_new()
assert_true(ch.try_recv() == nil)
ch.send(7)
assert_equal(ch.try_recv() ?? 0, 7)
```

</details>

### non-optional return contract — nogc_sync_mut nil-forwarding wrappers

#### file_mmap_read_bytes on an unreadable path returns Err

- file_mmap_read_bytes on an unreadable path returns Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_mmap_read_bytes on an unreadable path returns Err")
assert_true(mmap_bytes("/nonexistent/definitely/not/here.bin").is_err())
```

</details>

#### env_get on an unset variable yields \

- env_get on an unset variable yields \


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get on an unset variable yields \")
assert_equal(env_ops_env_get("SIMPLE_CONTRACT_PROBE_DEFINITELY_UNSET"), "")
```

</details>

#### home() is total even when HOME lookup yields nil

- home() is total even when HOME lookup yields nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("home() is total even when HOME lookup yields nil")
# `-> text`; documented default "" rather than nil.
assert_true(env_ops_home().len() >= 0)
```

</details>

#### io_runtime home() and platform_name() are total

- io_runtime home() and platform_name() are total


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("io_runtime home() and platform_name() are total")
assert_true(io_home().len() >= 0)
assert_true(io_platform_name().len() > 0)
```

</details>

#### cwd() is total with the documented \

- cwd() is total with the documented \


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cwd() is total with the documented \")
assert_true(sys_cwd().len() > 0)
```

</details>

#### args_get() is total with the documented [] default

- args_get() is total with the documented [] default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("args_get() is total with the documented [] default")
assert_true(sys_args_get().len() >= 0)
```

</details>

#### simd profile_name() is total and never a fabricated tier

- simd profile_name() is total and never a fabricated tier


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simd profile_name() is total and never a fabricated tier")
assert_true(simd_profile_name().len() > 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering non-optional return contract — stdlib wrappers stay total, non-optional return contract — nogc_sync_mut nil-forwarding wrappers.
- non-optional return contract — stdlib wrappers stay total
- non-optional return contract — nogc_sync_mut nil-forwarding wrappers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `cea41baa8a2545db646dcdcd7913165e185f243b8aa54357910f53a428f46c00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cea41baa8a2545db646dcdcd7913165e185f243b8aa54357910f53a428f46c00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cea41baa8a2545db646dcdcd7913165e185f243b8aa54357910f53a428f46c00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_read_lines on an unreadable path returns Err' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_read_lines on a directory path returns Err' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'channel try_recv on an empty channel returns nil through an optional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
