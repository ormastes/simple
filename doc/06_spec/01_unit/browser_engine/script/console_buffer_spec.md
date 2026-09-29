# ConsoleBuffer Specification

> Tests for `ConsoleBuffer` in `src/lib/gc_async_mut/gpu/browser_engine/script/console_buffer.spl` (REQ-5 / AC-4). All specs FAIL until that module is implemented.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ConsoleBuffer Specification

Tests for `ConsoleBuffer` in `src/lib/gc_async_mut/gpu/browser_engine/script/console_buffer.spl` (REQ-5 / AC-4). All specs FAIL until that module is implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-CONSOLE-BUFFER |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/browser_engine/script/console_buffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `ConsoleBuffer` in
`src/lib/gc_async_mut/gpu/browser_engine/script/console_buffer.spl` (REQ-5 / AC-4).
All specs FAIL until that module is implemented.

## Key Behaviors

- `ConsoleBuffer.new()` creates an empty buffer.
- `append(level, message, now_micros)` adds a `ConsoleEntry`.
- `entries()` returns all appended entries in insertion order.
- `clear()` empties the buffer.
- Buffer is bounded at 512 entries; on overflow the oldest entry is
  overwritten (ring semantics).

## Scenarios

### ConsoleBuffer

### AC-4: creation

#### AC-4: new buffer starts with zero entries

- AC-4: new buffer starts with zero entries
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: new buffer starts with zero entries")
val buf = _make_empty_buffer()
val count = _entry_count(buf)
expect(count).to_equal(0)
```

</details>

### AC-4: append and read

#### AC-4: appended log message is stored in entries

- AC-4: appended log message is stored in entries
   - Expected: msg equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: appended log message is stored in entries")
val buf = _buffer_with_one_log()
val msg = _first_entry_message(buf)
expect(msg).to_equal("hello world")
```

</details>

#### AC-4: appended level is stored in entries

- AC-4: appended level is stored in entries
   - Expected: lvl equals `log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: appended level is stored in entries")
val buf = _buffer_with_one_log()
val lvl = _first_entry_level(buf)
expect(lvl).to_equal("log")
```

</details>

#### AC-4: entries count grows with each append

- AC-4: entries count grows with each append
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: entries count grows with each append")
val buf = _buffer_with_three_levels()
val count = _entry_count(buf)
expect(count).to_equal(3)
```

</details>

#### AC-4: entries are in insertion order — first is log level

- AC-4: entries are in insertion order — first is log level
   - Expected: entries[0].level equals `log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: entries are in insertion order — first is log level")
val buf = _buffer_with_three_levels()
val entries = buf.entries()
expect(entries[0].level).to_equal("log")
```

</details>

#### AC-4: entries are in insertion order — second is warn level

- AC-4: entries are in insertion order — second is warn level
   - Expected: entries[1].level equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: entries are in insertion order — second is warn level")
val buf = _buffer_with_three_levels()
val entries = buf.entries()
expect(entries[1].level).to_equal("warn")
```

</details>

#### AC-4: entries are in insertion order — third is error level

- AC-4: entries are in insertion order — third is error level
   - Expected: entries[2].level equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: entries are in insertion order — third is error level")
val buf = _buffer_with_three_levels()
val entries = buf.entries()
expect(entries[2].level).to_equal("error")
```

</details>

#### AC-4: timestamp_micros is stored in entry

- AC-4: timestamp_micros is stored in entry
   - Expected: entries[0].timestamp_micros equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: timestamp_micros is stored in entry")
val buf = _buffer_with_one_log()
val entries = buf.entries()
expect(entries[0].timestamp_micros).to_equal(1000)
```

</details>

### AC-4: clear

#### AC-4: clear removes all entries

- AC-4: clear removes all entries
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: clear removes all entries")
var buf = _buffer_with_three_levels()
buf.clear()
val count = _entry_count(buf)
expect(count).to_equal(0)
```

</details>

### AC-4: ring overflow at 512

#### AC-4: buffer accepts exactly 512 entries without loss

- AC-4: buffer accepts exactly 512 entries without loss
   - Expected: count equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: buffer accepts exactly 512 entries without loss")
val buf = _buffer_filled_to(512)
val count = _entry_count(buf)
expect(count).to_equal(512)
```

</details>

#### AC-4: buffer stays at 512 entries after 513th append

- AC-4: buffer stays at 512 entries after 513th append
   - Expected: count equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-4: buffer stays at 512 entries after 513th append")
val buf = _buffer_filled_to(513)
val count = _entry_count(buf)
expect(count).to_equal(512)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0401a36abdfc64c1941198d029bf917100448b39cd7385a435fcfc55e5cdefc9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0401a36abdfc64c1941198d029bf917100448b39cd7385a435fcfc55e5cdefc9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0401a36abdfc64c1941198d029bf917100448b39cd7385a435fcfc55e5cdefc9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/script/console_buffer_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/script/console_buffer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/script/console_buffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/script/console_buffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/script/console_buffer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/script/console_buffer_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: new buffer starts with zero entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/console_buffer_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: appended log message is stored in entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/console_buffer_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: appended level is stored in entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
