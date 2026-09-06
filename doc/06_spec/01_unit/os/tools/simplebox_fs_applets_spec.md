# Simplebox Fs Applets Specification

> Tests covering streaming simplebox filesystem applet cores.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simplebox Fs Applets Specification

## Scenarios

### streaming simplebox filesystem applet cores

#### carries a word across chunk boundaries without double counting

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries a word across chunk boundaries without double counting
   - Expected: final.lines equals `1`
   - Expected: final.words equals `2`
   - Expected: final.bytes equals `8`
   - Expected: final.in_word is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("carries a word across chunk boundaries without double counting")
val first = simplebox_count_bytes(empty_count(), [97u8, 108u8, 112u8])
val final = simplebox_count_bytes(first, [104u8, 97u8, 32u8, 98u8, 10u8])
expect(final.lines).to_equal(1)
expect(final.words).to_equal(2)
expect(final.bytes).to_equal(8)
expect(final.in_word).to_equal(false)
```

</details>

#### uses byte semantics for invalid UTF-8 and all POSIX whitespace

- uses byte semantics for invalid UTF-8 and all POSIX whitespace
   - Expected: count.lines equals `1`
   - Expected: count.words equals `3`
   - Expected: count.bytes equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses byte semantics for invalid UTF-8 and all POSIX whitespace")
val count = simplebox_count_bytes(empty_count(),
    [255u8, 11u8, 254u8, 12u8, 253u8, 13u8, 10u8])
expect(count.lines).to_equal(1)
expect(count.words).to_equal(3)
expect(count.bytes).to_equal(7)
```

</details>

#### returns only the prefix through the requested newline

- returns only the prefix through the requested newline
   - Expected: prefix equals `4`
   - Expected: remaining equals `0`
   - Expected: reached is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns only the prefix through the requested newline")
val (prefix, remaining, reached) =
    simplebox_head_prefix_bytes([97u8, 10u8, 98u8, 10u8, 99u8], 2)
expect(prefix).to_equal(4)
expect(remaining).to_equal(0)
expect(reached).to_equal(true)
```

</details>

#### carries the remaining line count into the next chunk

- carries the remaining line count into the next chunk
   - Expected: prefix equals `3`
   - Expected: remaining equals `2`
   - Expected: reached is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("carries the remaining line count into the next chunk")
val (prefix, remaining, reached) =
    simplebox_head_prefix_bytes([97u8, 10u8, 98u8], 3)
expect(prefix).to_equal(3)
expect(remaining).to_equal(2)
expect(reached).to_equal(false)
```

</details>

#### writes nothing and requests no next chunk at zero lines

- writes nothing and requests no next chunk at zero lines
   - Expected: prefix equals `0`
   - Expected: remaining equals `0`
   - Expected: reached is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("writes nothing and requests no next chunk at zero lines")
val (prefix, remaining, reached) = simplebox_head_prefix_bytes([97u8], 0)
expect(prefix).to_equal(0)
expect(remaining).to_equal(0)
expect(reached).to_equal(true)
```

</details>

#### keeps file count byte count and reads explicitly bounded

- keeps file count byte count and reads explicitly bounded
   - Expected: SIMPLEBOX_FILE_LIMIT equals `128`
   - Expected: SIMPLEBOX_FILE_BYTES_LIMIT equals `67108864`
   - Expected: SIMPLEBOX_READ_CHUNK_BYTES equals `65536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps file count byte count and reads explicitly bounded")
expect(SIMPLEBOX_FILE_LIMIT).to_equal(128)
expect(SIMPLEBOX_FILE_BYTES_LIMIT).to_equal(67108864)
expect(SIMPLEBOX_READ_CHUNK_BYTES).to_equal(65536)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tools/simplebox_fs_applets_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering streaming simplebox filesystem applet cores.
- streaming simplebox filesystem applet cores

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46cdf3f100a07808c328630fe81bfb249d04312b5045c25b5b147e594dd09dc0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46cdf3f100a07808c328630fe81bfb249d04312b5045c25b5b147e594dd09dc0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46cdf3f100a07808c328630fe81bfb249d04312b5045c25b5b147e594dd09dc0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/tools/simplebox_fs_applets_spec.spl
mirror: doc/06_spec/01_unit/os/tools/simplebox_fs_applets_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tools/simplebox_fs_applets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tools/simplebox_fs_applets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tools/simplebox_fs_applets_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tools/simplebox_fs_applets_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries a word across chunk boundaries without double counting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_fs_applets_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses byte semantics for invalid UTF-8 and all POSIX whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_fs_applets_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns only the prefix through the requested newline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
