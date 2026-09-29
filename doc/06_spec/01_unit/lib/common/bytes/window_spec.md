# Window Specification

> Tests covering RingWindow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Specification

## Scenarios

### RingWindow

#### at_distance recovers recently pushed bytes (d=1 is most recent)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- at_distance recovers recently pushed bytes (d=1 is most recent)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("at_distance recovers recently pushed bytes (d=1 is most recent)")
var w = RingWindow.new(8)
w.push(11u8)
w.push(22u8)
w.push(33u8)
assert_equal(w.at_distance(1).to_i64(), 33)
assert_equal(w.at_distance(2).to_i64(), 22)
assert_equal(w.at_distance(3).to_i64(), 11)
```

</details>

#### fails closed on distance beyond filled size

- fails closed on distance beyond filled size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on distance beyond filled size")
var w = RingWindow.new(8)
w.push(5u8)
assert_equal(w.at_distance(2).to_i64(), 0)
assert_equal(w.at_distance(0).to_i64(), 0)
```

</details>

#### evicts oldest beyond capacity (wraparound invariant)

- evicts oldest beyond capacity (wraparound invariant)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evicts oldest beyond capacity (wraparound invariant)")
var w = RingWindow.new(3)
w.push(1u8)
w.push(2u8)
w.push(3u8)
w.push(4u8)
assert_equal(w.size(), 3)
assert_equal(w.at_distance(1).to_i64(), 4)
assert_equal(w.at_distance(3).to_i64(), 2)
assert_equal(w.at_distance(4).to_i64(), 0)
```

</details>

#### match_len finds the longest match against a span

- match_len finds the longest match against a span


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match_len finds the longest match against a span")
var w = RingWindow.new(16)
w.push(65u8)
w.push(66u8)
w.push(67u8)
# history (most recent first) is C,B,A. A span A,B,C matches all 3.
val probe: [u8] = [65u8, 66u8, 67u8]
assert_equal(w.match_len(ByteSpan.new(probe), 0), 3)
```

</details>

#### match_len fails closed on negative span offset

- match_len fails closed on negative span offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match_len fails closed on negative span offset")
var w = RingWindow.new(16)
w.push(65u8)
val probe: [u8] = [65u8]
assert_equal(w.match_len(ByteSpan.new(probe), -1), 0)
```

</details>

#### match_len fails closed on offset at span end

- match_len fails closed on offset at span end


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match_len fails closed on offset at span end")
var w = RingWindow.new(16)
w.push(65u8)
val probe: [u8] = [65u8]
assert_equal(w.match_len(ByteSpan.new(probe), 1), 0)
```

</details>

#### copy_match performs an overlapping LZ77 run-length copy

- copy_match performs an overlapping LZ77 run-length copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copy_match performs an overlapping LZ77 run-length copy")
var w = RingWindow.new(16)
w.push(97u8)            # 'a'
# distance 1, length 4 -> repeat 'a' four times
w.copy_match(1, 4)
assert_equal(w.size(), 5)
assert_equal(w.at_distance(1).to_i64(), 97)
assert_equal(w.at_distance(5).to_i64(), 97)
```

</details>

#### copy_match with distance 2 repeats a two-byte pattern

- copy_match with distance 2 repeats a two-byte pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copy_match with distance 2 repeats a two-byte pattern")
var w = RingWindow.new(16)
w.push(1u8)
w.push(2u8)
w.copy_match(2, 4)      # repeats 1,2,1,2
assert_equal(w.at_distance(4).to_i64(), 1)
assert_equal(w.at_distance(3).to_i64(), 2)
assert_equal(w.at_distance(2).to_i64(), 1)
assert_equal(w.at_distance(1).to_i64(), 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/window_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RingWindow.
- RingWindow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `88a1023e0ef00dba7eaebb91d7f23366cd8935383eabe760101733a331604173`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88a1023e0ef00dba7eaebb91d7f23366cd8935383eabe760101733a331604173`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88a1023e0ef00dba7eaebb91d7f23366cd8935383eabe760101733a331604173`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/bytes/window_spec.spl
mirror: doc/06_spec/01_unit/lib/common/bytes/window_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/bytes/window_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/bytes/window_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/bytes/window_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'at_distance recovers recently pushed bytes (d=1 is most recent)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bytes/window_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on distance beyond filled size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bytes/window_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evicts oldest beyond capacity (wraparound invariant)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
