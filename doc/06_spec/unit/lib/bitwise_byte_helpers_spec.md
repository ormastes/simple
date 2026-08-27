# bitwise_byte_helpers_spec

> B4 (compiler_bugs_for_crypto_2026-04-25.md) — bitfield helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bitwise_byte_helpers_spec

B4 (compiler_bugs_for_crypto_2026-04-25.md) — bitfield helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/bitwise_byte_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

B4 (compiler_bugs_for_crypto_2026-04-25.md) — bitfield helpers.

The plan's "do this regardless" part: byte/bit slice helpers in stdlib
that crypto-port code can call directly instead of writing
shift-and-mask by hand. These already exist in bitwise_utils.spl —
this spec is the regression guard for the get/set/extract/insert
round-trips that B4's acceptance covers (slice get, slice set,
multi-slice set, aliasing).

The full `int.bits[lo..hi]` syntax sugar is deferred (separate task
B4-sugar — needs parser + HIR variant; helpers cover the semantics).

## Scenarios

### byte helpers (B4)

#### get_byte extracts each byte position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- get_byte extracts each byte position
   - Expected: get_byte(n, 0) equals `0xEF`
   - Expected: get_byte(n, 1) equals `0xCD`
   - Expected: get_byte(n, 2) equals `0xAB`
   - Expected: get_byte(n, 3) equals `0x90`
   - Expected: get_byte(n, 4) equals `0x78`
   - Expected: get_byte(n, 5) equals `0x56`
   - Expected: get_byte(n, 6) equals `0x34`
   - Expected: get_byte(n, 7) equals `0x12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_byte extracts each byte position")
val n = 0x1234567890ABCDEF
expect(get_byte(n, 0)).to_equal(0xEF)
expect(get_byte(n, 1)).to_equal(0xCD)
expect(get_byte(n, 2)).to_equal(0xAB)
expect(get_byte(n, 3)).to_equal(0x90)
expect(get_byte(n, 4)).to_equal(0x78)
expect(get_byte(n, 5)).to_equal(0x56)
expect(get_byte(n, 6)).to_equal(0x34)
expect(get_byte(n, 7)).to_equal(0x12)
```

</details>

#### set_byte writes each byte position

- set_byte writes each byte position
   - Expected: set_byte(n, 0, 0xAB) equals `0xAB`
   - Expected: set_byte(n, 1, 0xAB) equals `0xAB00`
   - Expected: set_byte(n, 3, 0xAB) equals `0xAB000000`
   - Expected: set_byte(n, 7, 0xAB) equals `0xAB00000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_byte writes each byte position")
val n = 0x0
expect(set_byte(n, 0, 0xAB)).to_equal(0xAB)
expect(set_byte(n, 1, 0xAB)).to_equal(0xAB00)
expect(set_byte(n, 3, 0xAB)).to_equal(0xAB000000)
expect(set_byte(n, 7, 0xAB)).to_equal(0xAB00000000000000)
```

</details>

#### set_byte clears the existing byte before writing

- set_byte clears the existing byte before writing
   - Expected: set_byte(n, 0, 0x12) equals `0x12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_byte clears the existing byte before writing")
val n = 0xFF
expect(set_byte(n, 0, 0x12)).to_equal(0x12)
```

</details>

#### get/set round-trips for every byte position

- get/set round-trips for every byte position
   - Expected: updated equals `n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get/set round-trips for every byte position")
val n = 0x1234567890ABCDEF
var i = 0
while i < 8:
    val b = get_byte(n, i)
    val updated = set_byte(n, i, b)
    expect(updated).to_equal(n)
    i = i + 1
```

</details>

### bit slice helpers (B4)

#### extract_bits matches plan example

- extract_bits matches plan example
   - Expected: extract_bits(0b11010110, 2, 3) equals `0b101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_bits matches plan example")
# extract_bits(0b11010110, 2, 3) -> 0b101
expect(extract_bits(0b11010110, 2, 3)).to_equal(0b101)
```

</details>

#### insert_bits matches plan example

- insert_bits matches plan example
   - Expected: insert_bits(0b11110000, 0b101, 2, 3) equals `0b11110100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insert_bits matches plan example")
# insert_bits(0b11110000, 0b101, 2, 3) -> 0b11110100
expect(insert_bits(0b11110000, 0b101, 2, 3)).to_equal(0b11110100)
```

</details>

#### extract/insert round-trip preserves the field

- extract/insert round-trip preserves the field
   - Expected: rewritten equals `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract/insert round-trip preserves the field")
val target = 0xDEAD_BEEF
val v = extract_bits(target, 8, 8)   # second-lowest byte
val rewritten = insert_bits(target, v, 8, 8)
expect(rewritten).to_equal(target)
```

</details>

#### multi-slice insert composes (independent fields, no aliasing)

- multi-slice insert composes (independent fields, no aliasing)
   - Expected: with_hi equals `0xCDAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-slice insert composes (independent fields, no aliasing)")
val base = 0
val with_lo = insert_bits(base, 0xAB, 0, 8)
val with_hi = insert_bits(with_lo, 0xCD, 8, 8)
expect(with_hi).to_equal(0xCDAB)
```

</details>

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

- Canonical SPipe generation for source `fef66ab301fc75282160a4e90e8ed30aeab5a0bada84b19d5b633ab78c107e2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fef66ab301fc75282160a4e90e8ed30aeab5a0bada84b19d5b633ab78c107e2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fef66ab301fc75282160a4e90e8ed30aeab5a0bada84b19d5b633ab78c107e2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/bitwise_byte_helpers_spec.spl
mirror: doc/06_spec/unit/lib/bitwise_byte_helpers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/bitwise_byte_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/bitwise_byte_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/bitwise_byte_helpers_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_byte extracts each byte position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/bitwise_byte_helpers_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set_byte writes each byte position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/bitwise_byte_helpers_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set_byte clears the existing byte before writing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
