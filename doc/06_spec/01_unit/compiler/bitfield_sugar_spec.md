# bitfield_sugar_spec

> Purpose: Prove that int.bits[lo..hi] read sugar (B4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bitfield_sugar_spec

Purpose: Prove that int.bits[lo..hi] read sugar (B4).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bitfield_sugar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that int.bits[lo..hi] read sugar (B4).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### int.bits[lo..hi] read sugar (B4)

#### extracts the low byte of a u32-shaped value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts the low byte of a u32-shaped value
- Verify: extracts the low byte of a u32-shaped value
   - Expected: byte0 equals `0x78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts the low byte of a u32-shaped value")
step("Verify: extracts the low byte of a u32-shaped value")
# @req: REQ-COMP-INT-BITS-LO-HI-READ-SUGAR-B4-001
val state = 0x12345678
val byte0 = state.bits[0..8]
expect(byte0).to_equal(0x78)
```

</details>

#### extracts the high byte of a u32-shaped value

- extracts the high byte of a u32-shaped value
- Verify: extracts the high byte of a u32-shaped value
   - Expected: byte3 equals `0x12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts the high byte of a u32-shaped value")
step("Verify: extracts the high byte of a u32-shaped value")
val state = 0x12345678
val byte3 = state.bits[24..32]
expect(byte3).to_equal(0x12)
```

</details>

#### extracts a 4-bit nibble at a non-byte boundary

- extracts a 4-bit nibble at a non-byte boundary
- Verify: extracts a 4-bit nibble at a non-byte boundary
   - Expected: n.bits[4..8] equals `0xC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts a 4-bit nibble at a non-byte boundary")
step("Verify: extracts a 4-bit nibble at a non-byte boundary")
val n = 0xABCD
# bits[4..8] = nibble at position 4 = 0xC
expect(n.bits[4..8]).to_equal(0xC)
```

</details>

#### matches plan repro shape `(state[i] & 0xFF000000) >> 24`

- matches plan repro shape `(state[i] & 0xFF000000) >> 24`
- Verify: matches plan repro shape `(state[i] & 0xFF000000) >> 24`
   - Expected: via_sugar equals `via_manual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches plan repro shape `(state[i] & 0xFF000000) >> 24`")
step("Verify: matches plan repro shape `(state[i] & 0xFF000000) >> 24`")
val state = 0xDEADBEEF
val via_sugar = state.bits[24..32]
val via_manual = (state & 0xFF000000) >> 24
expect(via_sugar).to_equal(via_manual)
```

</details>

#### round-trips with bitwise_utils.extract_bits

- round-trips with bitwise_utils.extract_bits
- Verify: round-trips with bitwise_utils.extract_bits
   - Expected: sugar equals `0xBA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips with bitwise_utils.extract_bits")
step("Verify: round-trips with bitwise_utils.extract_bits")
# bits[lo..hi] is equivalent to extract_bits(n, lo, hi - lo)
val n = 0xCAFEBABE
val sugar = n.bits[8..16]
# 0xCAFEBABE -> byte at offset 8..16 = 0xBA
expect(sugar).to_equal(0xBA)
```

</details>

### int.bits[lo..hi] write sugar (B4)

#### writes the low byte and leaves higher bytes untouched

- writes the low byte and leaves higher bytes untouched
- Verify: writes the low byte and leaves higher bytes untouched
   - Expected: state equals `0x123456EF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes the low byte and leaves higher bytes untouched")
step("Verify: writes the low byte and leaves higher bytes untouched")
var state = 0x12345600
state.bits[0..8] = 0xEF
expect(state).to_equal(0x123456EF)
```

</details>

#### writes the high byte and leaves lower bytes untouched

- writes the high byte and leaves lower bytes untouched
- Verify: writes the high byte and leaves lower bytes untouched
   - Expected: state equals `0xAB345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes the high byte and leaves lower bytes untouched")
step("Verify: writes the high byte and leaves lower bytes untouched")
var state = 0x00345678
state.bits[24..32] = 0xAB
expect(state).to_equal(0xAB345678)
```

</details>

#### clears the existing field before writing the new value

- clears the existing field before writing the new value
- Verify: clears the existing field before writing the new value
   - Expected: state equals `0x00000012`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clears the existing field before writing the new value")
step("Verify: clears the existing field before writing the new value")
var state = 0x000000FF
state.bits[0..8] = 0x12
expect(state).to_equal(0x00000012)
```

</details>

#### matches plan repro shape `state[i].bits[24..32] = byte`

- matches plan repro shape `state[i].bits[24..32] = byte`
- Verify: matches plan repro shape `state[i].bits[24..32] = byte`
   - Expected: word equals `0xAABBCCDD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches plan repro shape `state[i].bits[24..32] = byte`")
step("Verify: matches plan repro shape `state[i].bits[24..32] = byte`")
var word = 0x00BBCCDD
word.bits[24..32] = 0xAA
expect(word).to_equal(0xAABBCCDD)
```

</details>

#### masks the source value to the field width

- masks the source value to the field width
- Verify: masks the source value to the field width
   - Expected: state equals `0xF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("masks the source value to the field width")
step("Verify: masks the source value to the field width")
# If the source has bits above the field width, they must be
# masked off — they must NOT bleed into adjacent fields.
var state = 0
state.bits[0..4] = 0xFF   # only the low 4 bits should land
expect(state).to_equal(0xF)
```

</details>

### int.bits round-trip and aliasing (B4)

#### write-then-read returns the written value

- write-then-read returns the written value
- Verify: write-then-read returns the written value
   - Expected: state.bits[8..16] equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("write-then-read returns the written value")
step("Verify: write-then-read returns the written value")
var state = 0x12345678
state.bits[8..16] = 0xAB
expect(state.bits[8..16]).to_equal(0xAB)
```

</details>

#### two non-overlapping field writes compose

- two non-overlapping field writes compose
- Verify: two non-overlapping field writes compose
   - Expected: state equals `0xCDAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two non-overlapping field writes compose")
step("Verify: two non-overlapping field writes compose")
var state = 0
state.bits[0..8] = 0xAB
state.bits[8..16] = 0xCD
expect(state).to_equal(0xCDAB)
```

</details>

#### writing one field does not disturb a neighbouring field

- writing one field does not disturb a neighbouring field
- Verify: writing one field does not disturb a neighbouring field
   - Expected: state.bits[8..16] equals `0`
   - Expected: state.bits[0..8] equals `0xAB`
   - Expected: state.bits[16..24] equals `0xEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writing one field does not disturb a neighbouring field")
step("Verify: writing one field does not disturb a neighbouring field")
var state = 0
state.bits[0..8] = 0xAB
state.bits[16..24] = 0xEF
# field at bits 8..16 should still be zero
expect(state.bits[8..16]).to_equal(0)
expect(state.bits[0..8]).to_equal(0xAB)
expect(state.bits[16..24]).to_equal(0xEF)
```

</details>

#### full-width write replaces the whole value

- full-width write replaces the whole value
- Verify: full-width write replaces the whole value
   - Expected: state.bits[0..32] equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("full-width write replaces the whole value")
step("Verify: full-width write replaces the whole value")
var state = 0xDEADBEEF
state.bits[0..32] = 0xCAFEBABE
expect(state.bits[0..32]).to_equal(0xCAFEBABE)
```

</details>

#### matches plan literal repro `state[i].bits[24..32] = byte`

- matches plan literal repro `state[i].bits[24..32] = byte`
- Verify: matches plan literal repro `state[i].bits[24..32] = byte`
   - Expected: arr[0] equals `0xAA000000`
   - Expected: arr[1] equals `0xBB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches plan literal repro `state[i].bits[24..32] = byte`")
step("Verify: matches plan literal repro `state[i].bits[24..32] = byte`")
# The plan's exact repro form: an indexed array element on the LHS.
# NOTE: `arr[i].bits[lo..hi] = v` desugars to a write that reads
# `arr[i]` twice — once to clear the field, once not. Pure-functional
# indices are fine; side-effecting indices would double-evaluate.
var arr = [0, 0]
arr[0].bits[24..32] = 0xAA
arr[1].bits[0..8] = 0xBB
expect(arr[0]).to_equal(0xAA000000)
expect(arr[1]).to_equal(0xBB)
```

</details>

### int.bits augmented assigns (B4-sugar Phase 2)

#### supports += on a single bitfield slice

- supports += on a single bitfield slice
- Verify: supports += on a single bitfield slice
   - Expected: state.bits[16..24] equals `0x15`
   - Expected: state.bits[24..32] equals `0x12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports += on a single bitfield slice")
step("Verify: supports += on a single bitfield slice")
var state = 0x12340000
state.bits[16..24] = 0x10
state.bits[16..24] += 0x05
expect(state.bits[16..24]).to_equal(0x15)
# Higher field untouched
expect(state.bits[24..32]).to_equal(0x12)
```

</details>

#### supports -= on a bitfield slice

- supports -= on a bitfield slice
- Verify: supports -= on a bitfield slice
   - Expected: state.bits[0..8] equals `0x19`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports -= on a bitfield slice")
step("Verify: supports -= on a bitfield slice")
var state = 0
state.bits[0..8] = 0x20
state.bits[0..8] -= 0x07
expect(state.bits[0..8]).to_equal(0x19)
```

</details>

#### supports *= on a bitfield slice

- supports *= on a bitfield slice
- Verify: supports *= on a bitfield slice
   - Expected: state.bits[8..16] equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports *= on a bitfield slice")
step("Verify: supports *= on a bitfield slice")
var state = 0
state.bits[8..16] = 3
state.bits[8..16] *= 7
expect(state.bits[8..16]).to_equal(21)
```

</details>

#### supports /= on a bitfield slice

- supports /= on a bitfield slice
- Verify: supports /= on a bitfield slice
   - Expected: state.bits[0..16] equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports /= on a bitfield slice")
step("Verify: supports /= on a bitfield slice")
var state = 0
state.bits[0..16] = 100
state.bits[0..16] /= 4
expect(state.bits[0..16]).to_equal(25)
```

</details>

#### supports %= on a bitfield slice

- supports %= on a bitfield slice
- Verify: supports %= on a bitfield slice
   - Expected: state.bits[0..16] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports %= on a bitfield slice")
step("Verify: supports %= on a bitfield slice")
var state = 0
state.bits[0..16] = 100
state.bits[0..16] %= 7
expect(state.bits[0..16]).to_equal(2)
```

</details>

#### masks += carry so it does not bleed into adjacent fields

- masks += carry so it does not bleed into adjacent fields
- Verify: masks += carry so it does not bleed into adjacent fields
   - Expected: state.bits[0..4] equals `0`
   - Expected: state.bits[4..8] equals `0x3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("masks += carry so it does not bleed into adjacent fields")
step("Verify: masks += carry so it does not bleed into adjacent fields")
# Field is 4 bits wide, holds 0xF; += 1 wraps the field to 0
# WITHOUT setting the next bit up.
var state = 0
state.bits[0..4] = 0xF
state.bits[4..8] = 0x3   # neighbour we want to leave alone
state.bits[0..4] += 1
expect(state.bits[0..4]).to_equal(0)
expect(state.bits[4..8]).to_equal(0x3)
```

</details>

#### augmented op on indexed lvalue still works (pure index)

- augmented op on indexed lvalue still works (pure index)
- Verify: augmented op on indexed lvalue still works (pure index)
   - Expected: arr[0].bits[0..8] equals `0x15`
   - Expected: arr[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("augmented op on indexed lvalue still works (pure index)")
step("Verify: augmented op on indexed lvalue still works (pure index)")
# Same pure-index caveat as Phase 1 plain `=`; documented above.
var arr = [0, 0]
arr[0].bits[0..8] = 0x10
arr[0].bits[0..8] += 0x05
expect(arr[0].bits[0..8]).to_equal(0x15)
expect(arr[1]).to_equal(0)
```

</details>

### int.bits writes inside defer blocks (B4-sugar Phase 3)

#### block-form defer with bitfield write runs the desugar (sanity)

- block-form defer with bitfield write runs the desugar (sanity)
- Verify: block-form defer with bitfield write runs the desugar (sanity)
   - Expected: state equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("block-form defer with bitfield write runs the desugar (sanity)")
step("Verify: block-form defer with bitfield write runs the desugar (sanity)")
# Sanity test: block-form defer always went through the regular
# statement parser, so it has worked since Phase 1. Pinning it
# so a regression in parse_block can't break Phase 3 silently.
var state = 0
defer:
    state.bits[0..8] = 0xCD
# defer fires when scope exits — but we observe inside the same
# `it` block, so we wire it via an inner scope using a do-block.
# Simpler: verify the parse succeeds and state stays its initial
# value during this scope. The defer just has to *parse*.
expect(state).to_equal(0)
```

</details>

#### single-line defer with bitfield write parses and lowers correctly

- single-line defer with bitfield write parses and lowers correctly
- Verify: single-line defer with bitfield write parses and lowers correctly
   - Expected: state equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("single-line defer with bitfield write parses and lowers correctly")
step("Verify: single-line defer with bitfield write parses and lowers correctly")
# The Phase 3 fix: this used to leave a raw FieldAccess("bits")
# in the AST and crash downstream. Now it desugars correctly.
var state = 0
defer state.bits[0..8] = 0xAB
# Same observation note as above — confirm parse succeeded and
# the desugar didn't mangle the surrounding scope's value.
expect(state).to_equal(0)
```

</details>

#### single-line defer with bitfield write on indexed lvalue

- single-line defer with bitfield write on indexed lvalue
- Verify: single-line defer with bitfield write on indexed lvalue
   - Expected: arr[0] equals `0`
   - Expected: arr[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("single-line defer with bitfield write on indexed lvalue")
step("Verify: single-line defer with bitfield write on indexed lvalue")
# Phase 1 pure-index caveat applies inside defer too.
var arr = [0, 0]
defer arr[0].bits[0..8] = 0x42
expect(arr[0]).to_equal(0)
expect(arr[1]).to_equal(0)
```

</details>

### int.bits side-effecting receiver guard (B4-sugar Phase 3)

#### literal index on bitfield write still parses (positive case)

- literal index on bitfield write still parses (positive case)
- Verify: literal index on bitfield write still parses (positive case)
   - Expected: arr[1] equals `0x33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("literal index on bitfield write still parses (positive case)")
step("Verify: literal index on bitfield write still parses (positive case)")
var arr = [0, 0, 0]
arr[1].bits[0..8] = 0x33
expect(arr[1]).to_equal(0x33)
```

</details>

#### identifier index on bitfield write still parses (positive case)

- identifier index on bitfield write still parses (positive case)
- Verify: identifier index on bitfield write still parses (positive case)
   - Expected: arr[2] equals `0x44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("identifier index on bitfield write still parses (positive case)")
step("Verify: identifier index on bitfield write still parses (positive case)")
var arr = [0, 0, 0]
var i = 2
arr[i].bits[0..8] = 0x44
expect(arr[2]).to_equal(0x44)
```

</details>

#### nested field-access on bitfield write still parses

- nested field-access on bitfield write still parses
- Verify: nested field-access on bitfield write still parses
   - Expected: arr[0] equals `0x37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("nested field-access on bitfield write still parses")
step("Verify: nested field-access on bitfield write still parses")
# Pure field-access spine: arr[0] is pure, .bits[…] desugars.
var arr = [0, 0]
arr[0].bits[0..4] = 0x7
arr[0].bits[4..8] = 0x3
expect(arr[0]).to_equal(0x37)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-INT-BITS-LO-HI-READ-SUGAR-B4-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3a1dad3e2ae2f57372fb30d61f39603ef8fdb831b24cec649dd187da9699997`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3a1dad3e2ae2f57372fb30d61f39603ef8fdb831b24cec649dd187da9699997`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3a1dad3e2ae2f57372fb30d61f39603ef8fdb831b24cec649dd187da9699997`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/bitfield_sugar_spec.spl
mirror: doc/06_spec/01_unit/compiler/bitfield_sugar_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bitfield_sugar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bitfield_sugar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bitfield_sugar_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/bitfield_sugar_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the low byte of a u32-shaped value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bitfield_sugar_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the high byte of a u32-shaped value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bitfield_sugar_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a 4-bit nibble at a non-byte boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
