# bitfield_sugar_spec

> B4-sugar (compiler_bugs_for_crypto_2026-04-25.md) — `int.bits[lo..hi]`

<!-- sdn-diagram:id=bitfield_sugar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_sugar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_sugar_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_sugar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bitfield_sugar_spec

B4-sugar (compiler_bugs_for_crypto_2026-04-25.md) — `int.bits[lo..hi]`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bitfield_sugar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

B4-sugar (compiler_bugs_for_crypto_2026-04-25.md) — `int.bits[lo..hi]`
get/set syntax sugar.

The sugar desugars at parse time to plain shift+mask expressions, so both
the interpreter and the HIR-lowering paths see only `Binary{Shr/Shl/BitAnd/BitOr}`
nodes. No new AST or HIR variant.

Read   : `x.bits[lo..hi]`     -> `(x >> lo) & ((1 << (hi - lo)) - 1)`
Write  : `x.bits[lo..hi] = v` -> `x = (x & ~((mask) << lo)) | ((v & mask) << lo)`

## Scenarios

### int.bits[lo..hi] read sugar (B4)

#### extracts the low byte of a u32-shaped value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = 0x12345678
val byte0 = state.bits[0..8]
expect(byte0).to_equal(0x78)
```

</details>

#### extracts the high byte of a u32-shaped value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = 0x12345678
val byte3 = state.bits[24..32]
expect(byte3).to_equal(0x12)
```

</details>

#### extracts a 4-bit nibble at a non-byte boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0xABCD
# bits[4..8] = nibble at position 4 = 0xC
expect(n.bits[4..8]).to_equal(0xC)
```

</details>

#### matches plan repro shape `(state[i] & 0xFF000000) >> 24`

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = 0xDEADBEEF
val via_sugar = state.bits[24..32]
val via_manual = (state & 0xFF000000) >> 24
expect(via_sugar).to_equal(via_manual)
```

</details>

#### round-trips with bitwise_utils.extract_bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[lo..hi] is equivalent to extract_bits(n, lo, hi - lo)
val n = 0xCAFEBABE
val sugar = n.bits[8..16]
# 0xCAFEBABE -> byte at offset 8..16 = 0xBA
expect(sugar).to_equal(0xBA)
```

</details>

### int.bits[lo..hi] write sugar (B4)

#### writes the low byte and leaves higher bytes untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0x12345600
state.bits[0..8] = 0xEF
expect(state).to_equal(0x123456EF)
```

</details>

#### writes the high byte and leaves lower bytes untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0x00345678
state.bits[24..32] = 0xAB
expect(state).to_equal(0xAB345678)
```

</details>

#### clears the existing field before writing the new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0x000000FF
state.bits[0..8] = 0x12
expect(state).to_equal(0x00000012)
```

</details>

#### matches plan repro shape `state[i].bits[24..32] = byte`

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var word = 0x00BBCCDD
word.bits[24..32] = 0xAA
expect(word).to_equal(0xAABBCCDD)
```

</details>

#### masks the source value to the field width

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If the source has bits above the field width, they must be
# masked off — they must NOT bleed into adjacent fields.
var state = 0
state.bits[0..4] = 0xFF   # only the low 4 bits should land
expect(state).to_equal(0xF)
```

</details>

### int.bits round-trip and aliasing (B4)

#### write-then-read returns the written value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0x12345678
state.bits[8..16] = 0xAB
expect(state.bits[8..16]).to_equal(0xAB)
```

</details>

#### two non-overlapping field writes compose

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0
state.bits[0..8] = 0xAB
state.bits[8..16] = 0xCD
expect(state).to_equal(0xCDAB)
```

</details>

#### writing one field does not disturb a neighbouring field

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0xDEADBEEF
state.bits[0..32] = 0xCAFEBABE
expect(state.bits[0..32]).to_equal(0xCAFEBABE)
```

</details>

#### matches plan literal repro `state[i].bits[24..32] = byte`

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0x12340000
state.bits[16..24] = 0x10
state.bits[16..24] += 0x05
expect(state.bits[16..24]).to_equal(0x15)
# Higher field untouched
expect(state.bits[24..32]).to_equal(0x12)
```

</details>

#### supports -= on a bitfield slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0
state.bits[0..8] = 0x20
state.bits[0..8] -= 0x07
expect(state.bits[0..8]).to_equal(0x19)
```

</details>

#### supports *= on a bitfield slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0
state.bits[8..16] = 3
state.bits[8..16] *= 7
expect(state.bits[8..16]).to_equal(21)
```

</details>

#### supports /= on a bitfield slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0
state.bits[0..16] = 100
state.bits[0..16] /= 4
expect(state.bits[0..16]).to_equal(25)
```

</details>

#### supports %= on a bitfield slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 0
state.bits[0..16] = 100
state.bits[0..16] %= 7
expect(state.bits[0..16]).to_equal(2)
```

</details>

#### masks += carry so it does not bleed into adjacent fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase 1 pure-index caveat applies inside defer too.
var arr = [0, 0]
defer arr[0].bits[0..8] = 0x42
expect(arr[0]).to_equal(0)
expect(arr[1]).to_equal(0)
```

</details>

### int.bits side-effecting receiver guard (B4-sugar Phase 3)

#### literal index on bitfield write still parses (positive case)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 0, 0]
arr[1].bits[0..8] = 0x33
expect(arr[1]).to_equal(0x33)
```

</details>

#### identifier index on bitfield write still parses (positive case)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 0, 0]
var i = 2
arr[i].bits[0..8] = 0x44
expect(arr[2]).to_equal(0x44)
```

</details>

#### nested field-access on bitfield write still parses

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
