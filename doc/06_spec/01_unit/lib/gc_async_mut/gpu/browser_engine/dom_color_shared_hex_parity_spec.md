# `dom_color` Hex Parsing Delegated to the Shared Parser

> `dom_color.spl` is one of eight browser-lane colour parsers that carry colour

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `dom_color` Hex Parsing Delegated to the Shared Parser

`dom_color.spl` is one of eight browser-lane colour parsers that carry colour

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser Engine |
| Status | Implemented |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`dom_color.spl` is one of eight browser-lane colour parsers that carry colour
as a packed `u32`. Its hex branch now delegates to the single shared
implementation in `std.common.color.css`. This spec is the before/after
evidence for that swap: it pins the value of every supported form so a
regression is a failing assertion rather than a slightly wrong pixel.

## Scope and Preconditions

`parse_color_value_checked(text) -> u32?` is the delegating entry point.
`parse_color_value(text) -> u32` wraps it with `?? 0x000000FF`. Both are
exercised, because they differ precisely in what they can say about failure.

## Primary Workflow

For a supported colour the two functions agree and produce the historical
`0xRRGGBBAA` value. For an unsupported colour the checked form answers `nil`
and the unchecked form answers opaque black — unchanged from before the swap,
so no existing caller moves.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `u32` is lossy | `#gg` and `#000000` are both `0x000000FF`. |
| `Color?` is not | `nil` distinguishes "unsupported" from "black". |
| Byte order | `dom_color` packs `0xRRGGBBAA` (`to_rgba_u32`). |

## Related Specifications

- [Shared CSS Colour Parsing](../../../common/color/css_color_spec.md)
- [Packed-u32 colour adapters](../../../common/color/color_pack_u32_spec.md)

## Scenarios

### dom_color hex parsing via the shared parser

#### parity on supported forms

#### parses #RRGGBB with implied opaque alpha

- parses #RRGGBB with implied opaque alpha
   - Expected: parse_color_value("#1d4ed8") equals `0x1D4ED8FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses #RRGGBB with implied opaque alpha")
expect(parse_color_value("#1d4ed8")).to_equal(0x1D4ED8FFu32)
```

</details>

#### parses #RRGGBBAA preserving the explicit alpha byte

- parses #RRGGBBAA preserving the explicit alpha byte
   - Expected: parse_color_value("#11223344") equals `0x11223344u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses #RRGGBBAA preserving the explicit alpha byte")
expect(parse_color_value("#11223344")).to_equal(0x11223344u32)
```

</details>

#### parses #RGB by doubling each nibble

- parses #RGB by doubling each nibble
   - Expected: parse_color_value("#abc") equals `0xAABBCCFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses #RGB by doubling each nibble")
expect(parse_color_value("#abc")).to_equal(0xAABBCCFFu32)
```

</details>

#### parses #RGBA by doubling the alpha nibble too

- parses #RGBA by doubling the alpha nibble too
   - Expected: parse_color_value("#f00f") equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses #RGBA by doubling the alpha nibble too")
expect(parse_color_value("#f00f")).to_equal(0xFF0000FFu32)
```

</details>

#### treats uppercase and lowercase hex identically

- treats uppercase and lowercase hex identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats uppercase and lowercase hex identically")
expect(parse_color_value("#ABCDEF")).to_equal(
    parse_color_value("#abcdef"))
```

</details>

#### parses pure black and pure white at the range ends

- parses pure black and pure white at the range ends
   - Expected: parse_color_value("#000000") equals `0x000000FFu32`
   - Expected: parse_color_value("#ffffff") equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses pure black and pure white at the range ends")
expect(parse_color_value("#000000")).to_equal(0x000000FFu32)
expect(parse_color_value("#ffffff")).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses fully transparent #00000000 without collapsing to black

- parses fully transparent #00000000 without collapsing to black
   - Expected: parse_color_value("#00000000") equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses fully transparent #00000000 without collapsing to black")
expect(parse_color_value("#00000000")).to_equal(0x00000000u32)
```

</details>

#### agrees between the checked and unchecked entry points

- agrees between the checked and unchecked entry points


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees between the checked and unchecked entry points")
expect(parse_color_value_checked("#1d4ed8")).to_equal(
    0x1D4ED8FFu32)
```

</details>

#### unsupported input fails explicitly

#### returns nil for a non-hex digit

- returns nil for a non-hex digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for a non-hex digit")
expect(parse_color_value_checked("#gg")).to_be_nil()
```

</details>

#### returns nil for a six-wide non-hex string

- returns nil for a six-wide non-hex string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for a six-wide non-hex string")
expect(parse_color_value_checked("#gggggg")).to_be_nil()
```

</details>

#### returns nil for a three-wide non-hex string

- returns nil for a three-wide non-hex string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for a three-wide non-hex string")
expect(parse_color_value_checked("#zzz")).to_be_nil()
```

</details>

#### returns nil for a length CSS does not define

- returns nil for a length CSS does not define


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for a length CSS does not define")
expect(parse_color_value_checked("#12345")).to_be_nil()
```

</details>

#### returns nil for a bare hash

- returns nil for a bare hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for a bare hash")
expect(parse_color_value_checked("#")).to_be_nil()
```

</details>

#### the u32 channel cannot carry the failure

#### gives an invalid colour the same u32 as a genuine black

- gives an invalid colour the same u32 as a genuine black


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives an invalid colour the same u32 as a genuine black")
expect(parse_color_value("#gg")).to_equal(
    parse_color_value("#000000"))
```

</details>

#### distinguishes them only through the checked entry point

- distinguishes them only through the checked entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes them only through the checked entry point")
expect(parse_color_value_checked("#gg")).to_be_nil()
expect(parse_color_value_checked("#000000")).to_equal(
    0x000000FFu32)
```

</details>

#### non-hex branches are untouched by the delegation
_The swap is scoped to the `#` branch; these must not move._

#### still resolves a named colour

- still resolves a named colour
   - Expected: parse_color_value("red") equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still resolves a named colour")
expect(parse_color_value("red")).to_equal(0xFF0000FFu32)
```

</details>

#### still resolves an rgb() function

- still resolves an rgb() function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still resolves an rgb() function")
expect(parse_color_value("rgb(29, 78, 216)")).to_equal(
    0x1D4ED8FFu32)
```

</details>

#### still returns transparent for var()

- still returns transparent for var()
   - Expected: parse_color_value("var(--x)") equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still returns transparent for var()")
expect(parse_color_value("var(--x)")).to_equal(0x00000000u32)
```

</details>

#### still returns nil for an empty string

- still returns nil for an empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still returns nil for an empty string")
expect(parse_color_value_checked("")).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-CSSCOLOR-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `777d469fa11395cb160064acfc092155c508d063635aecbf34aec6da539410d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `777d469fa11395cb160064acfc092155c508d063635aecbf34aec6da539410d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `777d469fa11395cb160064acfc092155c508d063635aecbf34aec6da539410d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses #RRGGBB with implied opaque alpha' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses #RRGGBBAA preserving the explicit alpha byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses #RGB by doubling each nibble' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
