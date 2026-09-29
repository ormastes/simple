# Packed-u32 Colour Adapters

> `std.common.color.css` is the one shared CSS colour parser, and it answers a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed-u32 Colour Adapters

`std.common.color.css` is the one shared CSS colour parser, and it answers a

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLOR-CVG |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/color/color_pack_u32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`std.common.color.css` is the one shared CSS colour parser, and it answers a
`Color` struct. The browser renderer lanes carry colour as a packed `u32`.
That difference — not any missing feature — is why the 2026-05-19
"commonization" could never be adopted: the extraction was authored against a
type no call site used. These adapters are the missing piece.

## Scope and Preconditions

The two adapters are `Color.to_argb_u32()` and `Color.to_rgba_u32()`.

**The two names are the point.** The lanes do not agree on byte order:
`gpu/browser_engine/dom_color.spl` packs `0xRRGGBBAA`, while
`simple_web_css_box_effects.spl`, `simple_web_engine2d_renderer.spl` and
`simple_web_html_layout_renderer_foundation.spl` (`argb()`) pack `0xAARRGGBB`.
A single unnamed `to_u32()` would silently channel-swap half of them, which is
a wrong pixel rather than a crash. So the layout is named and the caller picks.

## Primary Workflow

A supported colour packs losslessly: `u32` carries all four 0..255 channels,
so alpha survives the adaptation in both orders.

What `u32` cannot carry is **failure**. `parse_hex_color` answers `nil` for
input it does not understand; there is deliberately no adapter that turns
`nil` into a colour. A helper that substituted opaque black would paint a
wrong pixel invisible to any smoke test — the exact defect blink's colour path
has today. Callers unwrap explicitly, and the wired call site below is wired
precisely because its contract already had somewhere to put a failure.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `to_argb_u32` | `0xAARRGGBB` — `argb()`/box-effects/engine2d convention. |
| `to_rgba_u32` | `0xRRGGBBAA` — `dom_color.spl` convention. |
| No `nil` adapter | Failure is never turned into a substituted colour. |

## Related Specifications

- [Shared CSS Colour Parsing](css_color_spec.md) — the parser being adapted.

## Scenarios

### Packed-u32 colour adapters

#### byte order
_The two layouts are distinct and both are exercised._

#### packs ARGB with alpha in the high byte

- packs ARGB with alpha in the high byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs ARGB with alpha in the high byte")
expect(from_rgba(0x11, 0x22, 0x33, 0x44).to_argb_u32()).to_equal(
    0x44112233u32)
```

</details>

#### packs RGBA with alpha in the low byte

- packs RGBA with alpha in the low byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs RGBA with alpha in the low byte")
expect(from_rgba(0x11, 0x22, 0x33, 0x44).to_rgba_u32()).to_equal(
    0x11223344u32)
```

</details>

#### keeps the two orders distinct for an asymmetric colour

- keeps the two orders distinct for an asymmetric colour


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the two orders distinct for an asymmetric colour")
val c = from_rgba(1, 2, 3, 4)
expect(c.to_argb_u32() == c.to_rgba_u32()).to_be(false)
```

</details>

#### defaults an opaque colour to full alpha in both orders

- defaults an opaque colour to full alpha in both orders
   - Expected: from_rgb(0, 0, 0).to_argb_u32() equals `0xFF000000u32`
   - Expected: from_rgb(0, 0, 0).to_rgba_u32() equals `0x000000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults an opaque colour to full alpha in both orders")
expect(from_rgb(0, 0, 0).to_argb_u32()).to_equal(0xFF000000u32)
expect(from_rgb(0, 0, 0).to_rgba_u32()).to_equal(0x000000FFu32)
```

</details>

#### packs full white without overflowing into a signed value

- packs full white without overflowing into a signed value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs full white without overflowing into a signed value")
expect(from_rgba(255, 255, 255, 255).to_argb_u32()).to_equal(
    0xFFFFFFFFu32)
```

</details>

#### parity with the hand-written parser it replaces

#### matches on #RRGGBBAA

- matches on #RRGGBBAA
   - Expected: c.to_argb_u32() equals `0x44112233u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches on #RRGGBBAA")
if val c = parse_hex_color("#11223344"):
    expect(c.to_argb_u32()).to_equal(0x44112233u32)
else:
    fail("#11223344 must parse")
```

</details>

#### matches on #RRGGBB with implied opaque alpha

- matches on #RRGGBB with implied opaque alpha
   - Expected: c.to_argb_u32() equals `0xFF1D4ED8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches on #RRGGBB with implied opaque alpha")
if val c = parse_hex_color("#1d4ed8"):
    expect(c.to_argb_u32()).to_equal(0xFF1D4ED8u32)
else:
    fail("#1d4ed8 must parse")
```

</details>

#### matches on #RGB nibble doubling

- matches on #RGB nibble doubling
   - Expected: c.to_argb_u32() equals `0xFFAABBCCu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches on #RGB nibble doubling")
if val c = parse_hex_color("#abc"):
    expect(c.to_argb_u32()).to_equal(0xFFAABBCCu32)
else:
    fail("#abc must parse")
```

</details>

#### matches on #RGBA nibble doubling including alpha

- matches on #RGBA nibble doubling including alpha
   - Expected: c.to_argb_u32() equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches on #RGBA nibble doubling including alpha")
if val c = parse_hex_color("#0000"):
    expect(c.to_argb_u32()).to_equal(0x00000000u32)
else:
    fail("#0000 must parse")
```

</details>

#### accepts uppercase hex identically to lowercase

- accepts uppercase hex identically to lowercase
   - Expected: u.to_argb_u32() equals `l.to_argb_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts uppercase hex identically to lowercase")
val upper = parse_hex_color("#1D4ED8")
val lower = parse_hex_color("#1d4ed8")
if val u = upper:
    if val l = lower:
        expect(u.to_argb_u32()).to_equal(l.to_argb_u32())
    else:
        fail("lowercase must parse")
else:
    fail("uppercase must parse")
```

</details>

#### unsupported input is a failure, never a colour

#### rejects a non-hex digit

- rejects a non-hex digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-hex digit")
expect(parse_hex_color("#12gg00") == nil).to_be(true)
```

</details>

#### rejects an over-long hex run

- rejects an over-long hex run


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an over-long hex run")
expect(parse_hex_color("#000000000") == nil).to_be(true)
```

</details>

#### rejects a hex run of an unsupported length

- rejects a hex run of an unsupported length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a hex run of an unsupported length")
expect(parse_hex_color("#12345") == nil).to_be(true)
```

</details>

#### rejects a token with no leading hash

- rejects a token with no leading hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a token with no leading hash")
expect(parse_hex_color("112233") == nil).to_be(true)
```

</details>

#### rejects the empty token

- rejects the empty token


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects the empty token")
expect(parse_hex_color("") == nil).to_be(true)
```

</details>

#### does not answer black for an unsupported colour function

- does not answer black for an unsupported colour function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not answer black for an unsupported colour function")
"""
`color-mix()` is real CSS this module does not implement. The
wrong behaviour to guard against is answering `0xFF000000`.
"""
expect(parse_css_color("color-mix(in srgb, red, blue)") == nil
    ).to_be(true)
```

</details>

#### does not answer black for currentColor

- does not answer black for currentColor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not answer black for currentColor")
"""
`currentColor` is resolvable only against the cascade, so the
shared parser must decline it rather than guess black.
"""
expect(parse_css_color("currentcolor") == nil).to_be(true)
```

</details>

#### transparent is a colour, not a failure

#### parses transparent to a real zero-alpha colour

- parses transparent to a real zero-alpha colour
   - Expected: c.a equals `0`
   - Expected: c.to_argb_u32() equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses transparent to a real zero-alpha colour")
if val c = parse_css_color("transparent"):
    expect(c.a).to_equal(0)
    expect(c.to_argb_u32()).to_equal(0x00000000u32)
else:
    fail("transparent must parse")
```

</details>

#### distinguishes transparent from an unparsable token

- distinguishes transparent from an unparsable token


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes transparent from an unparsable token")
val ok = parse_css_color("transparent")
val bad = parse_css_color("not-a-colour")
expect(ok == nil).to_be(false)
expect(bad == nil).to_be(true)
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

- Canonical SPipe generation for source `c5d30834ed49b6c054699b1c2e44d459b9287239e86878096314005534bdb5f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5d30834ed49b6c054699b1c2e44d459b9287239e86878096314005534bdb5f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5d30834ed49b6c054699b1c2e44d459b9287239e86878096314005534bdb5f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/color/color_pack_u32_spec.spl
mirror: doc/06_spec/01_unit/lib/common/color/color_pack_u32_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/color/color_pack_u32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/color/color_pack_u32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/color/color_pack_u32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/color/color_pack_u32_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/color/color_pack_u32_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs ARGB with alpha in the high byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/color_pack_u32_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs RGBA with alpha in the low byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/color_pack_u32_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the two orders distinct for an asymmetric colour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
