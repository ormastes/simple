# `dom_color` Hex Parsing Delegated to the Shared Parser

> Verifies the dom color shared hex parity behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `dom_color` Hex Parsing Delegated to the Shared Parser

Verifies the dom color shared hex parity behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser Engine |
| Status | Implemented |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the dom color shared hex parity behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### dom_color hex parsing via the shared parser

#### parity on supported forms

#### parses #RRGGBB with implied opaque alpha

- Verify: parses #RRGGBB with implied opaque alpha
   - Expected: parse_color_value("#1d4ed8") equals `0x1D4ED8FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: parses #RRGGBB with implied opaque alpha")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#1d4ed8")).to_equal(0x1D4ED8FFu32)
```

</details>

#### parses #RRGGBBAA preserving the explicit alpha byte

- Verify: parses #RRGGBBAA preserving the explicit alpha byte
   - Expected: parse_color_value("#11223344") equals `0x11223344u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: parses #RRGGBBAA preserving the explicit alpha byte")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#11223344")).to_equal(0x11223344u32)
```

</details>

#### parses #RGB by doubling each nibble

- Verify: parses #RGB by doubling each nibble
   - Expected: parse_color_value("#abc") equals `0xAABBCCFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: parses #RGB by doubling each nibble")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#abc")).to_equal(0xAABBCCFFu32)
```

</details>

#### parses #RGBA by doubling the alpha nibble too

- Verify: parses #RGBA by doubling the alpha nibble too
   - Expected: parse_color_value("#f00f") equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: parses #RGBA by doubling the alpha nibble too")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#f00f")).to_equal(0xFF0000FFu32)
```

</details>

#### treats uppercase and lowercase hex identically

- Verify: treats uppercase and lowercase hex identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: treats uppercase and lowercase hex identically")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#ABCDEF")).to_equal(
    parse_color_value("#abcdef"))
```

</details>

#### parses pure black and pure white at the range ends

- Verify: parses pure black and pure white at the range ends
   - Expected: parse_color_value("#000000") equals `0x000000FFu32`
   - Expected: parse_color_value("#ffffff") equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: parses pure black and pure white at the range ends")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#000000")).to_equal(0x000000FFu32)
expect(parse_color_value("#ffffff")).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses fully transparent #00000000 without collapsing to black

- Verify: parses fully transparent #00000000 without collapsing to black
   - Expected: parse_color_value("#00000000") equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: parses fully transparent #00000000 without collapsing to black")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#00000000")).to_equal(0x00000000u32)
```

</details>

#### agrees between the checked and unchecked entry points

- Verify: agrees between the checked and unchecked entry points


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: agrees between the checked and unchecked entry points")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#1d4ed8")).to_equal(
    0x1D4ED8FFu32)
```

</details>

#### unsupported input fails explicitly

#### returns nil for a non-hex digit

- Verify: returns nil for a non-hex digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: returns nil for a non-hex digit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#gg")).to_be_nil()
```

</details>

#### returns nil for a six-wide non-hex string

- Verify: returns nil for a six-wide non-hex string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: returns nil for a six-wide non-hex string")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#gggggg")).to_be_nil()
```

</details>

#### returns nil for a three-wide non-hex string

- Verify: returns nil for a three-wide non-hex string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: returns nil for a three-wide non-hex string")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#zzz")).to_be_nil()
```

</details>

#### returns nil for a length CSS does not define

- Verify: returns nil for a length CSS does not define


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: returns nil for a length CSS does not define")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#12345")).to_be_nil()
```

</details>

#### returns nil for a bare hash

- Verify: returns nil for a bare hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: returns nil for a bare hash")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#")).to_be_nil()
```

</details>

#### the u32 channel cannot carry the failure

#### gives an invalid colour the same u32 as a genuine black

- Verify: gives an invalid colour the same u32 as a genuine black


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: gives an invalid colour the same u32 as a genuine black")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("#gg")).to_equal(
    parse_color_value("#000000"))
```

</details>

#### distinguishes them only through the checked entry point

- Verify: distinguishes them only through the checked entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: distinguishes them only through the checked entry point")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value_checked("#gg")).to_be_nil()
expect(parse_color_value_checked("#000000")).to_equal(
    0x000000FFu32)
```

</details>

#### non-hex branches are untouched by the delegation
_The swap is scoped to the `#` branch; these must not move._

#### still resolves a named colour

- Verify: still resolves a named colour
   - Expected: parse_color_value("red") equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: still resolves a named colour")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("red")).to_equal(0xFF0000FFu32)
```

</details>

#### still resolves an rgb() function

- Verify: still resolves an rgb() function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: still resolves an rgb() function")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("rgb(29, 78, 216)")).to_equal(
    0x1D4ED8FFu32)
```

</details>

#### still returns transparent for var()

- Verify: still returns transparent for var()
   - Expected: parse_color_value("var(--x)") equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: still returns transparent for var()")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(parse_color_value("var(--x)")).to_equal(0x00000000u32)
```

</details>

#### still returns nil for an empty string

- Verify: still returns nil for an empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CSSCOLOR-002
step("Verify: still returns nil for an empty string")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `305640fe5698f23cd78ff3a7854b9437dff6dafa62e9b912174c0b32a1fb1c42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `305640fe5698f23cd78ff3a7854b9437dff6dafa62e9b912174c0b32a1fb1c42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `305640fe5698f23cd78ff3a7854b9437dff6dafa62e9b912174c0b32a1fb1c42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_shared_hex_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
