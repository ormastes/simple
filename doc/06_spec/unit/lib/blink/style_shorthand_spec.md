# Blink Shorthand Expansion Specification

> Expanding a shorthand into longhands is only correct if the CASCADE ORDER survives it. Two rules carry the whole risk, and both fail silently when broken because the result is a plausible style rather than an error:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Shorthand Expansion Specification

Expanding a shorthand into longhands is only correct if the CASCADE ORDER survives it. Two rules carry the whole risk, and both fail silently when broken because the result is a plausible style rather than an error:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/style_shorthand_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Expanding a shorthand into longhands is only correct if the CASCADE ORDER
survives it. Two rules carry the whole risk, and both fail silently when
broken because the result is a plausible style rather than an error:

- a shorthand resets EVERY longhand it covers, including ones the author never
  mentioned, so a longhand written BEFORE it is gone;
- expansion happens IN PLACE, so a longhand written AFTER it still wins.

This specification pins both directions, plus the rule that a shorthand which
cannot be decomposed is dropped and reported rather than half-applied.

## Scenarios

### shorthand ordering

#### lets a longhand written after a shorthand win

- lets a longhand written after a shorthand win
- expand `margin: 5px; margin-left: 20px` and read margin-left
   - Expected: _final("margin: 5px; margin-left: 20px", "margin-left") equals `20px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets a longhand written after a shorthand win")
step("expand `margin: 5px; margin-left: 20px` and read margin-left")
expect(_final("margin: 5px; margin-left: 20px", "margin-left")).to_equal("20px")
```

</details>

#### lets a shorthand written after a longhand clobber it

- lets a shorthand written after a longhand clobber it
- expand `margin-left: 20px; margin: 5px` and read margin-left
   - Expected: _final("margin-left: 20px; margin: 5px", "margin-left") equals `5px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets a shorthand written after a longhand clobber it")
step("expand `margin-left: 20px; margin: 5px` and read margin-left")
expect(_final("margin-left: 20px; margin: 5px", "margin-left")).to_equal("5px")
```

</details>

#### resets a longhand the shorthand never mentions

- resets a longhand the shorthand never mentions
- write margin-left, then `margin: 0 auto`, which mentions no single side
   - Expected: _final("margin-left: 20px; margin: 0 auto", "margin-left") equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets a longhand the shorthand never mentions")
step("write margin-left, then `margin: 0 auto`, which mentions no single side")
expect(_final("margin-left: 20px; margin: 0 auto", "margin-left")).to_equal("auto")
```

</details>

#### resets a border colour the later shorthand omits

- resets a border colour the later shorthand omits
- write border-top-color, then `border-top: 1px solid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets a border colour the later shorthand omits")
step("write border-top-color, then `border-top: 1px solid`")
expect(_final("border-top-color: red; border-top: 1px solid", "border-top-color")).to_equal(
    "currentcolor")
```

</details>

#### expands in place rather than hoisting the longhands

- expands in place rather than hoisting the longhands
- expand `color: red; margin: 1px; display: block` and read the sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands in place rather than hoisting the longhands")
step("expand `color: red; margin: 1px; display: block` and read the sequence")
expect(_expanded("color: red; margin: 1px; display: block")).to_equal(
    "color=red;margin-top=1px;margin-right=1px;margin-bottom=1px;margin-left=1px;display=block")
```

</details>

#### leaves a non-shorthand declaration untouched

- leaves a non-shorthand declaration untouched
- expand a block with no shorthands at all
   - Expected: _expanded("color: red; display: block") equals `color=red;display=block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a non-shorthand declaration untouched")
step("expand a block with no shorthands at all")
expect(_expanded("color: red; display: block")).to_equal("color=red;display=block")
```

</details>

### important shorthands

#### marks every expanded longhand important when the shorthand was

- marks every expanded longhand important when the shorthand was
- expand `margin: 1px !important` and count important longhands
   - Expected: important_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks every expanded longhand important when the shorthand was")
step("expand `margin: 1px !important` and count important longhands")
val result = expand_declarations(parse_declarations("margin: 1px !important"))
var important_count = 0
var i = 0
while i < result.declarations.len():
    if result.declarations[i as i32].important:
        important_count = important_count + 1
    i = i + 1
expect(important_count).to_equal(4)
```

</details>

#### does not mark longhands important when the shorthand was not

- does not mark longhands important when the shorthand was not
- expand a plain `margin: 1px`
   - Expected: result.declarations[0 as i32].important is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mark longhands important when the shorthand was not")
step("expand a plain `margin: 1px`")
val result = expand_declarations(parse_declarations("margin: 1px"))
expect(result.declarations[0 as i32].important).to_equal(false)
```

</details>

### undecomposable shorthands

#### drops an undecomposable shorthand rather than expanding it partially

- drops an undecomposable shorthand rather than expanding it partially
- expand `border: 1px wiggly red` alongside a valid declaration
   - Expected: _expanded("color: red; border: 1px wiggly red") equals `color=red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops an undecomposable shorthand rather than expanding it partially")
step("expand `border: 1px wiggly red` alongside a valid declaration")
expect(_expanded("color: red; border: 1px wiggly red")).to_equal("color=red")
```

</details>

#### reports the dropped shorthand instead of losing it silently

- reports the dropped shorthand instead of losing it silently
- count the dropped shorthands of the same block
   - Expected: _dropped("color: red; border: 1px wiggly red") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the dropped shorthand instead of losing it silently")
step("count the dropped shorthands of the same block")
expect(_dropped("color: red; border: 1px wiggly red")).to_equal(1)
```

</details>

#### leaves an earlier longhand alive when the later shorthand is invalid

- leaves an earlier longhand alive when the later shorthand is invalid
- write border-top-color, then an invalid `border-top`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an earlier longhand alive when the later shorthand is invalid")
step("write border-top-color, then an invalid `border-top`")
expect(_final("border-top-color: red; border-top: 1px wiggly", "border-top-color")).to_equal(
    "red")
```

</details>

#### reports nothing dropped for a block it fully understands

- reports nothing dropped for a block it fully understands
- expand a block of valid shorthands
   - Expected: _dropped("margin: 1px; padding: 2px; flex: 1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports nothing dropped for a block it fully understands")
step("expand a block of valid shorthands")
expect(_dropped("margin: 1px; padding: 2px; flex: 1")).to_equal(0)
```

</details>

### expanding parsed rules

#### expands the declarations of every rule in a sheet

- expands the declarations of every rule in a sheet
- parse and expand two rules, each carrying one shorthand
   - Expected: expanded[0 as i32].declarations.len() equals `4`
   - Expected: expanded[1 as i32].declarations.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands the declarations of every rule in a sheet")
step("parse and expand two rules, each carrying one shorthand")
val sheet = parse_css(tokenize_css("p { margin: 1px; } div { flex: none; }"))
val expanded = expand_rules(sheet.rules)
expect(expanded[0 as i32].declarations.len()).to_equal(4)
expect(expanded[1 as i32].declarations.len()).to_equal(3)
```

</details>

#### keeps the selector when expanding a rule

- keeps the selector when expanding a rule
- expand a single rule and read its selector back
   - Expected: expand_rule(sheet.rules[0 as i32]).selector equals `p.lead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the selector when expanding a rule")
step("expand a single rule and read its selector back")
val sheet = parse_css(tokenize_css("p.lead { padding: 2px; }"))
expect(expand_rule(sheet.rules[0 as i32]).selector).to_equal("p.lead")
```

</details>

#### names the full reset set of a shorthand without a value

- names the full reset set of a shorthand without a value
- ask for the longhands `margin` writes
   - Expected: shorthand_longhands("margin").len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the full reset set of a shorthand without a value")
step("ask for the longhands `margin` writes")
expect(shorthand_longhands("margin").len()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `54751ed0817174800088ad77872c2b034cea64fa927df5afa366d30ed50c4d59`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54751ed0817174800088ad77872c2b034cea64fa927df5afa366d30ed50c4d59`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54751ed0817174800088ad77872c2b034cea64fa927df5afa366d30ed50c4d59`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/blink/style_shorthand_spec.spl
mirror: doc/06_spec/unit/lib/blink/style_shorthand_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/style_shorthand_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/style_shorthand_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/style_shorthand_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/style_shorthand_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets a longhand written after a shorthand win' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/style_shorthand_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets a shorthand written after a longhand clobber it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/style_shorthand_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets a longhand the shorthand never mentions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
