# `blink_parse_declarations` exists and is what the cascade binds to

> Two different modules define a function named `parse_declarations`:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `blink_parse_declarations` exists and is what the cascade binds to

Two different modules define a function named `parse_declarations`:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Two different modules define a function named `parse_declarations`:

- `src/lib/blink/css_parser/parser.spl` — returns `[CssDeclaration]`.
- `src/lib/gc_async_mut/gpu/browser_engine/style_block_parse.spl` — returns
  `[CssDecl]`, a DIFFERENT type with different fields.

The interpreter resolves a function by NAME across co-compiled modules rather
than by import scope, so `blink.style.cascade` calling the bare name could bind
to the browser-engine one and fail later with `class CssDecl has no field named
important` — a wrong-module bind, not a missing function. The agreed fix was to
give blink's version a unique prefixed name, `blink_parse_declarations`.

`cascade.spl` was updated to import and call `blink_parse_declarations`, but the
definition was never added: the name existed at exactly one site in the whole
tree, the `use` line itself. A dangling import is the same class of silent
defect — the name resolves to nothing rather than to the wrong thing.

## Examples

The reproducing example calls `blink_parse_declarations` directly and checks it
returns blink `CssDeclaration` values carrying `important`. The class-detection
example checks the invariant that actually failed: that every name a blink
module imports from another blink module is really defined there.

## Scenarios

### blink_parse_declarations

#### parses an inline style attribute into blink CssDeclaration values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses an inline style attribute into blink CssDeclaration values
   - Expected: decls.len() equals `2`
   - Expected: decls[0].property equals `color`
   - Expected: decls[0].value equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses an inline style attribute into blink CssDeclaration values")
val decls = blink_parse_declarations("color: red; margin: 0")
expect(decls.len()).to_equal(2)
expect(decls[0].property).to_equal("color")
expect(decls[0].value).to_equal("red")
```

</details>

#### returns the blink declaration type, which carries `important`

- returns the blink declaration type, which carries `important`
   - Expected: decls.len() equals `1`
   - Expected: decls[0].important is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the blink declaration type, which carries `important`")
# This is the field whose absence was the observed symptom when the
# bare name bound to the browser-engine module's CssDecl instead.
val decls = blink_parse_declarations("color: red !important")
expect(decls.len()).to_equal(1)
expect(decls[0].important).to_equal(true)
```

</details>

#### agrees with the legacy unprefixed alias

- agrees with the legacy unprefixed alias
   - Expected: a.len() equals `b.len()`
   - Expected: a[0].property equals `b[0].property`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees with the legacy unprefixed alias")
val a = blink_parse_declarations("color: red; margin: 0")
val b = parse_declarations("color: red; margin: 0")
expect(a.len()).to_equal(b.len())
expect(a[0].property).to_equal(b[0].property)
```

</details>

### no blink module imports a name that is not defined

#### resolves every name in blink/style/cascade.spl's blink imports

- resolves every name in blink/style/cascade.spl's blink imports
   - Expected: src_opt == nil is false
   - Expected: checked > 0 is true
   - Expected: missing equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves every name in blink/style/cascade.spl's blink imports")
val src_opt = read_to_string("src/lib/blink/style/cascade.spl")
expect(src_opt == nil).to_equal(false)
val src = src_opt!
var missing: [text] = []
var checked = 0
val lines = src.split("\n")
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("use std.blink.") and line.contains(".") and line.contains(","):
        val open = line.index_of("." + "{")
        if open > 0:
            val dotted = line.substring(8, open)
            val close = line.index_of("" + "}")
            if close > open:
                val names = line.substring(open + 2, close).split(",")
                val target_opt = read_to_string(_module_path(dotted))
                if target_opt != nil:
                    val target = target_opt!
                    var j = 0
                    while j < names.len():
                        val nm = names[j].trim()
                        if nm.len() > 0:
                            checked = checked + 1
                            if not _defines(target, nm):
                                missing = missing + [dotted + "." + nm]
                        j = j + 1
    i = i + 1
# Non-vacuity: cascade.spl imports many names from blink modules. If
# this parse found nothing, the example proves nothing and must fail.
expect(checked > 0).to_equal(true)
expect(missing).to_equal([])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1330abb14eaa17f1f1bf9207bc4e4980e2c557fb1059ccfec37004ef16776666`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1330abb14eaa17f1f1bf9207bc4e4980e2c557fb1059ccfec37004ef16776666`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1330abb14eaa17f1f1bf9207bc4e4980e2c557fb1059ccfec37004ef16776666`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/blink_parse_declarations_symbol_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/blink_parse_declarations_symbol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/blink_parse_declarations_symbol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses an inline style attribute into blink CssDeclaration values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the blink declaration type, which carries `important`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/blink_parse_declarations_symbol_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the legacy unprefixed alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
