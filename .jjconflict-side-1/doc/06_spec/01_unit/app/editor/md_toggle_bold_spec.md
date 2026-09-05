# markdown.toggle_bold — Handler Unit Coverage

> Unit coverage for the typed `markdown.toggle_bold` command handler: the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# markdown.toggle_bold — Handler Unit Coverage

Unit coverage for the typed `markdown.toggle_bold` command handler: the

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | IDE-EXT-KERNEL L1 |
| Category | Unit |
| Status | In Progress |
| Source | `test/01_unit/app/editor/md_toggle_bold_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Unit coverage for the typed `markdown.toggle_bold` command handler: the
line-level toggle (`md_toggle_bold_line`) over selections, words at the
cursor, and already-bold segments, plus the payload codec used by
`ExtensionHost.dispatch_command`.

## Scenarios

### md_toggle_bold_line

#### wraps an explicit selection in **

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wraps an explicit selection in **
   - Expected: md_toggle_bold_line("hello world", 0, 6, 11) equals `hello **world**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps an explicit selection in **")
expect(md_toggle_bold_line("hello world", 0, 6, 11)).to_equal("hello **world**")
```

</details>

#### unwraps when the selection is surrounded by **

- unwraps when the selection is surrounded by **
   - Expected: md_toggle_bold_line("hello **world**", 0, 8, 13) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unwraps when the selection is surrounded by **")
expect(md_toggle_bold_line("hello **world**", 0, 8, 13)).to_equal("hello world")
```

</details>

#### unwraps when the selection includes the ** markers

- unwraps when the selection includes the ** markers
   - Expected: md_toggle_bold_line("hello **world**", 0, 6, 15) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unwraps when the selection includes the ** markers")
expect(md_toggle_bold_line("hello **world**", 0, 6, 15)).to_equal("hello world")
```

</details>

#### wraps the word at the cursor when there is no selection

- wraps the word at the cursor when there is no selection
   - Expected: md_toggle_bold_line("hello world", 8, -1, -1) equals `hello **world**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps the word at the cursor when there is no selection")
expect(md_toggle_bold_line("hello world", 8, -1, -1)).to_equal("hello **world**")
```

</details>

#### unwraps the word at the cursor when already bold

- unwraps the word at the cursor when already bold
   - Expected: md_toggle_bold_line("hello **world**", 10, -1, -1) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unwraps the word at the cursor when already bold")
expect(md_toggle_bold_line("hello **world**", 10, -1, -1)).to_equal("hello world")
```

</details>

#### uses the word just before the cursor at end of line

- uses the word just before the cursor at end of line
   - Expected: md_toggle_bold_line("hello", 5, -1, -1) equals `**hello**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the word just before the cursor at end of line")
expect(md_toggle_bold_line("hello", 5, -1, -1)).to_equal("**hello**")
```

</details>

#### inserts empty bold markers when the cursor is not on a word

- inserts empty bold markers when the cursor is not on a word
   - Expected: md_toggle_bold_line("a  b", 2, -1, -1) equals `a **** b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("inserts empty bold markers when the cursor is not on a word")
expect(md_toggle_bold_line("a  b", 2, -1, -1)).to_equal("a **** b")
```

</details>

#### clamps an out-of-range selection to the line

- clamps an out-of-range selection to the line
   - Expected: md_toggle_bold_line("word", 0, 0, 99) equals `**word**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("clamps an out-of-range selection to the line")
expect(md_toggle_bold_line("word", 0, 0, 99)).to_equal("**word**")
```

</details>

### md_toggle_bold_handler payload codec

#### decodes col|sel_start|sel_end|line and returns the toggled line

- decodes col|sel_start|sel_end|line and returns the toggled line
   - Expected: value equals `hello **world**`
   - Expected: "handler" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("decodes col|sel_start|sel_end|line and returns the toggled line")
match md_toggle_bold_handler("0|6|11|hello world"):
    case Ok(value):
        expect(value).to_equal("hello **world**")
    case Err(_):
        expect("handler").to_equal("should have succeeded")
```

</details>

#### keeps pipe characters inside the line text

- keeps pipe characters inside the line text
   - Expected: value equals `a **|b|c**| d`
   - Expected: "handler" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps pipe characters inside the line text")
match md_toggle_bold_handler("0|2|6|a |b|c| d"):
    case Ok(value):
        expect(value).to_equal("a **|b|c**| d")
    case Err(_):
        expect("handler").to_equal("should have succeeded")
```

</details>

#### rejects a payload without a header

- rejects a payload without a header
   - Expected: "handler" equals `should have failed`
   - Expected: message contains `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a payload without a header")
match md_toggle_bold_handler("no separators here"):
    case Ok(_):
        expect("handler").to_equal("should have failed")
    case Err(message):
        expect(message.contains("payload")).to_equal(true)
```

</details>

### markdown diagnostics provider handler

#### encodes diagnostics as line|col|severity|message rows

- encodes diagnostics as line|col|severity|message rows
   - Expected: encoded contains `Heading requires a space after '#'`
   - Expected: "handler" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("encodes diagnostics as line|col|severity|message rows")
match md_language_diagnose_handler("#Bad\n"):
    case Ok(encoded):
        expect(encoded.contains("Heading requires a space after '#'")).to_equal(true)
    case Err(_):
        expect("handler").to_equal("should have succeeded")
```

</details>

#### returns empty text for clean markdown

- returns empty text for clean markdown
   - Expected: encoded equals ``
   - Expected: "handler" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns empty text for clean markdown")
match md_language_diagnose_handler("# Fine heading\n\nbody\n"):
    case Ok(encoded):
        expect(encoded).to_equal("")
    case Err(_):
        expect("handler").to_equal("should have succeeded")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-IDE-EXT-KERNEL-L1`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6b26b1ae5080f31b7fcfff61f25a1646aa72e0d65355bf8ffd935eb2208e4cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6b26b1ae5080f31b7fcfff61f25a1646aa72e0d65355bf8ffd935eb2208e4cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6b26b1ae5080f31b7fcfff61f25a1646aa72e0d65355bf8ffd935eb2208e4cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/editor/md_toggle_bold_spec.spl
mirror: doc/06_spec/01_unit/app/editor/md_toggle_bold_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/editor/md_toggle_bold_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/editor/md_toggle_bold_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/editor/md_toggle_bold_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/editor/md_toggle_bold_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps an explicit selection in **' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/editor/md_toggle_bold_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps when the selection is surrounded by **' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/editor/md_toggle_bold_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps when the selection includes the ** markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
