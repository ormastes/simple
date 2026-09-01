# width_index_spec

> Direct lifecycle and UTF-8 width coverage for WidthIndex.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# width_index_spec

Direct lifecycle and UTF-8 width coverage for WidthIndex.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/width_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct lifecycle and UTF-8 width coverage for WidthIndex.

## Scenarios

### WidthIndex lifecycle and coordinate conversion

#### maps every UTF-8 scalar width in the linear path

- maps every UTF-8 scalar width in the linear path
   - Expected: index.mode equals `linear`
   - Expected: index.char_to_byte(0) equals `0`
   - Expected: index.char_to_byte(1) equals `1`
   - Expected: index.char_to_byte(2) equals `3`
   - Expected: index.char_to_byte(3) equals `6`
   - Expected: index.char_to_byte(4) equals `10`
   - Expected: index.char_to_byte(5) equals `11`
   - Expected: index.char_to_byte(6) equals `-1`
   - Expected: index.char_to_byte(-1) equals `-1`
   - Expected: index.byte_to_char(0) equals `0`
   - Expected: index.byte_to_char(1) equals `1`
   - Expected: index.byte_to_char(3) equals `2`
   - Expected: index.byte_to_char(6) equals `3`
   - Expected: index.byte_to_char(10) equals `4`
   - Expected: index.byte_to_char(11) equals `5`
   - Expected: index.byte_to_char(-1) equals `-1`
   - Expected: index.char_at(0) equals `A`
   - Expected: index.char_at(1) equals `é`
   - Expected: index.char_at(2) equals `한`
   - Expected: index.char_at(3) equals `😀`
   - Expected: index.char_at(9) equals ``
   - Expected: index.char_at(-1) equals ``
   - Expected: index.slice(1, 4) equals `é한😀`
   - Expected: index.slice(-1, 4) equals ``
   - Expected: index.slice(1, -1) equals ``
   - Expected: index.codepoint_len() equals `5`
   - Expected: index.mode equals `freed`
   - Expected: index.mode equals `freed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps every UTF-8 scalar width in the linear path")
val index = WidthIndex.for_text("Aé한😀Z")
expect(index.mode).to_equal("linear")
expect(index.char_to_byte(0)).to_equal(0)
expect(index.char_to_byte(1)).to_equal(1)
expect(index.char_to_byte(2)).to_equal(3)
expect(index.char_to_byte(3)).to_equal(6)
expect(index.char_to_byte(4)).to_equal(10)
expect(index.char_to_byte(5)).to_equal(11)
expect(index.char_to_byte(6)).to_equal(-1)
expect(index.char_to_byte(-1)).to_equal(-1)
expect(index.byte_to_char(0)).to_equal(0)
expect(index.byte_to_char(1)).to_equal(1)
expect(index.byte_to_char(3)).to_equal(2)
expect(index.byte_to_char(6)).to_equal(3)
expect(index.byte_to_char(10)).to_equal(4)
expect(index.byte_to_char(11)).to_equal(5)
expect(index.byte_to_char(-1)).to_equal(-1)
expect(index.char_at(0)).to_equal("A")
expect(index.char_at(1)).to_equal("é")
expect(index.char_at(2)).to_equal("한")
expect(index.char_at(3)).to_equal("😀")
expect(index.char_at(9)).to_equal("")
expect(index.char_at(-1)).to_equal("")
expect(index.slice(1, 4)).to_equal("é한😀")
expect(index.slice(-1, 4)).to_equal("")
expect(index.slice(1, -1)).to_equal("")
expect(index.codepoint_len()).to_equal(5)
index.free()
expect(index.mode).to_equal("freed")
index.free()
expect(index.mode).to_equal("freed")
```

</details>

#### keeps short text linear after repeated access

- keeps short text linear after repeated access
   - Expected: index.char_to_byte(1) equals `1`
   - Expected: index.char_to_byte(2) equals `2`
   - Expected: index.mode equals `linear`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps short text linear after repeated access")
val index = WidthIndex.for_text("short")
expect(index.char_to_byte(1)).to_equal(1)
expect(index.char_to_byte(2)).to_equal(2)
expect(index.mode).to_equal("linear")
index.free()
```

</details>

#### builds SWI lazily and dispatches subsequent coordinate queries

- builds SWI lazily and dispatches subsequent coordinate queries
   - Expected: index.char_to_byte(259) equals `259`
   - Expected: index.mode equals `linear`
   - Expected: index.char_to_byte(260) equals `260`
   - Expected: index.mode equals `swi`
   - Expected: index.char_to_byte(261) equals `262`
   - Expected: index.byte_to_char(265) equals `262`
   - Expected: index.char_at(262) equals `😀`
   - Expected: index.mode equals `freed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds SWI lazily and dispatches subsequent coordinate queries")
val value = width_index_repeat("a", 260) + "é한😀Z"
val index = WidthIndex.for_text(value)
expect(index.char_to_byte(259)).to_equal(259)
expect(index.mode).to_equal("linear")
expect(index.char_to_byte(260)).to_equal(260)
expect(index.mode).to_equal("swi")
expect(index.char_to_byte(261)).to_equal(262)
expect(index.byte_to_char(265)).to_equal(262)
expect(index.char_at(262)).to_equal("😀")
index.free()
expect(index.mode).to_equal("freed")
```

</details>

#### falls back from an out-of-range SWI query to rank select

- falls back from an out-of-range SWI query to rank select
   - Expected: index.byte_to_char(1) equals `1`
   - Expected: index.byte_to_char(2) equals `2`
   - Expected: index.mode equals `swi`
   - Expected: index.char_to_byte(9999) equals `-1`
   - Expected: index.mode equals `rank_select`
   - Expected: index.char_to_byte(260) equals `260`
   - Expected: index.byte_to_char(262) equals `261`
   - Expected: index.mode equals `freed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back from an out-of-range SWI query to rank select")
val value = width_index_repeat("a", 260) + "é한😀Z"
val index = WidthIndex.for_text(value)
expect(index.byte_to_char(1)).to_equal(1)
expect(index.byte_to_char(2)).to_equal(2)
expect(index.mode).to_equal("swi")
expect(index.char_to_byte(9999)).to_equal(-1)
expect(index.mode).to_equal("rank_select")
expect(index.char_to_byte(260)).to_equal(260)
expect(index.byte_to_char(262)).to_equal(261)
index.free()
expect(index.mode).to_equal("freed")
```

</details>

#### falls back after an out-of-range SWI byte query

- falls back after an out-of-range SWI byte query
   - Expected: index.char_to_byte(1) equals `1`
   - Expected: index.char_to_byte(2) equals `2`
   - Expected: index.mode equals `swi`
   - Expected: index.byte_to_char(9999) equals `-1`
   - Expected: index.mode equals `rank_select`
   - Expected: index.byte_to_char(262) equals `261`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back after an out-of-range SWI byte query")
val value = width_index_repeat("a", 260) + "é한😀Z"
val index = WidthIndex.for_text(value)
expect(index.char_to_byte(1)).to_equal(1)
expect(index.char_to_byte(2)).to_equal(2)
expect(index.mode).to_equal("swi")
expect(index.byte_to_char(9999)).to_equal(-1)
expect(index.mode).to_equal("rank_select")
expect(index.byte_to_char(262)).to_equal(261)
index.free()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `f6384439c77aac5c971bb3e2f4bbfaeb01e9e78c043c5d3b1bf9cbf4d1232280`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6384439c77aac5c971bb3e2f4bbfaeb01e9e78c043c5d3b1bf9cbf4d1232280`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6384439c77aac5c971bb3e2f4bbfaeb01e9e78c043c5d3b1bf9cbf4d1232280`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/encoding/width_index_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/width_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/width_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/width_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/width_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 31 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/width_index_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps every UTF-8 scalar width in the linear path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/width_index_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps short text linear after repeated access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/width_index_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds SWI lazily and dispatches subsequent coordinate queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
