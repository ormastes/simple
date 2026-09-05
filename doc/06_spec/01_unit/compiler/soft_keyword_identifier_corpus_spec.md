# Soft Keyword Identifier Corpus Specification

> Tests covering soft keywords usable as ordinary identifiers (parse-position sweep).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Soft Keyword Identifier Corpus Specification

## Scenarios

### soft keywords usable as ordinary identifiers (parse-position sweep)

#### case -- the reported defect: match-arm marker only

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- case -- the reported defect: match-arm marker only


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("case -- the reported defect: match-arm marker only")
var total = 0
for case in [1, 2, 3]:
    total = total + case
val case = SkBox(n: 5)
expect total + case.n to_equal 11
```

</details>

#### context / feature / scenario -- BDD grouping keywords

- context / feature / scenario -- BDD grouping keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("context / feature / scenario -- BDD grouping keywords")
var t = 0
for context in [1, 2]:
    t = t + context
val feature = SkBox(n: 3)
var scenario = 0
for scenario in [4]:
    t = t + scenario
expect t + feature.n to_equal 10
```

</details>

#### given / when / then / outline -- Gherkin step keywords

- given / when / then / outline -- Gherkin step keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("given / when / then / outline -- Gherkin step keywords")
var t = 0
for given in [1]:
    t = t + given
for when in [2]:
    t = t + when
for then in [3]:
    t = t + then
val outline = SkBox(n: 4)
expect t + outline.n to_equal 10
```

</details>

#### result / out / type -- contract keywords

- result / out / type -- contract keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result / out / type -- contract keywords")
var t = 0
for result in [1]:
    t = t + result
for out in [2]:
    t = t + out
val type = SkBox(n: 3)
expect t + type.n to_equal 6
```

</details>

#### default / common -- config and stdlib-path keywords

- default / common -- config and stdlib-path keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default / common -- config and stdlib-path keywords")
var t = 0
for default in [1, 2]:
    t = t + default
val common = SkBox(n: 4)
expect t + common.n to_equal 7
```

</details>

#### lazy / skip / exists -- evaluation and test-control keywords

- lazy / skip / exists -- evaluation and test-control keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lazy / skip / exists -- evaluation and test-control keywords")
var t = 0
for lazy in [1]:
    t = t + lazy
for skip in [2]:
    t = t + skip
val exists = SkBox(n: 3)
expect t + exists.n to_equal 6
```

</details>

#### new / old / from / by -- contract and pipeline keywords

- new / old / from / by -- contract and pipeline keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new / old / from / by -- contract and pipeline keywords")
var t = 0
for new in [1]:
    t = t + new
for old in [2]:
    t = t + old
for from in [3]:
    t = t + from
val by = SkBox(n: 4)
expect t + by.n to_equal 10
```

</details>

#### mod / union / examples -- declaration keywords

- mod / union / examples -- declaration keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mod / union / examples -- declaration keywords")
var t = 0
for mod in [1]:
    t = t + mod
for union in [2]:
    t = t + union
val examples = SkBox(n: 3)
expect t + examples.n to_equal 6
```

</details>

#### un-reserving must not cost `case` its real job as a match-arm marker

- un-reserving must not cost `case` its real job as a match-arm marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("un-reserving must not cost `case` its real job as a match-arm marker")
# The other half of the invariant: this spec must fail if someone
# "fixes" the reservation by deleting the keyword outright.
val classify = \n: match n:
    case 0: "zero"
    case _: "other"
expect classify(0) to_equal "zero"
expect classify(7) to_equal "other"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/soft_keyword_identifier_corpus_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering soft keywords usable as ordinary identifiers (parse-position sweep).
- soft keywords usable as ordinary identifiers (parse-position sweep)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `e60701e34af0926f5975d021332ad3e9716ed2af3bef9a69012602cbf6eee02a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e60701e34af0926f5975d021332ad3e9716ed2af3bef9a69012602cbf6eee02a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e60701e34af0926f5975d021332ad3e9716ed2af3bef9a69012602cbf6eee02a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/soft_keyword_identifier_corpus_spec.spl
mirror: doc/06_spec/01_unit/compiler/soft_keyword_identifier_corpus_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/soft_keyword_identifier_corpus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/soft_keyword_identifier_corpus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/soft_keyword_identifier_corpus_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case -- the reported defect: match-arm marker only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/soft_keyword_identifier_corpus_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'context / feature / scenario -- BDD grouping keywords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/soft_keyword_identifier_corpus_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'given / when / then / outline -- Gherkin step keywords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
