# `unsafe` / `danger` as ordinary identifiers in block headers

> `unsafe` and `danger` name a block form (`unsafe:` / `unsafe(capabilities: [ffi]):`)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `unsafe` / `danger` as ordinary identifiers in block headers

`unsafe` and `danger` name a block form (`unsafe:` / `unsafe(capabilities: [ffi]):`)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`unsafe` and `danger` name a block form (`unsafe:` / `unsafe(capabilities: [ffi]):`)
but are NOT reserved words: a variable may be called `unsafe`. When such a
variable is the last token of a block header — `for e in unsafe:`,
`while unsafe:`, `if unsafe:` — the trailing colon belongs to the HEADER, not to
an unsafe block.

Regression for
`doc/08_tracking/bug/seed_redeploy_breaks_test_runner_accessor_rewrite_parse_2026-08-25.md`:
a seed accepted a bare `unsafe:` as an expression-position unsafe block, so the
header colon and the whole body were swallowed and
`src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl:134` failed with
`Unexpected token: expected Colon, found If`, aborting every `bin/simple test`.

## Scenarios

### unsafe as an ordinary identifier in block headers

#### iterates a list variable named unsafe

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- iterates a list variable named unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates a list variable named unsafe")
var unsafe: List<text> = []
unsafe.push("a")
unsafe.push("b")
var seen = ""
for existing in unsafe:
    seen = seen + existing
if seen != "":
    assert_equal(seen, "ab")
```

</details>

#### uses a bool variable named unsafe as a while condition

- uses a bool variable named unsafe as a while condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses a bool variable named unsafe as a while condition")
var unsafe = true
var rounds = 0
while unsafe:
    rounds = rounds + 1
    unsafe = false
if rounds > 0:
    assert_equal(rounds, 1)
```

</details>

#### uses a bool variable named unsafe as an if condition

- uses a bool variable named unsafe as an if condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses a bool variable named unsafe as an if condition")
var unsafe = false
var hit = 0
if unsafe:
    hit = 1
assert_equal(hit, 0)
```

</details>

#### iterates a list variable named danger

- iterates a list variable named danger


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates a list variable named danger")
var danger: List<text> = []
danger.push("x")
var seen = ""
for existing in danger:
    seen = seen + existing
if seen != "":
    assert_equal(seen, "x")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `730cf42bede47297d8f2e680eff863004cdad0545a4fcb98763eb94b1eebff45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `730cf42bede47297d8f2e680eff863004cdad0545a4fcb98763eb94b1eebff45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `730cf42bede47297d8f2e680eff863004cdad0545a4fcb98763eb94b1eebff45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/unsafe_identifier_block_header_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/unsafe_identifier_block_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/unsafe_identifier_block_header_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'iterates a list variable named unsafe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a bool variable named unsafe as a while condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a bool variable named unsafe as an if condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
