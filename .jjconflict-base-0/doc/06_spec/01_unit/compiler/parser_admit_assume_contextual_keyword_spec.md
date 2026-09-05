# `admit` and `assume` as ordinary identifiers

> `admit` and `assume` are proof statements: they only ever appear in STATEMENT

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `admit` and `assume` as ordinary identifiers

`admit` and `assume` are proof statements: they only ever appear in STATEMENT

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language / Parser |
| Status | Regression guard |
| Source | `test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`admit` and `assume` are proof statements: they only ever appear in STATEMENT
position, followed by a condition. They are not in the reserved-keyword list in
`.claude/rules/language.md`, so a user naturally reaches for `admit` as a plain
name -- a loader that admits a module, a verifier that admits a seal.

Until 2026-08-21 the lexer already handed back an identifier when `!` or `(`
followed (so `fn admit(x)` and `admit(1)` happened to work), but every OTHER
identifier position still saw the keyword token and died with
`Unexpected token: expected identifier, found Admit`: an import list
(`use m.lib.{admit}`), a variable declaration, a parameter or field name, or a
bare read in an expression. That is the same defect class as `move`,
`examples`, and `and_then` -- a reserved token rejected at the USE site.

The audience is anyone touching identifier admission in the Rust seed parser:
`expect_identifier` / `expect_path_segment` (`parser/src/parser_helpers.rs`)
and the primary-expression dispatch
(`parser/src/expressions/primary/identifiers.rs`).

## Scope and Preconditions

Requires a seed built at or after 2026-08-21; an older binary reports
`parse: Unexpected token: expected identifier, found Admit`.

This spec deliberately does NOT assert that the proof statements stopped
working -- the last scenario proves the keyword meaning survives in statement
position, which is the only place it was ever meant to apply.

See doc/08_tracking/bug/admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21.md

## Scenarios

### admit and assume as ordinary identifiers

#### declares and calls module-level functions named admit and assume

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares and calls module-level functions named admit and assume
- Call a module-level `pub fn admit(...)` -- the D4 loader-admission shape
   - Expected: admit(41) equals `42`
- Same for `assume`
   - Expected: assume(21) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares and calls module-level functions named admit and assume")
step("Call a module-level `pub fn admit(...)` -- the D4 loader-admission shape")
expect(admit(41)).to_equal(42)

step("Same for `assume`")
expect(assume(21)).to_equal(42)
```

</details>

#### binds local variables named admit and assume

- binds local variables named admit and assume
- Declare them -- the declaration name goes through expect_identifier
- Read them in expression position -- the position that used to fail
   - Expected: admit + 1 equals `6`
   - Expected: 2 + assume equals `9`
   - Expected: admit * assume equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds local variables named admit and assume")
step("Declare them -- the declaration name goes through expect_identifier")
val admit = 5
val assume = 7

step("Read them in expression position -- the position that used to fail")
expect(admit + 1).to_equal(6)
expect(2 + assume).to_equal(9)
expect(admit * assume).to_equal(35)
```

</details>

#### passes them as arguments and reassigns them

- passes them as arguments and reassigns them
   - Expected: admit equals `10`
- Pass a variable named admit to a function
   - Expected: str(admit) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes them as arguments and reassigns them")
var admit = 1
admit = admit * 10
expect(admit).to_equal(10)

step("Pass a variable named admit to a function")
expect(str(admit)).to_equal("10")
```

</details>

#### still runs `assume` as a proof statement

- still runs `assume` as a proof statement
- Statement position keeps the keyword meaning; this must not error
   - Expected: 1 + 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still runs `assume` as a proof statement")
step("Statement position keeps the keyword meaning; this must not error")
assume true
expect(1 + 1).to_equal(2)
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
- `REQ-PARSER-CONTEXTUAL-ADMIT-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6edf46b9de7a4462b0af4931d281727be17ddb1728b1376aa56c9057a7b2d03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6edf46b9de7a4462b0af4931d281727be17ddb1728b1376aa56c9057a7b2d03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6edf46b9de7a4462b0af4931d281727be17ddb1728b1376aa56c9057a7b2d03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares and calls module-level functions named admit and assume' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds local variables named admit and assume' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_admit_assume_contextual_keyword_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes them as arguments and reassigns them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
