# Collection Easy Fix Specification

> Tests covering collection lint auto-fix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Easy Fix Specification

## Scenarios

### collection lint auto-fix

#### reports COLL001 on the offending line, not the enclosing function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports COLL001 on the offending line, not the enclosing function
- Lint a function whose loop body grows an array by concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports COLL001 on the offending line, not the enclosing function")
"""A quadratic concat inside a loop should point at the concat itself,
so the reader lands on the defect rather than the function header."""
step("Lint a function whose loop body grows an array by concatenation")
var line = 0
var count = 0
for result in lint_cli_source(Linter.new(), "/tmp/coll_push.spl", CONCAT_SRC):
    if result.lint.code == "COLL001":
        count = count + 1
        line = result.line
assert_equal(count, 1)
# `out = out + [x]` is line 4; `fn build` is line 1.
assert_equal(line, 4)
```

</details>

#### offers a push rewrite that applies cleanly to the source

- offers a push rewrite that applies cleanly to the source
- Collect the COLL001 replacement and splice it into the source
   - Expected: new_text equals `out.push(x)`
- The spliced source keeps the indentation and drops the concat


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("offers a push rewrite that applies cleanly to the source")
"""The fix must be machine-applicable: splicing its replacement into the
original text has to yield working code with the concat gone."""
step("Collect the COLL001 replacement and splice it into the source")
var replacements = 0
var new_text = ""
var applied = ""
for result in lint_cli_source(Linter.new(), "/tmp/coll_push2.spl", CONCAT_SRC):
    if result.lint.code == "COLL001":
        match result.lint.easy_fix:
            case Some(fix):
                for rep in easyfix_replacements(fix):
                    replacements = replacements + 1
                    new_text = rep.new_text
                    applied = CONCAT_SRC.slice(0, rep.start) + rep.new_text + CONCAT_SRC.slice(rep.end)
            case nil:
                val _ = 0
assert_equal(replacements, 1)
expect(new_text).to_equal("out.push(x)")
step("The spliced source keeps the indentation and drops the concat")
expect(applied).to_contain("        out.push(x)\n")
assert_false(applied.contains("out + [x]"))
```

</details>

#### warns without a fix when the concat appends more than one element

- warns without a fix when the concat appends more than one element
- Lint a loop body appending a two-element literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("warns without a fix when the concat appends more than one element")
"""`arr + [a, b]` needs one push per element, which is not a
statement-local rewrite, so the warning stands alone."""
step("Lint a loop body appending a two-element literal")
var warned = false
var replacements = 0
for result in lint_cli_source(Linter.new(), "/tmp/coll_multi.spl", MULTI_SRC):
    if result.lint.code == "COLL001":
        warned = true
        match result.lint.easy_fix:
            case Some(fix):
                replacements = replacements + easyfix_replacements(fix).len()
            case nil:
                val _ = 0
assert_true(warned)
assert_equal(replacements, 0)
```

</details>

#### offers a .pop() rewrite for the array-rebuild-to-pop shape

- offers a .pop() rewrite for the array-rebuild-to-pop shape
- Lint a loop that rebuilds arr via arr[0:arr.len()-1]
   - Expected: new_text equals `arr.pop()`
- The spliced source keeps the indentation and drops the rebuild


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("offers a .pop() rewrite for the array-rebuild-to-pop shape")
"""The bug report and this rule's own header comment wrote the
fixture with `..` (arr[0..arr.len()-1]); that is not valid slice
syntax (`..` builds a Range, not a slice — indexing by one errors
at runtime), so neither the warning nor the fix could ever see it.
The rule fires on the real colon slice form, and the fix must
offer the matching rewrite."""
step("Lint a loop that rebuilds arr via arr[0:arr.len()-1]")
var replacements = 0
var new_text = ""
var applied = ""
for result in lint_cli_source(Linter.new(), "/tmp/coll_pop.spl", POP_SRC):
    if result.lint.code == "COLL007":
        match result.lint.easy_fix:
            case Some(fix):
                for rep in easyfix_replacements(fix):
                    replacements = replacements + 1
                    new_text = rep.new_text
                    applied = POP_SRC.slice(0, rep.start) + rep.new_text + POP_SRC.slice(rep.end)
            case nil:
                val _ = 0
assert_equal(replacements, 1)
expect(new_text).to_equal("arr.pop()")
step("The spliced source keeps the indentation and drops the rebuild")
expect(applied).to_contain("        arr.pop()\n")
assert_false(applied.contains("arr[0:arr.len()-1]"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/collection_easy_fix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering collection lint auto-fix.
- collection lint auto-fix

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `824ddcd92cd9c0147844b9992a28d62ec401ad74a15c037a7a82974d7c46f335`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `824ddcd92cd9c0147844b9992a28d62ec401ad74a15c037a7a82974d7c46f335`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `824ddcd92cd9c0147844b9992a28d62ec401ad74a15c037a7a82974d7c46f335`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/lint/collection_easy_fix_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/collection_easy_fix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/collection_easy_fix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/collection_easy_fix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/collection_easy_fix_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports COLL001 on the offending line, not the enclosing function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/collection_easy_fix_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offers a push rewrite that applies cleanly to the source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/collection_easy_fix_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns without a fix when the concat appends more than one element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
