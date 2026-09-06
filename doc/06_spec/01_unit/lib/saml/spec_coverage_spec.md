# Spec Coverage Specification

> Tests covering discover_spec_coverage — positive binding, discover_spec_coverage — must NOT bind.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Coverage Specification

## Scenarios

### discover_spec_coverage — positive binding

#### binds a plain call site inside an it block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds a plain call site inside an it block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a plain call site inside an it block")
val src = "describe \"d\":\n    it \"does the thing\":\n        val r = Extract(\"x\")\n        check(r != nil)\n"
val out = discover_spec_coverage(["Extract"], ["test/a_spec.spl"], [src])
check_msg(out.len() == 1, "expected exactly one binding, got " + out.len().to_text())
check_msg(has_entry(out, "Extract\texternal:test/a_spec.spl:does the thing"), "expected the binding to name the it title")
```

</details>

#### binds the same function from two different it blocks

- binds the same function from two different it blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds the same function from two different it blocks")
val src = "describe \"d\":\n    it \"case one\":\n        Extract(\"a\")\n    it \"case two\":\n        Extract(\"b\")\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(count_matching(out, "Extract") == 2, "expected two bindings, got " + count_matching(out, "Extract").to_text())
check_msg(has_entry(out, "external:s.spl:case one"), "expected case one to bind")
check_msg(has_entry(out, "external:s.spl:case two"), "expected case two to bind")
```

</details>

#### binds across multiple spec files, keyed by that file's path

- binds across multiple spec files, keyed by that file's path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds across multiple spec files, keyed by that file's path")
val src_a = "it \"a\":\n    Extract(1)\n"
val src_b = "it \"b\":\n    Score(2)\n"
val out = discover_spec_coverage(["Extract", "Score"], ["a_spec.spl", "b_spec.spl"], [src_a, src_b])
check_msg(has_entry(out, "Extract\texternal:a_spec.spl:a"), "expected Extract bound in a_spec.spl")
check_msg(has_entry(out, "Score\texternal:b_spec.spl:b"), "expected Score bound in b_spec.spl")
```

</details>

#### does not bind an unrelated function name that is not called

- does not bind an unrelated function name that is not called


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not bind an unrelated function name that is not called")
val src = "it \"case\":\n    Extract(1)\n"
val out = discover_spec_coverage(["Score"], ["s.spl"], [src])
check_msg(out.len() == 0, "Score was never called; expected no bindings")
```

</details>

#### binds even with leading whitespace variance on the call line

- binds even with leading whitespace variance on the call line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds even with leading whitespace variance on the call line")
val src = "it \"deep\":\n        val r =    Extract(1)\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(out.len() == 1, "expected binding despite extra whitespace")
```

</details>

#### stops the it-block body at a dedent back to the it line's own indent

- stops the it-block body at a dedent back to the it line's own indent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops the it-block body at a dedent back to the it line's own indent")
val src = "it \"first\":\n    Extract(1)\nit \"second\":\n    Score(2)\n"
val out = discover_spec_coverage(["Extract", "Score"], ["s.spl"], [src])
check_msg(has_entry(out, "external:s.spl:first"), "Extract should bind to first")
check_msg(has_entry(out, "external:s.spl:second"), "Score should bind to second")
check_msg(not has_entry(out, "Extract\texternal:s.spl:second"), "Extract must not leak into the second it block")
```

</details>

### discover_spec_coverage — must NOT bind

#### does not bind a function name that appears only in a comment

- does not bind a function name that appears only in a comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not bind a function name that appears only in a comment")
val src = "it \"case\":\n    # Extract(1) is what this used to call\n    check(true)\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(out.len() == 0, "a commented-out call must not count as coverage")
```

</details>

#### does not bind a function name that appears only inside a string literal

- does not bind a function name that appears only inside a string literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not bind a function name that appears only inside a string literal")
val src = "it \"case\":\n    val msg = \"Extract(1) is not a real call\"\n    check(true)\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(out.len() == 0, "a string literal mention must not count as coverage")
```

</details>

#### does not bind when the name is a substring of a longer identifier

- does not bind when the name is a substring of a longer identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not bind when the name is a substring of a longer identifier")
val src = "it \"case\":\n    val r = MyExtract(1)\n    check(true)\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(out.len() == 0, "MyExtract(...) must not count as a call to Extract")
```

</details>

#### does not bind a call that occurs outside any it block

- does not bind a call that occurs outside any it block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not bind a call that occurs outside any it block")
val src = "val setup = Extract(1)\ndescribe \"d\":\n    it \"case\":\n        check(true)\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(out.len() == 0, "a module-level call outside any it block must not count")
```

</details>

#### does not bind a describe-level call that precedes the first it

- does not bind a describe-level call that precedes the first it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not bind a describe-level call that precedes the first it")
val src = "describe \"d\":\n    val setup = Extract(1)\n    it \"case\":\n        check(true)\n"
val out = discover_spec_coverage(["Extract"], ["s.spl"], [src])
check_msg(out.len() == 0, "a call before the first it: line must not count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/saml/spec_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering discover_spec_coverage — positive binding, discover_spec_coverage — must NOT bind.
- discover_spec_coverage — positive binding
- discover_spec_coverage — must NOT bind

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `ee1f13696aeb64aed78b3c7f2cd9d6a65a57489f0ead83147c1edba0ad40e94c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee1f13696aeb64aed78b3c7f2cd9d6a65a57489f0ead83147c1edba0ad40e94c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee1f13696aeb64aed78b3c7f2cd9d6a65a57489f0ead83147c1edba0ad40e94c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/saml/spec_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/saml/spec_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/saml/spec_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/saml/spec_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/saml/spec_coverage_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds a plain call site inside an it block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/saml/spec_coverage_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the same function from two different it blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/saml/spec_coverage_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds across multiple spec files, keyed by that file's path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
