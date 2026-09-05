# Convert Nodes Loud Fallback Specification

> Tests covering convert_nodes.spl generic node-kind fallback is loud, not silent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Convert Nodes Loud Fallback Specification

## Scenarios

### convert_nodes.spl generic node-kind fallback is loud, not silent

#### keeps unsupported nested defer wired to the loud marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps unsupported nested defer wired to the loud marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps unsupported nested defer wired to the loud marker")
val bridge = rt_file_read_text(
    "src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl") ?? ""
expect(bridge).to_contain(
    "fn defer_unsupported_marker(span: Span) -> Stmt:")
```

</details>

#### converts a real spawn(...) call expression through its own arm, no loud fallback (EXPR_SPAWN)

- converts a real spawn(...) call expression through its own arm, no loud fallback (EXPR_SPAWN)


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts a real spawn(...) call expression through its own arm, no loud fallback (EXPR_SPAWN)")
# UPDATED 2026-08-21: this example used to assert the OPPOSITE --
# that `spawn(w)` still hit the generic loud fallback. That was the
# pre-fix state. `convert_nodes.spl` now has a dedicated
# `if tag == EXPR_SPAWN:` arm that emits an ordinary Call, so the node
# converts cleanly and no parser error is recorded. Asserting the
# error here made the spec red against correct behaviour. The
# STMT_STATIC_FOR example below remains the live loud-fallback probe.
# Bug: doc/08_tracking/bug/
# convert_nodes_loud_fallback_spawn_expectation_stale_2026-08-21.md
val bridge = rt_file_read_text(
    "src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl") ?? ""
expect(bridge).to_contain("if tag == EXPR_SPAWN:")
val src = "class Worker:\n" +
    "    id: i64\n" +
    "\n" +
    "fn boot(w: Worker):\n" +
    "    spawn(w)\n"
val parsed = parse_full_frontend(src, "testdata/fixture_nil1_spawn.spl", "fixture_nil1_spawn", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### records zero parser errors for an ordinary program using only well-handled node kinds

- records zero parser errors for an ordinary program using only well-handled node kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records zero parser errors for an ordinary program using only well-handled node kinds")
val src = "fn add(a: i64, b: i64) -> i64:\n" +
    "    val sum = a + b\n" +
    "    if sum > 10:\n" +
    "        return sum\n" +
    "    sum\n" +
    "\n" +
    "fn main() -> i64:\n" +
    "    var total = 0\n" +
    "    for i in 0..5:\n" +
    "        total += add(i, 1)\n" +
    "    total\n"
val parsed = parse_full_frontend(src, "testdata/fixture_nil1_ok.spl", "fixture_nil1_ok", Logger(level: 0))
assert_false(parser_has_errors())
```

</details>

#### records a parser error for a real static_for statement (STMT_STATIC_FOR, another unhandled kind with no dispatch arm)

- records a parser error for a real static_for statement (STMT_STATIC_FOR, another unhandled kind with no dispatch arm)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a parser error for a real static_for statement (STMT_STATIC_FOR, another unhandled kind with no dispatch arm)")
val src = "fn sum_all(values: [i64]) -> i64:\n" +
    "    var total = 0\n" +
    "    static_for item in values:\n" +
    "        total = total + item\n" +
    "    total\n"
val parsed = parse_full_frontend(src, "testdata/fixture_nil1_staticfor.spl", "fixture_nil1_staticfor", Logger(level: 0))
assert_true(parser_has_errors())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering convert_nodes.spl generic node-kind fallback is loud, not silent.
- convert_nodes.spl generic node-kind fallback is loud, not silent

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

- Canonical SPipe generation for source `17ed9ed40fa653478e02505dc60b596f8be2dbef1e2b09489424f4479766f415`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17ed9ed40fa653478e02505dc60b596f8be2dbef1e2b09489424f4479766f415`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17ed9ed40fa653478e02505dc60b596f8be2dbef1e2b09489424f4479766f415`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps unsupported nested defer wired to the loud marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts a real spawn(...) call expression through its own arm, no loud fallback (EXPR_SPAWN)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/convert_nodes_loud_fallback_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records zero parser errors for an ordinary program using only well-handled node kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
