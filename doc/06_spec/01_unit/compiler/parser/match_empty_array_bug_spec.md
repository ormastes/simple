# Match Empty Array Bug Specification

> Tests covering Match Empty Array Bug, Related Patterns, Bug Impact, Expected Behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Empty Array Bug Specification

## Scenarios

### Match Empty Array Bug

#### reproduces parser error with direct [] return

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reproduces parser error with direct [] return


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reproduces parser error with direct [] return")
# This pattern causes parse error during module loading:
# fn get_items(value: TestEnum) -> [i64]:
#     match value:
#         case Empty: []        <- PARSE ERROR
#         case Single(x): [x]
#         case Multiple(x, y): [x, y]

# Workaround: Assign to variable first
fn get_items_workaround(value: TestEnum) -> [i64]:
    match value:
        case Empty:
            val empty: [i64] = []
            empty
        case Single(x):
            [x]
        case Multiple(x, y):
            [x, y]

val result = get_items_workaround(TestEnum.Empty)
expect result.len() == 0
```

</details>

#### works with non-empty array literal

- works with non-empty array literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("works with non-empty array literal")
fn get_items(value: TestEnum) -> [i64]:
    match value:
        case Empty:
            [0]        # Non-empty works fine
        case Single(x):
            [x]
        case Multiple(x, y):
            [x, y]

val result = get_items(TestEnum.Empty)
expect result.len() == 1
```

</details>

#### works when assigning to variable first

- works when assigning to variable first


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("works when assigning to variable first")
fn get_items(value: TestEnum) -> [i64]:
    val result = match value:
        case Empty:
            val empty: [i64] = []
            empty
        case Single(x): [x]
        case Multiple(x, y): [x, y]
    result

val items = get_items(TestEnum.Empty)
expect items.len() == 0
```

</details>

### Related Patterns

#### direct nil return works

- direct nil return works


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("direct nil return works")
fn get_optional(flag: bool) -> i64?:
    match flag:
        case true: Some(42)
        case false: nil    # nil works fine

val result = get_optional(false)
expect not result.?
```

</details>

#### direct empty string works

- direct empty string works


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("direct empty string works")
fn get_text(flag: bool) -> text:
    match flag:
        case true: "hello"
        case false: ""     # Empty string works fine

val result = get_text(false)
expect result.len() == 0
```

</details>

#### direct empty dict might fail

- direct empty dict might fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("direct empty dict might fail")
# This might also fail - needs testing
fn get_dict(flag: bool) -> Dict<text, i64>:
    match flag:
        case true: {"key": 42}
        case false:
            val empty: Dict<text, i64> = {}
            empty  # Using workaround

val result = get_dict(false)
expect result.len() == 0
```

</details>

### Bug Impact

#### affects function returning arrays

- affects function returning arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("affects function returning arrays")
# Pattern used in loop_opt.spl:142-160
# fn get_successors(term: MirTerminator) -> [BlockId]:
#     match term:
#         case Return(_): []      <- BLOCKS MODULE LOADING
#         case Unreachable: []    <- BLOCKS MODULE LOADING
#         case _: []              <- BLOCKS MODULE LOADING

expect true  # Documenting the issue
```

</details>

#### workaround adds 2 extra lines per empty case

- workaround adds 2 extra lines per empty case


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("workaround adds 2 extra lines per empty case")
# Instead of:
#   case Empty: []
#
# Need:
#   case Empty:
#       val empty: [T] = []
#       empty

expect true  # Documenting workaround cost
```

</details>

### Expected Behavior

#### should allow direct [] return like other literals

- should allow direct [] return like other literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should allow direct [] return like other literals")
# These all work:
# case X: 42           # Direct integer literal
# case X: "text"       # Direct string literal
# case X: true         # Direct boolean literal
# case X: [1, 2, 3]    # Non-empty array literal
#
# This should also work:
# case X: []           # Empty array literal <- BUG

expect true  # Documenting expected behavior
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/match_empty_array_bug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Match Empty Array Bug, Related Patterns, Bug Impact, Expected Behavior.
- Match Empty Array Bug
- Related Patterns
- Bug Impact
- Expected Behavior

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d0369bf4bc88456b8294b3652eb92e0575ea984689b862b6702218fce01ec9ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0369bf4bc88456b8294b3652eb92e0575ea984689b862b6702218fce01ec9ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0369bf4bc88456b8294b3652eb92e0575ea984689b862b6702218fce01ec9ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/compiler/parser/match_empty_array_bug_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/match_empty_array_bug_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/match_empty_array_bug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/match_empty_array_bug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/match_empty_array_bug_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduces parser error with direct [] return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/match_empty_array_bug_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with non-empty array literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/match_empty_array_bug_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works when assigning to variable first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/match_empty_array_bug_spec.spl:160:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow direct [] return like other literals' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
