# String methods on named receivers must see the receiver, not fold into the call name

> Two related JIT/native defects, both re-verified fixed on 2026-08-09 against the currently-deployed seed binary (`bin/release/x86_64-unknown-linux-gnu/simple`):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String methods on named receivers must see the receiver, not fold into the call name

Two related JIT/native defects, both re-verified fixed on 2026-08-09 against the currently-deployed seed binary (`bin/release/x86_64-unknown-linux-gnu/simple`):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Parser / HIR return-type inference parity (compiled lanes) |
| Status | Active |
| Source | `test/01_unit/compiler/jit_string_method_receiver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Two related JIT/native defects, both re-verified fixed on 2026-08-09 against
the currently-deployed seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`):

1. A string method called on a `val`/`var`/module-level receiver whose name
   starts with an **uppercase letter** (e.g. `val T = "ABCDEF"`) used to be
   folded by an old parser heuristic into a bare call name (`"T.char_at"`),
   discarding the receiver entirely and returning empty/garbage. Fixed at the
   parser (`is_type_path()` heuristic removed,
   `src/compiler_rust/parser/src/expressions/postfix.rs`).
2. `.length()` (as opposed to `.len()`) on a string receiver — including a
   `var` reassigned inside a `while` loop — used to return a wrong/garbage
   value (`0.0`, or `nil` inside the loop) because HIR return-type inference
   was missing the `"length"` alias, leaving the call typed `ANY` instead of
   `I64` and skipping int-boxing before print. Fixed by adding `"length"`
   alongside `"len"` in the HIR method return-type tables
   (`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`).

The tree-walking interpreter was always correct for both symptoms, so this
spec is non-gating under `bin/simple test` (interpreter lane) — it passed on
the OLD, buggy seed too. The real regression gate is the **compiled** lane:
`bin/simple run <file>.spl` (Cranelift JIT) or `bin/simple compile --native`.
Re-run this file's assertions through those lanes to actually exercise the
fix; see `.claude/rules/testing.md` "`run` and `test` are DIFFERENT ENGINES".

## Syntax

```simple
use std.spec.step

val T = "ABCDEF"
print(T.char_at(0))   # must be "A", not empty
```

## Scenarios

### string methods on an uppercase-named receiver keep the receiver

#### char_at sees the receiver instead of folding into the call name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### length() on an uppercase local returns the real length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(uppercase_local_length(), 6)
```

</details>

#### char_at works the same for a module-level uppercase receiver

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(uppercase_module_char_at(), "A")
```

</details>

### length() stays correct across reassignment inside a loop

#### returns the reassigned string's length on every iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lowercase_local_length_loop(), 1)
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

- Canonical SPipe generation for source `2c4f1a5cc69026da53bde9e2d5cd79c1d5f987c19a1a60adf3b1f63a401aa95d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c4f1a5cc69026da53bde9e2d5cd79c1d5f987c19a1a60adf3b1f63a401aa95d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c4f1a5cc69026da53bde9e2d5cd79c1d5f987c19a1a60adf3b1f63a401aa95d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/jit_string_method_receiver_spec.spl
mirror: doc/06_spec/01_unit/compiler/jit_string_method_receiver_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/jit_string_method_receiver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/jit_string_method_receiver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/jit_string_method_receiver_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/jit_string_method_receiver_spec.spl:78:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'char_at sees the receiver instead of folding into the call name' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/jit_string_method_receiver_spec.spl:83:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'length() on an uppercase local returns the real length' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/jit_string_method_receiver_spec.spl:86:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'char_at works the same for a module-level uppercase receiver' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/jit_string_method_receiver_spec.spl:90:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns the reassigned string's length on every iteration' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
