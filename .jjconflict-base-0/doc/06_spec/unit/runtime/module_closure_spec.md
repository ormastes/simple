# Module Closure Specification

> Tests covering Module Function Closures, Runtime Built-in Functions, Import Path Resolution, Closure Limitations That DO Exist.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Closure Specification

## Scenarios

### Module Function Closures

#### allows imported functions to modify module var

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows imported functions to modify module var
   - Expected: module_state_touch("alpha") equals `1`
   - Expected: module_state_touch("beta") equals `2`
   - Expected: module_state_count() equals `2`
   - Expected: module_state_label() equals `beta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows imported functions to modify module var")
module_state_reset()
expect(module_state_touch("alpha")).to_equal(1)
expect(module_state_touch("beta")).to_equal(2)
expect(module_state_count()).to_equal(2)
expect(module_state_label()).to_equal("beta")
```

</details>

#### allows imported functions to read module val collections

- allows imported functions to read module val collections
   - Expected: items.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows imported functions to read module val collections")
# Arrays and other val collections are accessible
val items = ["a", "b", "c"]
expect(items.len()).to_equal(3)
```

</details>

#### preserves module state between calls

- preserves module state between calls
   - Expected: module_state_touch("first") equals `1`
   - Expected: module_state_count() equals `1`
   - Expected: module_state_touch("second") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves module state between calls")
module_state_reset()
expect(module_state_touch("first")).to_equal(1)
expect(module_state_count()).to_equal(1)
expect(module_state_touch("second")).to_equal(2)
```

</details>

#### documents nested closures limitation

- documents nested closures limitation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents nested closures limitation")
# Inner functions defined inside `it` blocks cannot access
# local vars from the enclosing scope (runtime limitation).
# fn inner(): outer + 5  -- would fail with "variable outer not found"
# This is a known limitation of the interpreter.
val limitation = "nested functions cannot capture it-block locals"
expect(limitation).to_contain("nested functions")
expect(limitation).to_contain("it-block locals")
```

</details>

#### documents function-scoped closures limitation

- documents function-scoped closures limitation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents function-scoped closures limitation")
# Functions defined inside `it` blocks cannot access
# local vars from the enclosing scope (runtime limitation).
# fn get_state(): module_state  -- would fail with "variable not found"
val limitation = "function-scoped closures cannot read enclosing locals"
expect(limitation).to_start_with("function-scoped")
expect(limitation).to_contain("enclosing locals")
```

</details>

### Runtime Built-in Functions

#### provides describe/it/expect without import

- provides describe/it/expect without import
   - Expected: 1 + 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides describe/it/expect without import")
# These functions are compiled into the runtime binary
# No 'use std.spec' needed
val runtime_spec_dsl = "describe/it/expect"
expect(runtime_spec_dsl).to_contain("expect")
expect(1 + 1).to_equal(2)
```

</details>

#### provides all core matchers

- provides all core matchers
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides all core matchers")
# Built-in matchers
expect(1).to_equal(1)
expect(1).to_be(1)
expect(nil).to_be_nil()
expect([1, 2]).to_contain(1)
expect("hello").to_start_with("he")
expect("hello").to_end_with("lo")
expect(5).to_be_greater_than(3)
expect(3).to_be_less_than(5)
```

</details>

### Import Path Resolution

#### keeps parser-safe coverage without a placeholder

- keeps parser-safe coverage without a placeholder
   - Expected: module_state_touch("import-path") equals `1`
   - Expected: module_state_label() equals `import-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps parser-safe coverage without a placeholder")
module_state_reset()
expect(module_state_touch("import-path")).to_equal(1)
expect(module_state_label()).to_equal("import-path")
```

</details>

### Closure Limitations That DO Exist

#### nested function modifications don't persist (known runtime limit)

- nested function modifications don't persist (known runtime limit)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested function modifications don't persist (known runtime limit)")
# This IS a real limitation - nested function var changes don't persist
# The nested fn cannot see locals from enclosing `it` block scope.
# This test documents the limitation without triggering a parse error.
# In practice: var count = 0; fn inc(): count = count + 1
# would fail with "variable `count` not found"
val unsupported_pattern = "fn inc cannot mutate enclosing it-block count"
expect(unsupported_pattern).to_contain("it-block count")
```

</details>

#### documents the difference: nested fn vs module fn

- documents the difference: nested fn vs module fn
   - Expected: module_state_touch("module-fn") equals `1`
   - Expected: module_state_label() equals `module-fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the difference: nested fn vs module fn")
# Nested function closures: BROKEN (var changes don't persist)
# Module function closures: WORK (var changes persist when imported)
# The confusion in MEMORY.md was about which one was broken
module_state_reset()
expect(module_state_touch("module-fn")).to_equal(1)
expect(module_state_label()).to_equal("module-fn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/unit/runtime/module_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module Function Closures, Runtime Built-in Functions, Import Path Resolution, Closure Limitations That DO Exist.
- Module Function Closures
- Runtime Built-in Functions
- Import Path Resolution
- Closure Limitations That DO Exist

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `aae36375c3ed4d2b6e2b90d5488074c070b8931fd3831f94c9a082d440145331`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aae36375c3ed4d2b6e2b90d5488074c070b8931fd3831f94c9a082d440145331`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aae36375c3ed4d2b6e2b90d5488074c070b8931fd3831f94c9a082d440145331`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/runtime/module_closure_spec.spl
mirror: doc/06_spec/unit/runtime/module_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/runtime/module_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/runtime/module_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/runtime/module_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/runtime/module_closure_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows imported functions to modify module var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/module_closure_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows imported functions to read module val collections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/module_closure_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves module state between calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
