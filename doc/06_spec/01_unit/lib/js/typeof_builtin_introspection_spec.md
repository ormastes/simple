# Typeof Builtin Introspection Specification

> Tests covering JS engine typeof introspection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typeof Builtin Introspection Specification

## Scenarios

### JS engine typeof introspection

#### reports Promise as function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports Promise as function
   - Expected: eval_str("typeof Promise") equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Promise as function")
expect(eval_str("typeof Promise")).to_equal("function")
```

</details>

#### reports array prototype methods as function

- reports array prototype methods as function
   - Expected: eval_str("typeof [].forEach") equals `function`
   - Expected: eval_str("typeof [1,2].map") equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports array prototype methods as function")
expect(eval_str("typeof [].forEach")).to_equal("function")
expect(eval_str("typeof [1,2].map")).to_equal("function")
```

</details>

#### reports string prototype methods as function

- reports string prototype methods as function
   - Expected: eval_str("typeof ''.replace") equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports string prototype methods as function")
expect(eval_str("typeof ''.replace")).to_equal("function")
```

</details>

#### still reports unknown identifiers and properties as undefined

- still reports unknown identifiers and properties as undefined
   - Expected: eval_str("typeof __no_such_global__") equals `undefined`
   - Expected: eval_str("typeof [].__no_such_method__") equals `undefined`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports unknown identifiers and properties as undefined")
expect(eval_str("typeof __no_such_global__")).to_equal("undefined")
expect(eval_str("typeof [].__no_such_method__")).to_equal("undefined")
```

</details>

#### does not break method calls or basic eval

- does not break method calls or basic eval
   - Expected: eval_str("[1,2,3].map(function(n){return n*2;}).join(',')") equals `2,4,6`
   - Expected: eval_str("'a-b'.replace('-','+')") equals `a+b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not break method calls or basic eval")
expect(eval_str("[1,2,3].map(function(n){return n*2;}).join(',')")).to_equal("2,4,6")
expect(eval_str("'a-b'.replace('-','+')")).to_equal("a+b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/typeof_builtin_introspection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS engine typeof introspection.
- JS engine typeof introspection

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `32a141f89a2b57c8b115b1a94d2b925c44f57a001dedc848f27d605513b3fb2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32a141f89a2b57c8b115b1a94d2b925c44f57a001dedc848f27d605513b3fb2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32a141f89a2b57c8b115b1a94d2b925c44f57a001dedc848f27d605513b3fb2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/js/typeof_builtin_introspection_spec.spl
mirror: doc/06_spec/01_unit/lib/js/typeof_builtin_introspection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/js/typeof_builtin_introspection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/js/typeof_builtin_introspection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/js/typeof_builtin_introspection_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Promise as function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/typeof_builtin_introspection_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports array prototype methods as function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/typeof_builtin_introspection_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports string prototype methods as function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
