# template_kind_can_follow_spec

> Purpose: Regression-pin the macro matcher fragment ordering predicate kind_can_follow

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# template_kind_can_follow_spec

Purpose: Regression-pin the macro matcher fragment ordering predicate kind_can_follow

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/macros/template_kind_can_follow_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Regression-pin the macro matcher fragment ordering predicate kind_can_follow
(start-any, no-expr/stmt-follow rules) after the impl->free-function refactor dropped its body.
Audience: compiler semantics engineers who own macro_check/template.spl.

## Scenarios

### kind_can_follow

#### allows any fragment kind to start a matcher (no previous kind)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows any fragment kind to start a matcher (no previous kind)
   - Expected: kind_can_follow(FragmentKind.Expr, nil) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows any fragment kind to start a matcher (no previous kind)")
expect(kind_can_follow(FragmentKind.Expr, nil)).to_equal(true)
```

</details>

#### forbids anything from directly following an expr fragment

- forbids anything from directly following an expr fragment
   - Expected: kind_can_follow(FragmentKind.Ident, FragmentKind.Expr) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("forbids anything from directly following an expr fragment")
expect(kind_can_follow(FragmentKind.Ident, FragmentKind.Expr)).to_equal(false)
```

</details>

#### forbids anything from directly following a stmt fragment

- forbids anything from directly following a stmt fragment
   - Expected: kind_can_follow(FragmentKind.Ident, FragmentKind.Stmt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("forbids anything from directly following a stmt fragment")
expect(kind_can_follow(FragmentKind.Ident, FragmentKind.Stmt)).to_equal(false)
```

</details>

#### allows a fragment to follow an unambiguous fragment kind

- allows a fragment to follow an unambiguous fragment kind
   - Expected: kind_can_follow(FragmentKind.Ident, FragmentKind.Ty) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows a fragment to follow an unambiguous fragment kind")
expect(kind_can_follow(FragmentKind.Ident, FragmentKind.Ty)).to_equal(true)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `314f6ac7f57a61be7258e0f4fd7d96452bd229ec1ab1cbe65872afcba9f7803a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `314f6ac7f57a61be7258e0f4fd7d96452bd229ec1ab1cbe65872afcba9f7803a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `314f6ac7f57a61be7258e0f4fd7d96452bd229ec1ab1cbe65872afcba9f7803a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/macros/template_kind_can_follow_spec.spl
mirror: doc/06_spec/01_unit/compiler/macros/template_kind_can_follow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/macros/template_kind_can_follow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/macros/template_kind_can_follow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows any fragment kind to start a matcher (no previous kind)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids anything from directly following an expr fragment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids anything from directly following a stmt fragment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
