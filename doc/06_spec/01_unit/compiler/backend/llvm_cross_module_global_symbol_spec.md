# Llvm Cross Module Global Symbol Specification

> Tests covering llvm cross-module global symbol references.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Cross Module Global Symbol Specification

## Scenarios

### llvm cross-module global symbol references

#### lint model classes are defined under their canonical names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lint model classes are defined under their canonical names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lint model classes are defined under their canonical names")
extern fn rt_file_read_text(path: text) -> text
val model = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/config_and_model.spl") ?? ""
expect(model.len()).to_be_greater_than(0)
expect(model).to_contain("class LintDiag:")
expect(model).to_contain("class LintRunResult:")
# The retired bare names are easy_fix's old ones; they must not return.
expect(model).to_not_contain("class Lint:")
expect(model).to_not_contain("class LintResult:")
```

</details>

#### lint traceability module references only defined lint model classes (repro)

- lint traceability module references only defined lint model classes (repro)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lint traceability module references only defined lint model classes (repro)")
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl") ?? ""
expect(source.len()).to_be_greater_than(0)
expect(source).to_contain("LintDiag")
# The retired bare constructors must never come back.
expect(source).to_not_contain("Lint.new(")
expect(source).to_not_contain("LintResult.new(")
```

</details>

#### lint entry module references only defined lint model classes (2026-08-21 regression)

- lint entry module references only defined lint model classes (2026-08-21 regression)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lint entry module references only defined lint model classes (2026-08-21 regression)")
# entry_and_fixes.spl and lint_checks.spl were reverted to the retired
# bare names after config_and_model.spl had moved to LintDiag /
# LintRunResult, so `simple test` on any spec that loads the lint chain
# died with `semantic: variable Lint not found`.
extern fn rt_file_read_text(path: text) -> text
val entry = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl") ?? ""
expect(entry.len()).to_be_greater_than(0)
expect(entry).to_contain("LintDiag.new(")
expect(entry).to_contain("LintRunResult.new(")
expect(entry).to_not_contain("Lint.new(")
expect(entry).to_not_contain("LintResult.new(")
```

</details>

#### lint checks module references only defined lint model classes (generalization)

- lint checks module references only defined lint model classes (generalization)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lint checks module references only defined lint model classes (generalization)")
# Same defect class, second call-site file carrying the same revert.
extern fn rt_file_read_text(path: text) -> text
val checks = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/lint_checks.spl") ?? ""
expect(checks.len()).to_be_greater_than(0)
expect(checks).to_contain("LintDiag.new(")
expect(checks).to_contain("LintRunResult.new(")
expect(checks).to_not_contain("Lint.new(")
expect(checks).to_not_contain("LintResult.new(")
```

</details>

#### easy_fix keeps the de-collided class names (generalization)

- easy_fix keeps the de-collided class names (generalization)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("easy_fix keeps the de-collided class names (generalization)")
# The other half of the 9728f2ac2e7 rename: if easy_fix reclaims the bare
# names, the cross-module collision the rename removed comes straight back.
extern fn rt_file_read_text(path: text) -> text
val types = rt_file_read_text("src/lib/nogc_sync_mut/tooling/easy_fix/types.spl") ?? ""
expect(types.len()).to_be_greater_than(0)
expect(types).to_contain("class EasyFixLint:")
expect(types).to_not_contain("class Lint:")
expect(types).to_not_contain("class LintResult:")
```

</details>

#### llvm-lib backend keeps the undeclared-global-load diagnostic (generalization)

- llvm-lib backend keeps the undeclared-global-load diagnostic (generalization)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("llvm-lib backend keeps the undeclared-global-load diagnostic (generalization)")
# The backend check that surfaced this bug must stay: a global load of a
# symbol with no emitted declaration is a semantic error, not silent UB.
extern fn rt_file_read_text(path: text) -> text
val src = rt_file_read_text("src/compiler_rust/compiler/src/codegen/llvm/functions.rs") ?? ""
expect(src).to_contain("llvm global load referenced undeclared symbol")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering llvm cross-module global symbol references.
- llvm cross-module global symbol references

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `6579209c7b78d4849b587214403357f7519c056e4c6bd4b223840f7d6579e3ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6579209c7b78d4849b587214403357f7519c056e4c6bd4b223840f7d6579e3ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6579209c7b78d4849b587214403357f7519c056e4c6bd4b223840f7d6579e3ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lint model classes are defined under their canonical names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lint traceability module references only defined lint model classes (repro)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_cross_module_global_symbol_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lint entry module references only defined lint model classes (2026-08-21 regression)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
