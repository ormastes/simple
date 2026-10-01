# Compiler Sffi No Shadow Types Specification

> Tests covering loader compiler_sffi compat surface declares no shadow types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Sffi No Shadow Types Specification

## Scenarios

### loader compiler_sffi compat surface declares no shadow types

#### the real module still owns the one TypeInfo and CompilerContext definition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the real module still owns the one TypeInfo and CompilerContext definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the real module still owns the one TypeInfo and CompilerContext definition")
val real_src = real_text()
expect(real_src).to_contain("struct TypeInfo:")
expect(real_src).to_contain("struct CompilerContext:")
```

</details>

#### the compat module does not redeclare TypeInfo

- the compat module does not redeclare TypeInfo
   - Expected: compat does not contain `class TypeInfo:`
   - Expected: compat does not contain `struct TypeInfo:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the compat module does not redeclare TypeInfo")
val compat = compat_text()
expect(compat.contains("class TypeInfo:")).to_equal(false)
expect(compat.contains("struct TypeInfo:")).to_equal(false)
```

</details>

#### the compat module does not redeclare CompilerContext

- the compat module does not redeclare CompilerContext
   - Expected: compat does not contain `class CompilerContext:`
   - Expected: compat does not contain `struct CompilerContext:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the compat module does not redeclare CompilerContext")
val compat = compat_text()
expect(compat.contains("class CompilerContext:")).to_equal(false)
expect(compat.contains("struct CompilerContext:")).to_equal(false)
```

</details>

#### the compat module re-exports the real definitions instead

- the compat module re-exports the real definitions instead


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the compat module re-exports the real definitions instead")
val compat = compat_text()
expect(compat).to_contain("export use compiler.loader.loader.compiler_sffi.")
expect(compat).to_contain("TypeInfo, CompilerContext,")
```

</details>

#### the compat module no longer shadows the real sffi entry points with stubs

- the compat module no longer shadows the real sffi entry points with stubs
   - Expected: compat does not contain `fn compiler_create_context() -> i64:`
   - Expected: compat does not contain `fn make_named_type(name: text) -> TypeInfo:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the compat module no longer shadows the real sffi entry points with stubs")
val compat = compat_text()
expect(compat.contains("fn compiler_create_context() -> i64:")).to_equal(false)
expect(compat.contains("fn make_named_type(name: text) -> TypeInfo:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering loader compiler_sffi compat surface declares no shadow types.
- loader compiler_sffi compat surface declares no shadow types

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

- Canonical SPipe generation for source `8b6845442d0d606871b4bea933ac8df7893f48064a806eb5691a83ddb9ac5580`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b6845442d0d606871b4bea933ac8df7893f48064a806eb5691a83ddb9ac5580`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b6845442d0d606871b4bea933ac8df7893f48064a806eb5691a83ddb9ac5580`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.spl
mirror: doc/06_spec/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the real module still owns the one TypeInfo and CompilerContext definition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the compat module does not redeclare TypeInfo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/compiler_sffi_no_shadow_types_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the compat module does not redeclare CompilerContext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
