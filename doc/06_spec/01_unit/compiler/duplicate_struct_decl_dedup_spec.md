# Duplicate Struct Decl Dedup Specification

> Tests covering duplicate struct declaration dedupe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Struct Decl Dedup Specification

## Scenarios

### duplicate struct declaration dedupe

#### keeps exactly one CompileOptions: the driver one (with `mode`)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps exactly one CompileOptions: the driver one (with `mode`)
   - Expected: driver contains `struct CompileOptions:`
   - Expected: driver contains `mode: CompileMode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps exactly one CompileOptions: the driver one (with `mode`)")
val driver = file_read("src/compiler/00.common/driver_compile_options.spl")
expect(driver.contains("struct CompileOptions:")).to_equal(true)
expect(driver.contains("mode: CompileMode")).to_equal(true)
```

</details>

#### backend options struct is BackendCompileOptions, not CompileOptions

- backend options struct is BackendCompileOptions, not CompileOptions
   - Expected: backend contains `struct BackendCompileOptions:`
   - Expected: backend does not contain `struct CompileOptions:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("backend options struct is BackendCompileOptions, not CompileOptions")
val backend = file_read("src/compiler/70.backend/backend/backend_types.spl")
expect(backend.contains("struct BackendCompileOptions:")).to_equal(true)
expect(backend.contains("struct CompileOptions:")).to_equal(false)
```

</details>

#### frontend options struct is FrontendCompileOptions, not CompileOptions

- frontend options struct is FrontendCompileOptions, not CompileOptions
   - Expected: frontend contains `struct FrontendCompileOptions:`
   - Expected: frontend does not contain `struct CompileOptions:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frontend options struct is FrontendCompileOptions, not CompileOptions")
val frontend = file_read("src/compiler/10.frontend/core/backend_types.spl")
expect(frontend.contains("struct FrontendCompileOptions:")).to_equal(true)
expect(frontend.contains("struct CompileOptions:")).to_equal(false)
```

</details>

#### sdn source span is SdnSpan, not Span

- sdn source span is SdnSpan, not Span
   - Expected: sdn contains `class SdnSpan:`
   - Expected: sdn does not contain `class Span:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sdn source span is SdnSpan, not Span")
val sdn = file_read("src/lib/common/sdn/value.spl")
expect(sdn.contains("class SdnSpan:")).to_equal(true)
expect(sdn.contains("class Span:")).to_equal(false)
```

</details>

#### web_framework tracing span is TraceSpan, not Span

- web_framework tracing span is TraceSpan, not Span
   - Expected: tracing contains `class TraceSpan:`
   - Expected: tracing does not contain `class Span:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("web_framework tracing span is TraceSpan, not Span")
val tracing = file_read("src/lib/nogc_sync_mut/web_framework/tracing.spl")
expect(tracing.contains("class TraceSpan:")).to_equal(true)
expect(tracing.contains("class Span:")).to_equal(false)
```

</details>

#### compute container span is ComputeSpan, not Span

- compute container span is ComputeSpan, not Span
   - Expected: containers contains `class ComputeSpan<T>:`
   - Expected: containers does not contain `class Span<T>:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute container span is ComputeSpan, not Span")
val containers = file_read("src/lib/nogc_async_mut/compute/containers.spl")
expect(containers.contains("class ComputeSpan<T>:")).to_equal(true)
expect(containers.contains("class Span<T>:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/duplicate_struct_decl_dedup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering duplicate struct declaration dedupe.
- duplicate struct declaration dedupe

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

- Canonical SPipe generation for source `613e11748d41f169e234286b96b274a1c82c8f1245aff4b3998d4e3acfde0351`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `613e11748d41f169e234286b96b274a1c82c8f1245aff4b3998d4e3acfde0351`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `613e11748d41f169e234286b96b274a1c82c8f1245aff4b3998d4e3acfde0351`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/duplicate_struct_decl_dedup_spec.spl
mirror: doc/06_spec/01_unit/compiler/duplicate_struct_decl_dedup_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/duplicate_struct_decl_dedup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/duplicate_struct_decl_dedup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/duplicate_struct_decl_dedup_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps exactly one CompileOptions: the driver one (with `mode`)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/duplicate_struct_decl_dedup_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backend options struct is BackendCompileOptions, not CompileOptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/duplicate_struct_decl_dedup_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'frontend options struct is FrontendCompileOptions, not CompileOptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
