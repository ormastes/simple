# Jit Compilation Context Specification

> Tests covering Jit Compilation Context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Compilation Context Specification

## Scenarios

### Jit Compilation Context

#### loads existing templates from SMF state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads existing templates from SMF state
   - Expected: ctx.has_template("Vec") is true
   - Expected: ctx.has_template("Map") is false
   - Expected: ctx.load_template("Vec").is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads existing templates from SMF state")
var templates: Dict<text, TemplateBytes> = {}
templates["Vec"] = build_template("Vec", 1)
val ctx = JitCompilationContext.from_smf(templates)

expect(ctx.has_template("Vec")).to_equal(true)
expect(ctx.has_template("Map")).to_equal(false)
expect(ctx.load_template("Vec").is_ok()).to_equal(true)
```

</details>

#### reports boundary contract mode and jit_time instantiation

- reports boundary contract mode and jit_time instantiation
   - Expected: ctx.contract_mode() equals `boundary`
   - Expected: ctx.coverage_enabled() is false
   - Expected: ctx.instantiation_mode() equals `jit_time`
   - Expected: ctx.di_container() != nil is false
   - Expected: ctx.aop_weaver() != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports boundary contract mode and jit_time instantiation")
val ctx = JitCompilationContext.from_smf({})
expect(ctx.contract_mode()).to_equal("boundary")
expect(ctx.coverage_enabled()).to_equal(false)
expect(ctx.instantiation_mode()).to_equal("jit_time")
expect(ctx.di_container() != nil).to_equal(false)
expect(ctx.aop_weaver() != nil).to_equal(false)
```

</details>

#### compiles a template into a mangled specialized unit

- compiles a template into a mangled specialized unit
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().name equals `List$Int`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles a template into a mangled specialized unit")
var templates: Dict<text, TemplateBytes> = {}
templates["List"] = build_template("List", 1)
val ctx = JitCompilationContext.from_smf(templates)
val tmpl = ctx.load_template("List").unwrap()

val result = ctx.compile_template(tmpl, [make_named_type("Int")])
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().name).to_equal("List$Int")
expect(result.unwrap().bytes.len()).to_be_greater_than(0)
```

</details>

#### records instantiation attempts

- records instantiation attempts
   - Expected: ctx.recorded.len() equals `1`
   - Expected: ctx.recorded[0].mangled_name equals `Result$String`
   - Expected: ctx.recorded[0].success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records instantiation attempts")
var ctx = JitCompilationContext.from_smf({})
ctx.record_instantiation("Result", [make_named_type("String")], "Result$String", true, nil)

expect(ctx.recorded.len()).to_equal(1)
expect(ctx.recorded[0].mangled_name).to_equal("Result$String")
expect(ctx.recorded[0].success).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/jit_compilation_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Jit Compilation Context.
- Jit Compilation Context

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

- Canonical SPipe generation for source `fd87285e82683ef6251e1d132b86cb4c93cae67612b14e4c1d5b9160da17dbaf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd87285e82683ef6251e1d132b86cb4c93cae67612b14e4c1d5b9160da17dbaf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd87285e82683ef6251e1d132b86cb4c93cae67612b14e4c1d5b9160da17dbaf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/loader/jit_compilation_context_spec.spl
mirror: doc/06_spec/unit/compiler/loader/jit_compilation_context_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/jit_compilation_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/jit_compilation_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/jit_compilation_context_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/loader/jit_compilation_context_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads existing templates from SMF state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/jit_compilation_context_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports boundary contract mode and jit_time instantiation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/jit_compilation_context_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles a template into a mangled specialized unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
