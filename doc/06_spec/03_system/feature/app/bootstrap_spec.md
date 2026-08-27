# Bootstrap Self-Compilation

> Tests the bootstrap self-compilation pipeline with lightweight doubles. Verifies that the staged bootstrap process (Rust seed to Simple compiler to self-hosted binary) correctly progresses through each compilation stage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Self-Compilation

Tests the bootstrap self-compilation pipeline with lightweight doubles. Verifies that the staged bootstrap process (Rust seed to Simple compiler to self-hosted binary) correctly progresses through each compilation stage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/bootstrap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the bootstrap self-compilation pipeline with lightweight doubles. Verifies
that the staged bootstrap process (Rust seed to Simple compiler to self-hosted
binary) correctly progresses through each compilation stage.

## Scenarios

### Bootstrap Self-Compilation

#### lexes compiler source into a stable token summary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lexes compiler source into a stable token summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lexes compiler source into a stable token summary")
val source = "fn main(): 42"
val tokens = fake_lex(source)
check(tokens == "tokens:13")
```

</details>

#### parses source into a stable AST summary

- parses source into a stable AST summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses source into a stable AST summary")
val source = "fn main(): 42"
val ast = fake_parse(source)
check(ast == "ast:tokens:13")
```

</details>

#### lowers parsed source into a stable HIR summary

- lowers parsed source into a stable HIR summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lowers parsed source into a stable HIR summary")
val source = "fn main(): 42"
val hir = fake_lower(fake_parse(source))
check(hir == "hir:ast:tokens:13")
```

</details>

#### generates a stable binary summary

- generates a stable binary summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates a stable binary summary")
val source = "fn main(): 42"
val bin = fake_codegen(fake_lower(fake_parse(source)))
check(bin == "bin:hir:ast:tokens:13")
```

</details>

#### bootstrap output is stable across repeated runs

- bootstrap output is stable across repeated runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bootstrap output is stable across repeated runs")
val source = "fn bootstrap(): 1"
check(generation_pair(source))
```

</details>

#### bootstrap rejects empty source

- bootstrap rejects empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bootstrap rejects empty source")
val source = ""
val boot = fake_bootstrap(source)
check(boot == "mir-error")
```

</details>

#### bootstrap summarizes two generations identically

- bootstrap summarizes two generations identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bootstrap summarizes two generations identically")
val source = "fn self_compile(): 7"
val first = fake_bootstrap(source)
val second = fake_bootstrap(source)
check(first == second)
```

</details>

#### supports a larger source fixture

- supports a larger source fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports a larger source fixture")
val source = "fn outer():\n    val x = 1\n    val y = 2\n    x + y"
val boot = fake_bootstrap(source)
check(boot.starts_with("bin:"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6d66f11c5009e1572be5c3a3ce49d2525c08747220b3e51fc7957a3e625e9091`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d66f11c5009e1572be5c3a3ce49d2525c08747220b3e51fc7957a3e625e9091`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d66f11c5009e1572be5c3a3ce49d2525c08747220b3e51fc7957a3e625e9091`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/bootstrap_spec.spl
mirror: doc/06_spec/03_system/feature/app/bootstrap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/bootstrap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/bootstrap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/bootstrap_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes compiler source into a stable token summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/bootstrap_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses source into a stable AST summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/bootstrap_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers parsed source into a stable HIR summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
