# Chained Text Builtin To Int Specification

> Tests covering a chained text builtin feeding .to_i64().

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chained Text Builtin To Int Specification

## Scenarios

### a chained text builtin feeding .to_i64()

#### parses the trimmed text instead of returning its heap pointer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the trimmed text instead of returning its heap pointer
- Run the run-path probe under the cranelift JIT
- The unchained control arm already worked and must keep working
-   42


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the trimmed text instead of returning its heap pointer")
step("Run the run-path probe under the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("The unchained control arm already worked and must keep working")
expect(jit).to_contain("PASS text_to_i64_direct")

step('"  42  ".trim().to_i64() must be 42, not a heap address')
expect(jit).to_contain("PASS text_to_i64_after_trim")
```

</details>

#### generalises to the other text-only text-returning builtins

- generalises to the other text-only text-returning builtins
- to_upper and replace return text on a text receiver and on no other receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generalises to the other text-only text-returning builtins")
val jit = run_probe_in_mode("jit")

step("to_upper and replace return text on a text receiver and on no other receiver")
expect(jit).to_contain("PASS text_to_i64_after_upper")
expect(jit).to_contain("PASS text_to_i64_after_replace")
```

</details>

#### agrees with the interpreter, which decodes tags dynamically

- agrees with the interpreter, which decodes tags dynamically


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the interpreter, which decodes tags dynamically")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PASS text_to_i64_after_trim")
expect(interp).to_contain("PASS text_to_i64_after_upper")
expect(interp).to_contain("PASS text_to_i64_after_replace")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering a chained text builtin feeding .to_i64().
- a chained text builtin feeding .to_i64()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `c6111fb9cb5b67d0521789b09379db7c61f75345310b47b26650ea52f8b98e7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6111fb9cb5b67d0521789b09379db7c61f75345310b47b26650ea52f8b98e7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6111fb9cb5b67d0521789b09379db7c61f75345310b47b26650ea52f8b98e7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the trimmed text instead of returning its heap pointer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generalises to the other text-only text-returning builtins' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_text_builtin_to_int_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the interpreter, which decodes tags dynamically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
