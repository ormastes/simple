# Trait Impl Arity Conformance Specification

> Tests covering an impl method must match the trait's parameter count.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Impl Arity Conformance Specification

## Scenarios

### an impl method must match the trait's parameter count

#### rejects an impl whose method takes fewer parameters than the trait declares, on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an impl whose method takes fewer parameters than the trait declares, on the interpreter
- Compile the wrong-arity fixture in its own subprocess, engine pinned to interpreter
- The compiler must report a conformance error naming the method
- The ill-formed program must NOT reach its body — reaching it is the silent wrong result
- A rejected compile must exit non-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an impl whose method takes fewer parameters than the trait declares, on the interpreter")
step("Compile the wrong-arity fixture in its own subprocess, engine pinned to interpreter")
val out = compile_fixture(WRONG_ARITY, "interpreter")

step("The compiler must report a conformance error naming the method")
expect(out).to_contain("greet")

step("The ill-formed program must NOT reach its body — reaching it is the silent wrong result")
expect(out).to_not_contain("FIXTURE_RAN_WRONG_ARITY")

step("A rejected compile must exit non-zero")
expect(out).to_not_contain("EXIT=0")
```

</details>

#### rejects the same impl on the JIT — the engine ordinary programs actually run on

- rejects the same impl on the JIT — the engine ordinary programs actually run on
- Same fixture, same binary, engine pinned to jit
- The JIT must reject it exactly as the interpreter does


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects the same impl on the JIT — the engine ordinary programs actually run on")
# EXPECTED RED as of 2026-08-17. Measured A/B, one binary, one tree, one
# toggle: SIMPLE_EXECUTION_MODE=interpreter rejects (rc=1, correct
# diagnostic); =jit accepts and RUNS the body (rc=0). The conformance
# check lives in interpreter_eval.rs and has no JIT-path counterpart, so
# `bin/simple run` — the default engine — silently executes a
# non-conforming impl. Do not weaken this example to make it green.
step("Same fixture, same binary, engine pinned to jit")
val out = compile_fixture(WRONG_ARITY, "jit")

step("The JIT must reject it exactly as the interpreter does")
expect(out).to_not_contain("FIXTURE_RAN_WRONG_ARITY")
expect(out).to_not_contain("EXIT=0")
```

</details>

#### still accepts a correct impl on both engines — the control arm

- still accepts a correct impl on both engines — the control arm
- A compiler that rejects everything must not pass this spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still accepts a correct impl on both engines — the control arm")
step("A compiler that rejects everything must not pass this spec")
val interp = compile_fixture(CONFORMING, "interpreter")
expect(interp).to_contain("FIXTURE_RAN_CONFORMING")
expect(interp).to_contain("EXIT=0")

val jit = compile_fixture(CONFORMING, "jit")
expect(jit).to_contain("FIXTURE_RAN_CONFORMING")
expect(jit).to_contain("EXIT=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering an impl method must match the trait's parameter count.
- an impl method must match the trait's parameter count

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

- Canonical SPipe generation for source `be33240e8bf8ac0fcc4c0f028ba5173ac80d0312dec905f13299c72e4ce69d79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be33240e8bf8ac0fcc4c0f028ba5173ac80d0312dec905f13299c72e4ce69d79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be33240e8bf8ac0fcc4c0f028ba5173ac80d0312dec905f13299c72e4ce69d79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.spl
mirror: doc/06_spec/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an impl whose method takes fewer parameters than the trait declares, on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the same impl on the JIT — the engine ordinary programs actually run on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts a correct impl on both engines — the control arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
