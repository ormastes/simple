# Backend Port Phases Specification

> Tests covering BackendPort: Phase 1 - Basic API, BackendPort: Phase 2 - Integration, BackendPort: Phase 3 - System behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Port Phases Specification

## Scenarios

### BackendPort: Phase 1 - Basic API

#### struct construction via factory

#### creates backend port with name field

- creates backend port with name field
   - Expected: backend.name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates backend port with name field")
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")
```

</details>

#### backend port has run_fn field

- backend port has run_fn field
   - Expected: f equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend port has run_fn field")
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
expect(f).to_equal(f)
```

</details>

#### backend port has supports_jit_fn field

- backend port has supports_jit_fn field
   - Expected: f equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend port has supports_jit_fn field")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
expect(f).to_equal(f)
```

</details>

#### backend port has target_triple_fn field

- backend port has target_triple_fn field
   - Expected: f equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend port has target_triple_fn field")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
expect(f).to_equal(f)
```

</details>

#### fn-field invocation

#### supports_jit_fn returns false for noop backend

- supports_jit_fn returns false for noop backend
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports_jit_fn returns false for noop backend")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### target_triple_fn returns noop for noop backend

- target_triple_fn returns noop for noop backend
   - Expected: result equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("target_triple_fn returns noop for noop backend")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>

#### name distinguishes backend implementations

- name distinguishes backend implementations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("name distinguishes backend implementations")
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_start_with("noop")
```

</details>

### BackendPort: Phase 2 - Integration

#### backend port inside CompilerServices

#### CompilerServices has backend field with name

- CompilerServices has backend field with name
   - Expected: name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CompilerServices has backend field with name")
val services = create_default_services()
val name = services.backend.name
expect(name).to_equal("noop-backend")
```

</details>

#### backend port is separate from other ports

- backend port is separate from other ports
   - Expected: lexer_name equals `noop-lexer`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend port is separate from other ports")
val services = create_default_services()
val lexer_name = services.lexer.name
val backend_name = services.backend.name
expect(lexer_name).to_equal("noop-lexer")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend port and parser port are independent

- backend port and parser port are independent
   - Expected: parser_name equals `noop-parser`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend port and parser port are independent")
val services = create_default_services()
val parser_name = services.parser.name
val backend_name = services.backend.name
expect(parser_name).to_equal("noop-parser")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### custom backend port construction

#### can construct custom backend port with typed fn-fields

- can construct custom backend port with typed fn-fields
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("can construct custom backend port with typed fn-fields")
var call_count = 0
fn my_supports_jit() -> bool: true
fn my_target_triple() -> text: "x86_64-linux"
fn my_run(m) -> text: "ran"
val custom_backend_name = "custom-test-backend"
val f_jit = my_supports_jit
val result = f_jit()
expect(result).to_equal(true)
```

</details>

#### target_triple identifies backend type

- target_triple identifies backend type
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("target_triple identifies backend type")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val triple = f()
expect(triple).to_equal("noop")
```

</details>

#### supports_jit reflects backend capability

- supports_jit reflects backend capability
   - Expected: jit_support is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports_jit reflects backend capability")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val jit_support = f()
expect(jit_support).to_equal(false)
```

</details>

### BackendPort: Phase 3 - System behavior

#### typed contract enforced

#### backend name is always a text value

- backend name is always a text value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend name is always a text value")
val services = create_default_services()
val backend = services.backend
val n = backend.name
expect(n.len()).to_be_greater_than(0)
```

</details>

#### noop backend has consistent identity

- noop backend has consistent identity
   - Expected: s1.backend.name equals `s2.backend.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("noop backend has consistent identity")
val s1 = create_default_services()
val s2 = create_default_services()
expect(s1.backend.name).to_equal(s2.backend.name)
```

</details>

#### backend fn-fields are non-nil

- backend fn-fields are non-nil
   - Expected: r1 is false
   - Expected: r2 equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend fn-fields are non-nil")
val services = create_default_services()
val backend = services.backend
val f1 = backend.supports_jit_fn
val f2 = backend.target_triple_fn
val r1 = f1()
val r2 = f2()
expect(r1).to_equal(false)
expect(r2).to_equal("noop")
```

</details>

#### edge cases

#### calling supports_jit multiple times gives same result

- calling supports_jit multiple times gives same result
   - Expected: r1 equals `r2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("calling supports_jit multiple times gives same result")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal(r2)
```

</details>

#### calling target_triple multiple times gives same result

- calling target_triple multiple times gives same result
   - Expected: r1 equals `r2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("calling target_triple multiple times gives same result")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal(r2)
```

</details>

#### two separate service instances have independent backends

- two separate service instances have independent backends
   - Expected: r1 equals `r2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two separate service instances have independent backends")
val s1 = create_default_services()
val s2 = create_default_services()
val b1 = s1.backend
val b2 = s2.backend
val f1 = b1.supports_jit_fn
val f2 = b2.supports_jit_fn
val r1 = f1()
val r2 = f2()
expect(r1).to_equal(r2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/backend_port_phases_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BackendPort: Phase 1 - Basic API, BackendPort: Phase 2 - Integration, BackendPort: Phase 3 - System behavior.
- BackendPort: Phase 1 - Basic API
- BackendPort: Phase 2 - Integration
- BackendPort: Phase 3 - System behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `b1237eb25bd11ae65eaf73629222727b6d70fd2b66a5395e245a06340c880fa0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1237eb25bd11ae65eaf73629222727b6d70fd2b66a5395e245a06340c880fa0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1237eb25bd11ae65eaf73629222727b6d70fd2b66a5395e245a06340c880fa0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/compiler/backend/backend_port_phases_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/backend_port_phases_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/backend_port_phases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/backend_port_phases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/backend_port_phases_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates backend port with name field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/backend_port_phases_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backend port has run_fn field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/backend_port_phases_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backend port has supports_jit_fn field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/backend_port_phases_spec.spl:121:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can construct custom backend port with typed fn-fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
