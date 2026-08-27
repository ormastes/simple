# Backend Port System Specification

> Tests covering BackendPort System: end-to-end backend selection, BackendPort System: Phase - noop pipeline completes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Port System Specification

## Scenarios

### BackendPort System: end-to-end backend selection

#### interpreter backend services

#### interpreter backend services work

- interpreter backend services work
   - Expected: backend.name equals `noop-backend`
   - Expected: jit is false
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpreter backend services work")
val services = create_default_services()
val backend = services.backend
val f_jit = backend.supports_jit_fn
val f_triple = backend.target_triple_fn
val jit = f_jit()
val triple = f_triple()
expect(backend.name).to_equal("noop-backend")
expect(jit).to_equal(false)
expect(triple).to_equal("noop")
```

</details>

#### backend port is immediately accessible from services

- backend port is immediately accessible from services
   - Expected: name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port is immediately accessible from services")
val services = create_default_services()
val name = services.backend.name
expect(name).to_equal("noop-backend")
```

</details>

#### backend port fn-fields are independently invocable

- backend port fn-fields are independently invocable
   - Expected: jit_result is false
   - Expected: triple_result equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port fn-fields are independently invocable")
val services = create_default_services()
val backend = services.backend
val jit_fn = backend.supports_jit_fn
val triple_fn = backend.target_triple_fn
val jit_result = jit_fn()
val triple_result = triple_fn()
expect(jit_result).to_equal(false)
expect(triple_result).to_equal("noop")
```

</details>

#### typed access vs string-keyed DI

#### backend port replaces string-keyed di lookup

- backend port replaces string-keyed di lookup
   - Expected: name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port replaces string-keyed di lookup")
# Old pattern (di.resolve("Backend") -> Any, no type safety):
#   val backend_any = di.resolve("Backend")  # returns Any
#   # Caller must know the shape; no compiler check
#
# New pattern (typed BackendPort on CompilerServices):
val services = create_default_services()
val backend = services.backend          # typed field access
val name = backend.name                 # statically known field
expect(name).to_equal("noop-backend")
```

</details>

#### named field access catches wrong field at load time

- named field access catches wrong field at load time
   - Expected: backend.name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("named field access catches wrong field at load time")
# With string-keyed DI, a typo like "Backned" silently returns nil.
# With typed BackendPort, the field is a named struct field.
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")
```

</details>

#### supports_jit reflects backend capability without string lookup

- supports_jit reflects backend capability without string lookup
   - Expected: supported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports_jit reflects backend capability without string lookup")
# Old: (di.resolve("Backend") as BackendImpl).supports_jit()
# New:
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val supported = f()
expect(supported).to_equal(false)
```

</details>

#### target_triple reflects backend target without string lookup

- target_triple reflects backend target without string lookup
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("target_triple reflects backend target without string lookup")
# Old: (di.resolve("Backend") as BackendImpl).target_triple()
# New:
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val triple = f()
expect(triple).to_equal("noop")
```

</details>

### BackendPort System: Phase - noop pipeline completes

#### noop backend processes input without error

#### noop backend run_fn accepts module input

- noop backend run_fn accepts module input
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend run_fn accepts module input")
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
val result = f(nil)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_be_nil()
```

</details>

#### noop backend pipeline executes all fn-fields

- noop backend pipeline executes all fn-fields
   - Expected: jit is false
   - Expected: triple equals `noop`
   - Expected: run.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend pipeline executes all fn-fields")
val services = create_default_services()
val backend = services.backend
val jit_fn = backend.supports_jit_fn
val triple_fn = backend.target_triple_fn
val run_fn = backend.run_fn
val jit = jit_fn()
val triple = triple_fn()
val run = run_fn(nil)
expect(jit).to_equal(false)
expect(triple).to_equal("noop")
expect(run.is_ok()).to_equal(true)
expect(run.unwrap()).to_be_nil()
```

</details>

#### noop pipeline is repeatable across service instances

- noop pipeline is repeatable across service instances
   - Expected: t1 equals `t2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop pipeline is repeatable across service instances")
val s1 = create_default_services()
val s2 = create_default_services()
val f1 = s1.backend.target_triple_fn
val f2 = s2.backend.target_triple_fn
val t1 = f1()
val t2 = f2()
expect(t1).to_equal(t2)
```

</details>

#### backend works alongside other pipeline ports

#### backend port and lexer port are both accessible

- backend port and lexer port are both accessible
   - Expected: lexer_name equals `noop-lexer`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port and lexer port are both accessible")
val services = create_default_services()
val lexer_name = services.lexer.name
val backend_name = services.backend.name
expect(lexer_name).to_equal("noop-lexer")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend port and module_loader port are both accessible

- backend port and module_loader port are both accessible
   - Expected: loader_name equals `noop-module-loader`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port and module_loader port are both accessible")
val services = create_default_services()
val loader_name = services.module_loader.name
val backend_name = services.backend.name
expect(loader_name).to_equal("noop-module-loader")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### all pipeline stages have distinct names

- all pipeline stages have distinct names
   - Expected: lexer_name equals `noop-lexer`
   - Expected: parser_name equals `noop-parser`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all pipeline stages have distinct names")
val services = create_default_services()
val lexer_name = services.lexer.name
val parser_name = services.parser.name
val backend_name = services.backend.name
expect(lexer_name).to_equal("noop-lexer")
expect(parser_name).to_equal("noop-parser")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend name identifies the implementation

#### noop backend is identifiable by name prefix

- noop backend is identifiable by name prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend is identifiable by name prefix")
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_start_with("noop")
```

</details>

#### noop backend target triple is noop sentinel

- noop backend target triple is noop sentinel
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend target triple is noop sentinel")
val services = create_default_services()
val f = services.backend.target_triple_fn
val triple = f()
expect(triple).to_equal("noop")
```

</details>

#### noop backend does not claim jit support

- noop backend does not claim jit support
   - Expected: jit is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend does not claim jit support")
val services = create_default_services()
val f = services.backend.supports_jit_fn
val jit = f()
expect(jit).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/backend_port_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BackendPort System: end-to-end backend selection, BackendPort System: Phase - noop pipeline completes.
- BackendPort System: end-to-end backend selection
- BackendPort System: Phase - noop pipeline completes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `97fd198435e0d2c21bc9ada85769c066571a720637b02b3a3d709e152ee5db52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97fd198435e0d2c21bc9ada85769c066571a720637b02b3a3d709e152ee5db52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97fd198435e0d2c21bc9ada85769c066571a720637b02b3a3d709e152ee5db52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/backend_port_system_spec.spl
mirror: doc/06_spec/03_system/compiler/backend_port_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/backend_port_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/backend_port_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/backend_port_system_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpreter backend services work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/backend_port_system_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backend port is immediately accessible from services' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/backend_port_system_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backend port fn-fields are independently invocable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
