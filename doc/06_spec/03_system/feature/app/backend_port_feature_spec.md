# BackendPort Typed Composition Root

> Tests the BackendPort typed composition root that manages backend pipeline stage wiring. Verifies that backend ports are correctly instantiated, composed, and that the typed dispatch routes compilation requests to the right backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BackendPort Typed Composition Root

Tests the BackendPort typed composition root that manages backend pipeline stage wiring. Verifies that backend ports are correctly instantiated, composed, and that the typed dispatch routes compilation requests to the right backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/backend_port_feature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the BackendPort typed composition root that manages backend pipeline
stage wiring. Verifies that backend ports are correctly instantiated, composed,
and that the typed dispatch routes compilation requests to the right backend.

## Scenarios

### BackendPort Feature: Phase 1 - Struct shape

#### name field

#### BackendPort has name field

- BackendPort has name field
   - Expected: n equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BackendPort has name field")
val services = create_default_services()
val backend = services.backend
val n = backend.name
expect(n).to_equal("noop-backend")
```

</details>

#### name field is a non-empty text

- name field is a non-empty text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("name field is a non-empty text")
val services = create_default_services()
val backend = services.backend
expect(backend.name.len()).to_be_greater_than(0)
```

</details>

#### compile function field

#### BackendPort has run_fn field

- BackendPort has run_fn field
   - Expected: f equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BackendPort has run_fn field")
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
expect(f).to_equal(f)
```

</details>

#### run_fn is a callable function

- run_fn is a callable function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run_fn is a callable function")
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
val result = f(nil)
expect(result).to_be_nil()
```

</details>

#### emit function fields

#### BackendPort has supports_jit_fn field

- BackendPort has supports_jit_fn field
   - Expected: f equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BackendPort has supports_jit_fn field")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
expect(f).to_equal(f)
```

</details>

#### BackendPort has target_triple_fn field

- BackendPort has target_triple_fn field
   - Expected: f equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BackendPort has target_triple_fn field")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
expect(f).to_equal(f)
```

</details>

#### supports_jit_fn is callable and returns bool

- supports_jit_fn is callable and returns bool
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports_jit_fn is callable and returns bool")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### target_triple_fn is callable and returns text

- target_triple_fn is callable and returns text
   - Expected: result equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("target_triple_fn is callable and returns text")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>

### BackendPort Feature: Phase 2 - Factory creation

#### noop backend factory

#### noop backend has correct name

- noop backend has correct name
   - Expected: backend.name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend has correct name")
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")
```

</details>

#### noop backend compile fn returns result

- noop backend compile fn returns result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend compile fn returns result")
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
val result = f(nil)
expect(result).to_be_nil()
```

</details>

#### noop backend supports_jit_fn returns false

- noop backend supports_jit_fn returns false
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend supports_jit_fn returns false")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### noop backend target_triple_fn returns noop

- noop backend target_triple_fn returns noop
   - Expected: result equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend target_triple_fn returns noop")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>

#### custom backend creation

#### custom backend can define its own supports_jit behavior

- custom backend can define its own supports_jit behavior
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("custom backend can define its own supports_jit behavior")
fn custom_jit() -> bool: true
val f = custom_jit
val result = f()
expect(result).to_equal(true)
```

</details>

#### custom backend can define its own target_triple

- custom backend can define its own target_triple
   - Expected: result equals `x86_64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("custom backend can define its own target_triple")
fn custom_triple() -> text: "x86_64-unknown-linux-gnu"
val f = custom_triple
val result = f()
expect(result).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### custom backend target triple differs from noop triple

- custom backend target triple differs from noop triple
   - Expected: noop_triple equals `noop`
   - Expected: custom_triple equals `x86_64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("custom backend target triple differs from noop triple")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val noop_triple = f()
val custom_triple = "x86_64-unknown-linux-gnu"
expect(noop_triple).to_equal("noop")
expect(custom_triple).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### multiple backends

#### two noop backends have same name

- two noop backends have same name
   - Expected: s1.backend.name equals `s2.backend.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two noop backends have same name")
val s1 = create_default_services()
val s2 = create_default_services()
expect(s1.backend.name).to_equal(s2.backend.name)
```

</details>

#### two noop backends have same target triple

- two noop backends have same target triple
   - Expected: r1 equals `r2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two noop backends have same target triple")
val s1 = create_default_services()
val s2 = create_default_services()
val f1 = s1.backend.target_triple_fn
val f2 = s2.backend.target_triple_fn
val r1 = f1()
val r2 = f2()
expect(r1).to_equal(r2)
```

</details>

### BackendPort Feature: Phase 3 - Integration with CompilerServices

#### CompilerServices has backend field

#### CompilerServices.backend is a BackendPort

- CompilerServices.backend is a BackendPort
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CompilerServices.backend is a BackendPort")
val services = create_default_services()
val backend_name = services.backend.name
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend field is distinct from lexer field

- backend field is distinct from lexer field
   - Expected: lexer_name equals `noop-lexer`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend field is distinct from lexer field")
val services = create_default_services()
val lexer_name = services.lexer.name
val backend_name = services.backend.name
expect(lexer_name).to_equal("noop-lexer")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend field is distinct from parser field

- backend field is distinct from parser field
   - Expected: parser_name equals `noop-parser`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend field is distinct from parser field")
val services = create_default_services()
val parser_name = services.parser.name
val backend_name = services.backend.name
expect(parser_name).to_equal("noop-parser")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend field is distinct from logger field

- backend field is distinct from logger field
   - Expected: logger_name equals `noop-logger`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend field is distinct from logger field")
val services = create_default_services()
val logger_name = services.logger.name
val backend_name = services.backend.name
expect(logger_name).to_equal("noop-logger")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend swapping in services

#### backend can be replaced with different name via delegation

- backend can be replaced with different name via delegation
   - Expected: backend.name equals `wasm-backend`
   - Expected: f_jit() is true
   - Expected: f_triple() equals `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend can be replaced with different name via delegation")
fn alt_jit() -> bool: true
fn alt_triple() -> text: "wasm32"
fn alt_run(m): nil
val backend = BackendPort(name: "wasm-backend", run_fn: alt_run, supports_jit_fn: alt_jit, target_triple_fn: alt_triple)
val f_run = backend.run_fn
val f_jit = backend.supports_jit_fn
val f_triple = backend.target_triple_fn

expect(backend.name).to_equal("wasm-backend")
expect(f_run(nil)).to_be_nil()
expect(f_jit()).to_equal(true)
expect(f_triple()).to_equal("wasm32")
```

</details>

#### alternate backend target triple is different from noop

- alternate backend target triple is different from noop
   - Expected: noop_triple equals `noop`
   - Expected: wasm_triple equals `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("alternate backend target triple is different from noop")
val services = create_default_services()
val f = services.backend.target_triple_fn
val noop_triple = f()
val wasm_triple = "wasm32"
expect(noop_triple).to_equal("noop")
expect(wasm_triple).to_equal("wasm32")
```

</details>

#### backend port functions callable end-to-end

#### full chain: services -> backend -> supports_jit

- full chain: services -> backend -> supports_jit
   - Expected: jit_supported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("full chain: services -> backend -> supports_jit")
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val jit_supported = f()
expect(jit_supported).to_equal(false)
```

</details>

#### full chain: services -> backend -> target_triple

- full chain: services -> backend -> target_triple
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("full chain: services -> backend -> target_triple")
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val triple = f()
expect(triple).to_equal("noop")
```

</details>

#### full chain: services -> backend -> name then supports_jit

- full chain: services -> backend -> name then supports_jit
   - Expected: name equals `noop-backend`
   - Expected: jit is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("full chain: services -> backend -> name then supports_jit")
val services = create_default_services()
val backend = services.backend
val name = backend.name
val f = backend.supports_jit_fn
val jit = f()
expect(name).to_equal("noop-backend")
expect(jit).to_equal(false)
```

</details>

### BackendPort Feature: Phase 4 - Type safety

#### name is unique identifier

#### BackendPort name is meaningful (not empty)

- BackendPort name is meaningful (not empty)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BackendPort name is meaningful (not empty)")
val services = create_default_services()
val backend = services.backend
expect(backend.name.len()).to_be_greater_than(0)
```

</details>

#### noop backend name starts with noop prefix

- noop backend name starts with noop prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend name starts with noop prefix")
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_start_with("noop")
```

</details>

#### noop backend name contains backend suffix

- noop backend name contains backend suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend name contains backend suffix")
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_end_with("backend")
```

</details>

#### different backends have different names

#### noop backend name differs from custom name

- noop backend name differs from custom name
   - Expected: noop_name equals `noop-backend`
   - Expected: custom_name equals `interpreter-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend name differs from custom name")
val services = create_default_services()
val noop_name = services.backend.name
val custom_name = "interpreter-backend"
expect(noop_name).to_equal("noop-backend")
expect(custom_name).to_equal("interpreter-backend")
```

</details>

#### noop backend name differs from wasm backend name

- noop backend name differs from wasm backend name
   - Expected: noop_name equals `noop-backend`
   - Expected: wasm_name equals `wasm-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop backend name differs from wasm backend name")
val services = create_default_services()
val noop_name = services.backend.name
val wasm_name = "wasm-backend"
expect(noop_name).to_equal("noop-backend")
expect(wasm_name).to_equal("wasm-backend")
```

</details>

#### backend identification works via target_triple

- backend identification works via target_triple
   - Expected: noop_triple equals `noop`
   - Expected: x86_triple equals `x86_64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend identification works via target_triple")
val services = create_default_services()
val f = services.backend.target_triple_fn
val noop_triple = f()
val x86_triple = "x86_64-unknown-linux-gnu"
expect(noop_triple).to_equal("noop")
expect(x86_triple).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### fn-field type correctness

#### supports_jit_fn always returns a bool

- supports_jit_fn always returns a bool
   - Expected: is_false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports_jit_fn always returns a bool")
val services = create_default_services()
val f = services.backend.supports_jit_fn
val result = f()
val is_false = result == false
expect(is_false).to_equal(true)
```

</details>

#### target_triple_fn always returns a text

- target_triple_fn always returns a text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("target_triple_fn always returns a text")
val services = create_default_services()
val f = services.backend.target_triple_fn
val result = f()
expect(result.len()).to_be_greater_than(0)
```

</details>

#### calling fn-fields multiple times is idempotent

- calling fn-fields multiple times is idempotent
   - Expected: r1 equals `r2`
   - Expected: t1 equals `t2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calling fn-fields multiple times is idempotent")
val services = create_default_services()
val backend = services.backend
val f_jit = backend.supports_jit_fn
val f_triple = backend.target_triple_fn
val r1 = f_jit()
val r2 = f_jit()
val t1 = f_triple()
val t2 = f_triple()
expect(r1).to_equal(r2)
expect(t1).to_equal(t2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
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

- Canonical SPipe generation for source `641555aad9dead25a27383c4da3b2d8d9095b26b0c78b97d6cf1b87660052c60`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `641555aad9dead25a27383c4da3b2d8d9095b26b0c78b97d6cf1b87660052c60`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `641555aad9dead25a27383c4da3b2d8d9095b26b0c78b97d6cf1b87660052c60`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/backend_port_feature_spec.spl
mirror: doc/06_spec/03_system/feature/app/backend_port_feature_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/backend_port_feature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/backend_port_feature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/backend_port_feature_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BackendPort has name field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/backend_port_feature_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'name field is a non-empty text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/backend_port_feature_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BackendPort has run_fn field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
