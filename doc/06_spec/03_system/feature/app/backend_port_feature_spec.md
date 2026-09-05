# BackendPort Typed Composition Root

> Tests the BackendPort typed composition root that manages backend pipeline stage wiring. Verifies that backend ports are correctly instantiated, composed, and that the typed dispatch routes compilation requests to the right backend.

<!-- sdn-diagram:id=backend_port_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_port_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_port_feature_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_port_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the BackendPort typed composition root that manages backend pipeline
stage wiring. Verifies that backend ports are correctly instantiated, composed,
and that the typed dispatch routes compilation requests to the right backend.

## Scenarios

### BackendPort Feature: Phase 1 - Struct shape

#### name field

#### BackendPort has name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val n = backend.name
expect(n).to_equal("noop-backend")
```

</details>

#### name field is a non-empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name.len()).to_be_greater_than(0)
```

</details>

#### compile function field

#### BackendPort has run_fn field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
expect(f).to_equal(f)
```

</details>

#### run_fn is a callable function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
val result = f(nil)
expect(result).to_be_nil()
```

</details>

#### emit function fields

#### BackendPort has supports_jit_fn field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
expect(f).to_equal(f)
```

</details>

#### BackendPort has target_triple_fn field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
expect(f).to_equal(f)
```

</details>

#### supports_jit_fn is callable and returns bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### target_triple_fn is callable and returns text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")
```

</details>

#### noop backend compile fn returns result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
val result = f(nil)
expect(result).to_be_nil()
```

</details>

#### noop backend supports_jit_fn returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### noop backend target_triple_fn returns noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>

#### custom backend creation

#### custom backend can define its own supports_jit behavior

1. fn custom jit
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn custom_jit() -> bool: true
val f = custom_jit
val result = f()
expect(result).to_equal(true)
```

</details>

#### custom backend can define its own target_triple

1. fn custom triple
   - Expected: result equals `x86_64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn custom_triple() -> text: "x86_64-unknown-linux-gnu"
val f = custom_triple
val result = f()
expect(result).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### custom backend target triple differs from noop triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = create_default_services()
val s2 = create_default_services()
expect(s1.backend.name).to_equal(s2.backend.name)
```

</details>

#### two noop backends have same target triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend_name = services.backend.name
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend field is distinct from lexer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lexer_name = services.lexer.name
val backend_name = services.backend.name
expect(lexer_name).to_equal("noop-lexer")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend field is distinct from parser field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val parser_name = services.parser.name
val backend_name = services.backend.name
expect(parser_name).to_equal("noop-parser")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend field is distinct from logger field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val logger_name = services.logger.name
val backend_name = services.backend.name
expect(logger_name).to_equal("noop-logger")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### backend swapping in services

#### backend can be replaced with different name via delegation

1. fn alt jit
2. fn alt triple
3. fn alt run
   - Expected: backend.name equals `wasm-backend`
   - Expected: f_jit() is true
   - Expected: f_triple() equals `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val jit_supported = f()
expect(jit_supported).to_equal(false)
```

</details>

#### full chain: services -> backend -> target_triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val triple = f()
expect(triple).to_equal("noop")
```

</details>

#### full chain: services -> backend -> name then supports_jit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name.len()).to_be_greater_than(0)
```

</details>

#### noop backend name starts with noop prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_start_with("noop")
```

</details>

#### noop backend name contains backend suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_end_with("backend")
```

</details>

#### different backends have different names

#### noop backend name differs from custom name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val noop_name = services.backend.name
val custom_name = "interpreter-backend"
expect(noop_name).to_equal("noop-backend")
expect(custom_name).to_equal("interpreter-backend")
```

</details>

#### noop backend name differs from wasm backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val noop_name = services.backend.name
val wasm_name = "wasm-backend"
expect(noop_name).to_equal("noop-backend")
expect(wasm_name).to_equal("wasm-backend")
```

</details>

#### backend identification works via target_triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val f = services.backend.supports_jit_fn
val result = f()
val is_false = result == false
expect(is_false).to_equal(true)
```

</details>

#### target_triple_fn always returns a text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val f = services.backend.target_triple_fn
val result = f()
expect(result.len()).to_be_greater_than(0)
```

</details>

#### calling fn-fields multiple times is idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
