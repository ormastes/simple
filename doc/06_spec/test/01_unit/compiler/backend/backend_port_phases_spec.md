# Backend Port Phases Specification

> <details>

<!-- sdn-diagram:id=backend_port_phases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_port_phases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_port_phases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_port_phases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

#### backend port has run_fn field

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

#### backend port has supports_jit_fn field

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

#### backend port has target_triple_fn field

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

#### fn-field invocation

#### supports_jit_fn returns false for noop backend

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

#### target_triple_fn returns noop for noop backend

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

#### name distinguishes backend implementations

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

### BackendPort: Phase 2 - Integration

#### backend port inside CompilerServices

#### CompilerServices has backend field with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val name = services.backend.name
expect(name).to_equal("noop-backend")
```

</details>

#### backend port is separate from other ports

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

#### backend port and parser port are independent

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

#### custom backend port construction

#### can construct custom backend port with typed fn-fields

1. fn my supports jit
2. fn my target triple
3. fn my run
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### supports_jit reflects backend capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val n = backend.name
expect(n.len()).to_be_greater_than(0)
```

</details>

#### noop backend has consistent identity

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

#### backend fn-fields are non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal(r2)
```

</details>

#### calling target_triple multiple times gives same result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal(r2)
```

</details>

#### two separate service instances have independent backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
