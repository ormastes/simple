# Backend Port System Specification

> <details>

<!-- sdn-diagram:id=backend_port_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_port_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_port_system_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_port_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### backend port fn-fields are independently invocable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With string-keyed DI, a typo like "Backned" silently returns nil.
# With typed BackendPort, the field is a named struct field.
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")
```

</details>

#### supports_jit reflects backend capability without string lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.run_fn
val result = f(nil)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_be_nil()
```

</details>

#### noop backend pipeline executes all fn-fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### backend port and module_loader port are both accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val loader_name = services.module_loader.name
val backend_name = services.backend.name
expect(loader_name).to_equal("noop-module-loader")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### all pipeline stages have distinct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### noop backend target triple is noop sentinel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val f = services.backend.target_triple_fn
val triple = f()
expect(triple).to_equal("noop")
```

</details>

#### noop backend does not claim jit support

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
