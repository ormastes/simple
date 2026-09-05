# Compiler Services Phases Specification

> <details>

<!-- sdn-diagram:id=compiler_services_phases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_services_phases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_services_phases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_services_phases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Services Phases Specification

## Scenarios

### CompilerServices: Phase 1 - Basic API

#### factory creates services

#### create_default_services returns a container

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.lexer.name).to_equal("noop-lexer")
```

</details>

#### all 9 ports are wired with correct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.lexer.name).to_equal("noop-lexer")
expect(s.parser.name).to_equal("noop-parser")
expect(s.desugarer.name).to_equal("noop-desugarer")
```

</details>

#### type checker and hir lowerer have correct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.type_checker.name).to_equal("noop-type-checker")
expect(s.hir_lowerer.name).to_equal("noop-hir-lowerer")
```

</details>

#### mir lowerer has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.mir_lowerer.name).to_equal("noop-mir-lowerer")
```

</details>

#### backend has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.backend.name).to_equal("noop-backend")
```

</details>

#### logger has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.logger.name).to_equal("noop-logger")
```

</details>

#### module loader has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.module_loader.name).to_equal("noop-module-loader")
```

</details>

#### port fn-fields are callable

#### lexer tokenize_fn returns empty list for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.lexer.tokenize_fn
val result = f("val x = 1")
expect(result.len()).to_equal(0)
```

</details>

#### parser parse_fn returns empty errors for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.parser.parse_fn
val result = f([], "")
expect(result.len()).to_equal(0)
```

</details>

#### desugarer desugar_fn returns source unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val src = "val x = 1"
val f = s.desugarer.desugar_fn
val result = f(src)
expect(result).to_equal(src)
```

</details>

#### type checker check_fn returns empty errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.type_checker.check_fn
val result = f("main")
expect(result.len()).to_equal(0)
```

</details>

#### hir lowerer lower_fn returns empty errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.hir_lowerer.lower_fn
val result = f("main")
expect(result.len()).to_equal(0)
```

</details>

#### mir lowerer lower_fn returns empty errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.mir_lowerer.lower_fn
val result = f("main")
expect(result.len()).to_equal(0)
```

</details>

#### backend supports_jit_fn returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### backend target_triple_fn returns noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>

#### module loader load_fn returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.module_loader.load_fn
val result = f("some/path.spl")
expect(result).to_equal("")
```

</details>

#### module loader resolve_fn returns import name unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.module_loader.resolve_fn
val result = f("/src/main.spl", "std.string")
expect(result).to_equal("std.string")
```

</details>

### CompilerServices: Phase 2 - Integration

#### pipeline stage separation

#### each port has a distinct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val names = [
    s.lexer.name,
    s.parser.name,
    s.desugarer.name,
    s.type_checker.name,
    s.hir_lowerer.name,
    s.mir_lowerer.name,
    s.backend.name,
    s.logger.name,
    s.module_loader.name
]
expect(names.len()).to_equal(9)
```

</details>

#### lexer and parser are independent ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.lexer.name).to_equal("noop-lexer")
expect(s.parser.name).to_equal("noop-parser")
```

</details>

#### hir and mir lowerers have distinct names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val hir = s.hir_lowerer.name
val mir = s.mir_lowerer.name
expect(hir).to_equal("noop-hir-lowerer")
expect(mir).to_equal("noop-mir-lowerer")
```

</details>

#### logger port has data fields

#### logger has name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.logger.name).to_equal("noop-logger")
```

</details>

#### logger has level field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
expect(s.logger.level).to_equal(0)
```

</details>

#### create_default_services called multiple times

#### each call produces independent containers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = create_default_services()
val s2 = create_default_services()
expect(s1.lexer.name).to_equal(s2.lexer.name)
expect(s1.backend.name).to_equal(s2.backend.name)
```

</details>

#### two service containers have same port names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = create_default_services()
val s2 = create_default_services()
expect(s1.parser.name).to_equal(s2.parser.name)
```

</details>

### CompilerServices: Phase 3 - System behavior

#### desugar pass-through behavior

#### noop desugarer returns source unchanged for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.desugarer.desugar_fn
val result = f("")
expect(result).to_equal("")
```

</details>

#### noop desugarer preserves complex source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val src = "fn foo(x: i64) -> i64:\n    x * 2"
val f = s.desugarer.desugar_fn
val result = f(src)
expect(result).to_equal(src)
```

</details>

#### module loader resolve behavior

#### noop resolve returns import name for any current path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.module_loader.resolve_fn
val r1 = f("/a/b.spl", "std.math")
val r2 = f("/x/y.spl", "std.math")
expect(r1).to_equal("std.math")
expect(r2).to_equal("std.math")
```

</details>

#### noop load returns empty for any path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.module_loader.load_fn
val r1 = f("src/foo.spl")
val r2 = f("test/bar.spl")
expect(r1).to_equal("")
expect(r2).to_equal("")
```

</details>

#### backend port in services

#### noop backend supports_jit is consistently false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = create_default_services()
val s2 = create_default_services()
val f1 = s1.backend.supports_jit_fn
val f2 = s2.backend.supports_jit_fn
expect(f1()).to_equal(false)
expect(f2()).to_equal(false)
```

</details>

#### noop backend triple is consistently noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = create_default_services()
val f = s.backend.target_triple_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal(r2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compiler_services_phases_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CompilerServices: Phase 1 - Basic API
- CompilerServices: Phase 2 - Integration
- CompilerServices: Phase 3 - System behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
