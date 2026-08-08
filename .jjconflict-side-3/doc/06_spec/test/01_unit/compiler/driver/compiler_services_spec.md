# Compiler Services Specification

> <details>

<!-- sdn-diagram:id=compiler_services_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_services_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_services_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_services_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Services Specification

## Scenarios

### CompilerServices - create_default_services

#### factory construction

#### creates services without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.lexer.name).to_equal("noop-lexer")
```

</details>

#### wires lexer port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.lexer.name).to_equal("noop-lexer")
```

</details>

#### wires parser port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.parser.name).to_equal("noop-parser")
```

</details>

#### wires desugarer port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.desugarer.name).to_equal("noop-desugarer")
```

</details>

#### wires type_checker port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.type_checker.name).to_equal("noop-type-checker")
```

</details>

#### wires hir_lowerer port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.hir_lowerer.name).to_equal("noop-hir-lowerer")
```

</details>

#### wires mir_lowerer port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.mir_lowerer.name).to_equal("noop-mir-lowerer")
```

</details>

#### wires backend port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.backend.name).to_equal("noop-backend")
```

</details>

#### wires logger port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.logger.name).to_equal("noop-logger")
```

</details>

#### wires module_loader port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.module_loader.name).to_equal("noop-module-loader")
```

</details>

### CompilerServices - port fn-fields are callable

#### lexer port

#### tokenize_fn returns a list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lexer = services.lexer
val f = lexer.tokenize_fn
val result = f("val x = 1")
expect(result.len()).to_equal(0)
```

</details>

#### parser port

#### parse_fn returns empty errors for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val parser = services.parser
val f = parser.parse_fn
val result = f([], "")
expect(result.len()).to_equal(0)
```

</details>

#### desugarer port

#### desugar_fn returns source unchanged for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val desugarer = services.desugarer
val src = "val x = 1"
val f = desugarer.desugar_fn
val result = f(src)
expect(result).to_equal(src)
```

</details>

#### type checker port

#### check_fn returns empty errors for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val checker = services.type_checker
val f = checker.check_fn
val result = f("main")
expect(result.len()).to_equal(0)
```

</details>

#### hir lowerer port

#### lower_fn returns empty errors for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lowerer = services.hir_lowerer
val f = lowerer.lower_fn
val result = f("main")
expect(result.len()).to_equal(0)
```

</details>

#### mir lowerer port

#### lower_fn returns empty errors for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lowerer = services.mir_lowerer
val f = lowerer.lower_fn
val result = f("main")
expect(result.len()).to_equal(0)
```

</details>

#### backend port

#### supports_jit_fn returns false for noop

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

#### module loader port

#### load_fn returns empty string for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val loader = services.module_loader
val f = loader.load_fn
val result = f("some/path.spl")
expect(result).to_equal("")
```

</details>

#### resolve_fn returns import name unchanged for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val loader = services.module_loader
val f = loader.resolve_fn
val result = f("/src/main.spl", "std.string")
expect(result).to_equal("std.string")
```

</details>

### CompilerServices - struct shape

#### field presence

#### has lexer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lexer_name = services.lexer.name
expect(lexer_name).to_equal("noop-lexer")
```

</details>

#### has parser field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val parser_name = services.parser.name
expect(parser_name).to_equal("noop-parser")
```

</details>

#### has desugarer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val desugarer_name = services.desugarer.name
expect(desugarer_name).to_equal("noop-desugarer")
```

</details>

#### has type_checker field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val checker_name = services.type_checker.name
expect(checker_name).to_equal("noop-type-checker")
```

</details>

#### has hir_lowerer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val hir_name = services.hir_lowerer.name
expect(hir_name).to_equal("noop-hir-lowerer")
```

</details>

#### has mir_lowerer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val mir_name = services.mir_lowerer.name
expect(mir_name).to_equal("noop-mir-lowerer")
```

</details>

#### has backend field

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

#### has logger field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val logger_name = services.logger.name
expect(logger_name).to_equal("noop-logger")
```

</details>

#### has module_loader field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val loader_name = services.module_loader.name
expect(loader_name).to_equal("noop-module-loader")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compiler_services_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CompilerServices - create_default_services
- CompilerServices - port fn-fields are callable
- CompilerServices - struct shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
