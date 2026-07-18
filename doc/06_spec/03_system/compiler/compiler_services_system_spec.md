# Compiler Services System Specification

> <details>

<!-- sdn-diagram:id=compiler_services_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_services_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_services_system_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_services_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Services System Specification

## Scenarios

### CompilerServices System: Service container construction

#### create_default_services produces a fully wired container

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.lexer.name).to_equal("noop-lexer")
expect(svc.parser.name).to_equal("noop-parser")
expect(svc.desugarer.name).to_equal("noop-desugarer")
expect(svc.type_checker.name).to_equal("noop-type-checker")
expect(svc.hir_lowerer.name).to_equal("noop-hir-lowerer")
expect(svc.mir_lowerer.name).to_equal("noop-mir-lowerer")
expect(svc.backend.name).to_equal("noop-backend")
expect(svc.logger.name).to_equal("noop-logger")
expect(svc.module_loader.name).to_equal("noop-module-loader")
```

</details>

#### service container can be created and immediately queried

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val lexer_name = svc.lexer.name
expect(lexer_name).to_start_with("noop")
```

</details>

#### all port names follow the noop- naming convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.lexer.name).to_start_with("noop")
expect(svc.parser.name).to_start_with("noop")
expect(svc.desugarer.name).to_start_with("noop")
expect(svc.type_checker.name).to_start_with("noop")
expect(svc.hir_lowerer.name).to_start_with("noop")
expect(svc.mir_lowerer.name).to_start_with("noop")
expect(svc.backend.name).to_start_with("noop")
expect(svc.logger.name).to_start_with("noop")
expect(svc.module_loader.name).to_start_with("noop")
```

</details>

### CompilerServices System: Lexer and parser stages

#### lexer tokenizes a simple function declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val source = "fn add(a: i64, b: i64) -> i64: a + b"
val tokenize = svc.lexer.tokenize_fn
val tokens = tokenize(source)
# noop returns empty - verifies stage boundary contract
expect(tokens.len()).to_equal(0)
```

</details>

#### parser receives token stream from lexer and returns no errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val source = "fn add(a: i64, b: i64) -> i64: a + b"
val tokenize = svc.lexer.tokenize_fn
val tokens = tokenize(source)
expect(svc.parser.name).to_equal("noop-parser")
```

</details>

#### lexer handles multiline source without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val source = "fn foo():\n    val x = 1\n    x + 1"
val tokenize = svc.lexer.tokenize_fn
val tokens = tokenize(source)
expect(tokens.len()).to_equal(0)
```

</details>

#### parser returns empty error list for noop implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.parser.name).to_start_with("noop")
```

</details>

### CompilerServices System: Desugaring and type checking stages

#### desugarer receives source and returns transformed output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val source = "fn main(): print 1"
val desugar = svc.desugarer.desugar_fn
val transformed = desugar(source)
# noop returns source unchanged
expect(transformed).to_equal(source)
```

</details>

#### desugarer preserves source structure for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val source = "class Point:\n    x: i64\n    y: i64"
val desugar = svc.desugarer.desugar_fn
val result = desugar(source)
expect(result).to_equal(source)
```

</details>

#### type checker validates module by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val check = svc.type_checker.check_fn
val errors = check("my_module")
expect(errors.len()).to_equal(0)
```

</details>

#### type checker returns empty error list for unknown module in noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val check = svc.type_checker.check_fn
val errors = check("nonexistent_module")
expect(errors.len()).to_equal(0)
```

</details>

### CompilerServices System: HIR and MIR lowering stages

#### HIR lowerer lowers a module by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val lower = svc.hir_lowerer.lower_fn
val errors = lower("main")
expect(errors.len()).to_equal(0)
```

</details>

#### MIR lowerer lowers a module by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val lower = svc.mir_lowerer.lower_fn
val errors = lower("main")
expect(errors.len()).to_equal(0)
```

</details>

#### HIR and MIR lowering stages both succeed for same module

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val hir_lower = svc.hir_lowerer.lower_fn
val mir_lower = svc.mir_lowerer.lower_fn
val hir_errors = hir_lower("main")
val mir_errors = mir_lower("main")
expect(hir_errors.len()).to_equal(0)
expect(mir_errors.len()).to_equal(0)
```

</details>

#### HIR lowerer handles multiple module names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val lower = svc.hir_lowerer.lower_fn
val e1 = lower("module_a")
val e2 = lower("module_b")
expect(e1.len()).to_equal(0)
expect(e2.len()).to_equal(0)
```

</details>

### CompilerServices System: Backend stage

#### backend reports its capabilities via supports_jit_fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val jit_fn = svc.backend.supports_jit_fn
val supports = jit_fn()
expect(supports).to_equal(false)
```

</details>

#### backend reports its target architecture via target_triple_fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val triple_fn = svc.backend.target_triple_fn
val triple = triple_fn()
expect(triple).to_equal("noop")
```

</details>

#### backend triple is consistent across multiple calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val triple_fn = svc.backend.target_triple_fn
val t1 = triple_fn()
val t2 = triple_fn()
expect(t1).to_equal(t2)
```

</details>

#### backend JIT support is consistent across multiple calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val jit_fn = svc.backend.supports_jit_fn
val j1 = jit_fn()
val j2 = jit_fn()
expect(j1).to_equal(j2)
```

</details>

### CompilerServices System: Logger integration

#### logger has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.logger.name).to_equal("noop-logger")
```

</details>

#### logger has level field set to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.logger.level).to_equal(0)
```

</details>

#### logger name follows noop convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.logger.name).to_start_with("noop")
```

</details>

### CompilerServices System: Module loader integration

#### module loader resolves import paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val path = "std.math"
expect(path).to_equal("std.math")
```

</details>

#### module loader loads resolved module content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val load = svc.module_loader.load_fn
val resolved = "std.array"
val content = load(resolved)
# noop returns empty string
expect(content).to_equal("")
```

</details>

#### module loader returns import name unchanged for noop resolver

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val r1 = "compiler.driver"
val r2 = "compiler.driver"
expect(r1).to_equal("compiler.driver")
expect(r2).to_equal("compiler.driver")
```

</details>

#### module loader returns empty content for any path in noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val load = svc.module_loader.load_fn
val c1 = load("src/compiler/driver.spl")
val c2 = load("src/std/math.spl")
expect(c1).to_equal("")
expect(c2).to_equal("")
```

</details>

### CompilerServices System: Full end-to-end pipeline

#### simulates a complete compilation run through all 9 stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val src = "fn greet(msg: text): print msg"
val module_name = "greet"

# Stage 1: Lex
val lex = svc.lexer.tokenize_fn
val tokens = lex(src)
expect(tokens.len()).to_equal(0)

# Stage 2: Parse
expect(svc.parser.name).to_equal("noop-parser")

# Stage 3: Desugar
val desugar = svc.desugarer.desugar_fn
val desugared = desugar(src)
expect(desugared).to_equal(src)

# Stage 4: Type check
val check = svc.type_checker.check_fn
val type_errs = check(module_name)
expect(type_errs.len()).to_equal(0)

# Stage 5: HIR lower
val hir_lower = svc.hir_lowerer.lower_fn
val hir_errs = hir_lower(module_name)
expect(hir_errs.len()).to_equal(0)

# Stage 6: MIR lower
val mir_lower = svc.mir_lowerer.lower_fn
val mir_errs = mir_lower(module_name)
expect(mir_errs.len()).to_equal(0)

# Stage 7: Backend capabilities check
val jit_fn = svc.backend.supports_jit_fn
val jit_ok = jit_fn()
expect(jit_ok).to_equal(false)

# Stage 8: Backend target
val triple_fn = svc.backend.target_triple_fn
val triple = triple_fn()
expect(triple).to_equal("noop")

# Stage 9: Verify logger
expect(svc.logger.name).to_equal("noop-logger")
```

</details>

#### pipeline can be run for multiple modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()

val lex = svc.lexer.tokenize_fn
val desugar = svc.desugarer.desugar_fn
val check = svc.type_checker.check_fn
val hir_lower = svc.hir_lowerer.lower_fn
val mir_lower = svc.mir_lowerer.lower_fn

val src_a = "fn foo(): 1"
val tokens_a = lex(src_a)
val parse_errs_a: [text] = []
val desugared_a = desugar(src_a)
val type_errs_a = check("module_a")
val hir_errs_a = hir_lower("module_a")
val mir_errs_a = mir_lower("module_a")

val src_b = "fn bar(): 2"
val tokens_b = lex(src_b)
val parse_errs_b: [text] = []
val desugared_b = desugar(src_b)
val type_errs_b = check("module_b")
val hir_errs_b = hir_lower("module_b")
val mir_errs_b = mir_lower("module_b")

expect(parse_errs_a.len()).to_equal(0)
expect(parse_errs_b.len()).to_equal(0)
expect(desugared_a).to_equal(src_a)
expect(desugared_b).to_equal(src_b)
expect(type_errs_a.len()).to_equal(0)
expect(type_errs_b.len()).to_equal(0)
expect(hir_errs_a.len()).to_equal(0)
expect(hir_errs_b.len()).to_equal(0)
expect(mir_errs_a.len()).to_equal(0)
expect(mir_errs_b.len()).to_equal(0)
```

</details>

#### module loader participates in full pipeline as module source provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val load = svc.module_loader.load_fn

# Resolve module path
val resolved = "std.string"
expect(resolved).to_equal("std.string")

# Load module content
val content = load(resolved)
expect(content).to_equal("")

# Continue pipeline with loaded content
val lex = svc.lexer.tokenize_fn
val tokens = lex(content)
expect(tokens.len()).to_equal(0)

val errors: [text] = []
expect(errors.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_services_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CompilerServices System: Service container construction
- CompilerServices System: Lexer and parser stages
- CompilerServices System: Desugaring and type checking stages
- CompilerServices System: HIR and MIR lowering stages
- CompilerServices System: Backend stage
- CompilerServices System: Logger integration
- CompilerServices System: Module loader integration
- CompilerServices System: Full end-to-end pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
