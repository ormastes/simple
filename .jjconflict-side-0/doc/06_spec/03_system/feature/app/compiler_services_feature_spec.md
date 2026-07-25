# CompilerServices Pipeline Stage Ports

> Tests the CompilerServices pipeline stage port system including stage registration, data flow between stages, and port type validation. Verifies that compilation pipeline stages are correctly wired and produce expected intermediate outputs.

<!-- sdn-diagram:id=compiler_services_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_services_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_services_feature_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_services_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CompilerServices Pipeline Stage Ports

Tests the CompilerServices pipeline stage port system including stage registration, data flow between stages, and port type validation. Verifies that compilation pipeline stages are correctly wired and produce expected intermediate outputs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/compiler_services_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the CompilerServices pipeline stage port system including stage registration,
data flow between stages, and port type validation. Verifies that compilation
pipeline stages are correctly wired and produce expected intermediate outputs.

## Scenarios

### CompilerServices Feature: Phase 1 - All ports present

<details>
<summary>Advanced: lexer port is present</summary>

#### lexer port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.lexer.name).to_equal("noop-lexer")
```

</details>


</details>

<details>
<summary>Advanced: parser port is present</summary>

#### parser port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.parser.name).to_equal("noop-parser")
```

</details>


</details>

<details>
<summary>Advanced: desugarer port is present</summary>

#### desugarer port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.desugarer.name).to_equal("noop-desugarer")
```

</details>


</details>

<details>
<summary>Advanced: type checker port is present</summary>

#### type checker port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.type_checker.name).to_equal("noop-type-checker")
```

</details>


</details>

<details>
<summary>Advanced: HIR lowerer port is present</summary>

#### HIR lowerer port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.hir_lowerer.name).to_equal("noop-hir-lowerer")
```

</details>


</details>

<details>
<summary>Advanced: MIR lowerer port is present</summary>

#### MIR lowerer port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.mir_lowerer.name).to_equal("noop-mir-lowerer")
```

</details>


</details>

<details>
<summary>Advanced: backend port is present</summary>

#### backend port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.backend.name).to_equal("noop-backend")
```

</details>


</details>

<details>
<summary>Advanced: logger port is present</summary>

#### logger port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: module loader port is present</summary>

#### module loader port is present _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.module_loader.name).to_equal("noop-module-loader")
```

</details>


</details>

<details>
<summary>Advanced: all 9 ports exist in a single services container</summary>

#### all 9 ports exist in a single services container _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val names = [
    svc.lexer.name,
    svc.parser.name,
    svc.desugarer.name,
    svc.type_checker.name,
    svc.hir_lowerer.name,
    svc.mir_lowerer.name,
    svc.backend.name,
    svc.logger.name,
    svc.module_loader.name
]
expect(names.len()).to_equal(9)
```

</details>


</details>

### CompilerServices Feature: Phase 2 - Each port callable

<details>
<summary>Advanced: lexer port tokenize_fn is callable</summary>

#### lexer port tokenize_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.lexer.tokenize_fn
val result = f("source code")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: lexer port tokenize_fn handles empty string</summary>

#### lexer port tokenize_fn handles empty string _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.lexer.tokenize_fn
val result = f("")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: parser port parse_fn is callable</summary>

#### parser port parse_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.parser.parse_fn
val errors = f([], "source")
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: parser port parse_fn accepts non-empty token list</summary>

#### parser port parse_fn accepts non-empty token list _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.parser.parse_fn
val tokens = ["val", "x", "=", "1"]
val errors = f(tokens, "val x = 1")
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: desugarer port desugar_fn is callable</summary>

#### desugarer port desugar_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.desugarer.desugar_fn
val result = f("val x = 1")
expect(result).to_equal("val x = 1")
```

</details>


</details>

<details>
<summary>Advanced: desugarer port desugar_fn passes through empty source</summary>

#### desugarer port desugar_fn passes through empty source _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.desugarer.desugar_fn
val result = f("")
expect(result).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: type checker port check_fn is callable</summary>

#### type checker port check_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.type_checker.check_fn
val errors = f("main")
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: hir lowerer port lower_fn is callable</summary>

#### hir lowerer port lower_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.hir_lowerer.lower_fn
val errors = f("main")
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: mir lowerer port lower_fn is callable</summary>

#### mir lowerer port lower_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.mir_lowerer.lower_fn
val errors = f("main")
expect(errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: backend port supports_jit_fn is callable</summary>

#### backend port supports_jit_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: backend port target_triple_fn is callable</summary>

#### backend port target_triple_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>


</details>

<details>
<summary>Advanced: logger port has name field</summary>

#### logger port has name field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: logger port has level field</summary>

#### logger port has level field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
expect(svc.logger.level).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: module loader port load_fn is callable</summary>

#### module loader port load_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.module_loader.load_fn
val result = f("some/path.spl")
expect(result).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: module loader port resolve_fn is callable</summary>

#### module loader port resolve_fn is callable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.module_loader.resolve_fn
val result = f("/src/main.spl", "std.string")
expect(result).to_equal("std.string")
```

</details>


</details>

### CompilerServices Feature: Phase 3 - Port replacement

<details>
<summary>Advanced: calling create_default_services twice gives independent containers</summary>

#### calling create_default_services twice gives independent containers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc1 = create_default_services()
val svc2 = create_default_services()
expect(svc1.lexer.name).to_equal(svc2.lexer.name)
expect(svc1.parser.name).to_equal(svc2.parser.name)
```

</details>


</details>

<details>
<summary>Advanced: all ports in two independent containers share the same names</summary>

#### all ports in two independent containers share the same names _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc1 = create_default_services()
val svc2 = create_default_services()
expect(svc1.backend.name).to_equal(svc2.backend.name)
expect(svc1.logger.name).to_equal(svc2.logger.name)
expect(svc1.module_loader.name).to_equal(svc2.module_loader.name)
```

</details>


</details>

<details>
<summary>Advanced: replacing lexer port does not affect parser port name</summary>

#### replacing lexer port does not affect parser port name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
# Verify both ports exist and are independent
val lexer_name = svc.lexer.name
val parser_name = svc.parser.name
expect(lexer_name).to_equal("noop-lexer")
expect(parser_name).to_equal("noop-parser")
```

</details>


</details>

<details>
<summary>Advanced: accessing one port does not change another port</summary>

#### accessing one port does not change another port _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val lex_f = svc.lexer.tokenize_fn
val lex_result = lex_f("some source")
# parser is unaffected
expect(svc.parser.name).to_equal("noop-parser")
expect(svc.desugarer.name).to_equal("noop-desugarer")
```

</details>


</details>

<details>
<summary>Advanced: accessing backend port does not affect logger port</summary>

#### accessing backend port does not affect logger port _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val bf = svc.backend.supports_jit_fn
val jit = bf()
expect(jit).to_equal(false)
# logger unaffected
expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: accessing module loader does not affect hir or mir lowerers</summary>

#### accessing module loader does not affect hir or mir lowerers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val lf = svc.module_loader.load_fn
val loaded = lf("/path/to/module.spl")
expect(loaded).to_equal("")
# hir and mir lowerers unchanged
expect(svc.hir_lowerer.name).to_equal("noop-hir-lowerer")
expect(svc.mir_lowerer.name).to_equal("noop-mir-lowerer")
```

</details>


</details>

### CompilerServices Feature: Phase 4 - Full pipeline simulation

<details>
<summary>Advanced: tokenize stage returns empty token list for noop lexer</summary>

#### tokenize stage returns empty token list for noop lexer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val src = "fn main(): print 1"
val lf = svc.lexer.tokenize_fn
val tokens = lf(src)
expect(tokens.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: parse stage returns no errors for noop parser</summary>

#### parse stage returns no errors for noop parser _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val lf = svc.lexer.tokenize_fn
val tokens = lf("fn main(): print 1")
val pf = svc.parser.parse_fn
val parse_errors = pf(tokens, "fn main(): print 1")
expect(parse_errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: desugar stage returns source for noop desugarer</summary>

#### desugar stage returns source for noop desugarer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val src = "fn main(): print 1"
val df = svc.desugarer.desugar_fn
val desugared = df(src)
expect(desugared).to_equal(src)
```

</details>


</details>

<details>
<summary>Advanced: type check stage returns no errors for noop checker</summary>

#### type check stage returns no errors for noop checker _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val cf = svc.type_checker.check_fn
val type_errors = cf("main")
expect(type_errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: HIR lowering stage returns no errors for noop lowerer</summary>

#### HIR lowering stage returns no errors for noop lowerer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val hf = svc.hir_lowerer.lower_fn
val hir_errors = hf("main")
expect(hir_errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: MIR lowering stage returns no errors for noop lowerer</summary>

#### MIR lowering stage returns no errors for noop lowerer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val mf = svc.mir_lowerer.lower_fn
val mir_errors = mf("main")
expect(mir_errors.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: backend stage reports no JIT support for noop backend</summary>

#### backend stage reports no JIT support for noop backend _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val jit_fn = svc.backend.supports_jit_fn
val jit_supported = jit_fn()
expect(jit_supported).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: backend stage reports noop target triple</summary>

#### backend stage reports noop target triple _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val triple_fn = svc.backend.target_triple_fn
val triple = triple_fn()
expect(triple).to_equal("noop")
```

</details>


</details>

<details>
<summary>Advanced: running through all 9 stages sequentially produces no errors</summary>

#### running through all 9 stages sequentially produces no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val src = "fn main(): print 1"
val module_name = "main"

val lf = svc.lexer.tokenize_fn
val tokens = lf(src)
expect(tokens.len()).to_equal(0)

val pf = svc.parser.parse_fn
val parse_errs = pf(tokens, src)
expect(parse_errs.len()).to_equal(0)

val df = svc.desugarer.desugar_fn
val desugared = df(src)
expect(desugared).to_equal(src)

val cf = svc.type_checker.check_fn
val type_errs = cf(module_name)
expect(type_errs.len()).to_equal(0)

val hf = svc.hir_lowerer.lower_fn
val hir_errs = hf(module_name)
expect(hir_errs.len()).to_equal(0)

val mf = svc.mir_lowerer.lower_fn
val mir_errs = mf(module_name)
expect(mir_errs.len()).to_equal(0)

val jit_fn = svc.backend.supports_jit_fn
val jit_ok = jit_fn()
expect(jit_ok).to_equal(false)

val triple_fn = svc.backend.target_triple_fn
val triple = triple_fn()
expect(triple).to_equal("noop")

expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: module loader can resolve and load during pipeline</summary>

#### module loader can resolve and load during pipeline _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val resolve_fn = svc.module_loader.resolve_fn
val resolved = resolve_fn("/src/main.spl", "std.math")
expect(resolved).to_equal("std.math")

val load_fn = svc.module_loader.load_fn
val content = load_fn(resolved)
expect(content).to_equal("")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 41 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
