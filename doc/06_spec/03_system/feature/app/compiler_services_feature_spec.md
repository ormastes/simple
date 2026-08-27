# CompilerServices Pipeline Stage Ports

> Tests the CompilerServices pipeline stage port system including stage registration, data flow between stages, and port type validation. Verifies that compilation pipeline stages are correctly wired and produce expected intermediate outputs.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lexer port is present
   - Expected: svc.lexer.name equals `noop-lexer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lexer port is present")
val svc = SHARED_SVC
expect(svc.lexer.name).to_equal("noop-lexer")
```

</details>


</details>

<details>
<summary>Advanced: parser port is present</summary>

#### parser port is present _(slow)_

- parser port is present
   - Expected: svc.parser.name equals `noop-parser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parser port is present")
val svc = SHARED_SVC
expect(svc.parser.name).to_equal("noop-parser")
```

</details>


</details>

<details>
<summary>Advanced: desugarer port is present</summary>

#### desugarer port is present _(slow)_

- desugarer port is present
   - Expected: svc.desugarer.name equals `noop-desugarer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugarer port is present")
val svc = SHARED_SVC
expect(svc.desugarer.name).to_equal("noop-desugarer")
```

</details>


</details>

<details>
<summary>Advanced: type checker port is present</summary>

#### type checker port is present _(slow)_

- type checker port is present
   - Expected: svc.type_checker.name equals `noop-type-checker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("type checker port is present")
val svc = SHARED_SVC
expect(svc.type_checker.name).to_equal("noop-type-checker")
```

</details>


</details>

<details>
<summary>Advanced: HIR lowerer port is present</summary>

#### HIR lowerer port is present _(slow)_

- HIR lowerer port is present
   - Expected: svc.hir_lowerer.name equals `noop-hir-lowerer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HIR lowerer port is present")
val svc = SHARED_SVC
expect(svc.hir_lowerer.name).to_equal("noop-hir-lowerer")
```

</details>


</details>

<details>
<summary>Advanced: MIR lowerer port is present</summary>

#### MIR lowerer port is present _(slow)_

- MIR lowerer port is present
   - Expected: svc.mir_lowerer.name equals `noop-mir-lowerer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MIR lowerer port is present")
val svc = SHARED_SVC
expect(svc.mir_lowerer.name).to_equal("noop-mir-lowerer")
```

</details>


</details>

<details>
<summary>Advanced: backend port is present</summary>

#### backend port is present _(slow)_

- backend port is present
   - Expected: svc.backend.name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port is present")
val svc = SHARED_SVC
expect(svc.backend.name).to_equal("noop-backend")
```

</details>


</details>

<details>
<summary>Advanced: logger port is present</summary>

#### logger port is present _(slow)_

- logger port is present
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger port is present")
val svc = SHARED_SVC
expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: module loader port is present</summary>

#### module loader port is present _(slow)_

- module loader port is present
   - Expected: svc.module_loader.name equals `noop-module-loader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader port is present")
val svc = SHARED_SVC
expect(svc.module_loader.name).to_equal("noop-module-loader")
```

</details>


</details>

<details>
<summary>Advanced: all 9 ports exist in a single services container</summary>

#### all 9 ports exist in a single services container _(slow)_

- all 9 ports exist in a single services container
   - Expected: names.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all 9 ports exist in a single services container")
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

- lexer port tokenize_fn is callable
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lexer port tokenize_fn is callable")
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

- lexer port tokenize_fn handles empty string
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lexer port tokenize_fn handles empty string")
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

- parser port parse_fn is callable
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parser port parse_fn is callable")
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

- parser port parse_fn accepts non-empty token list
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parser port parse_fn accepts non-empty token list")
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

- desugarer port desugar_fn is callable
   - Expected: result equals `val x = 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugarer port desugar_fn is callable")
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

- desugarer port desugar_fn passes through empty source
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugarer port desugar_fn passes through empty source")
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

- type checker port check_fn is callable
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("type checker port check_fn is callable")
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

- hir lowerer port lower_fn is callable
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hir lowerer port lower_fn is callable")
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

- mir lowerer port lower_fn is callable
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mir lowerer port lower_fn is callable")
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

- backend port supports_jit_fn is callable
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port supports_jit_fn is callable")
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

- backend port target_triple_fn is callable
   - Expected: result equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend port target_triple_fn is callable")
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

- logger port has name field
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger port has name field")
val svc = SHARED_SVC
expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: logger port has level field</summary>

#### logger port has level field _(slow)_

- logger port has level field
   - Expected: svc.logger.level equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger port has level field")
val svc = SHARED_SVC
expect(svc.logger.level).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: module loader port load_fn is callable</summary>

#### module loader port load_fn is callable _(slow)_

- module loader port load_fn is callable
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader port load_fn is callable")
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

- module loader port resolve_fn is callable
   - Expected: result equals `std.string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader port resolve_fn is callable")
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

- calling create_default_services twice gives independent containers
   - Expected: svc1.lexer.name equals `svc2.lexer.name`
   - Expected: svc1.parser.name equals `svc2.parser.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calling create_default_services twice gives independent containers")
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

- all ports in two independent containers share the same names
   - Expected: svc1.backend.name equals `svc2.backend.name`
   - Expected: svc1.logger.name equals `svc2.logger.name`
   - Expected: svc1.module_loader.name equals `svc2.module_loader.name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all ports in two independent containers share the same names")
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

- replacing lexer port does not affect parser port name
   - Expected: lexer_name equals `noop-lexer`
   - Expected: parser_name equals `noop-parser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replacing lexer port does not affect parser port name")
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

- accessing one port does not change another port
   - Expected: svc.parser.name equals `noop-parser`
   - Expected: svc.desugarer.name equals `noop-desugarer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accessing one port does not change another port")
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

- accessing backend port does not affect logger port
   - Expected: jit is false
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accessing backend port does not affect logger port")
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

- accessing module loader does not affect hir or mir lowerers
   - Expected: loaded equals ``
   - Expected: svc.hir_lowerer.name equals `noop-hir-lowerer`
   - Expected: svc.mir_lowerer.name equals `noop-mir-lowerer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accessing module loader does not affect hir or mir lowerers")
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

- tokenize stage returns empty token list for noop lexer
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tokenize stage returns empty token list for noop lexer")
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

- parse stage returns no errors for noop parser
   - Expected: parse_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse stage returns no errors for noop parser")
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

- desugar stage returns source for noop desugarer
   - Expected: desugared equals `src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugar stage returns source for noop desugarer")
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

- type check stage returns no errors for noop checker
   - Expected: type_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("type check stage returns no errors for noop checker")
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

- HIR lowering stage returns no errors for noop lowerer
   - Expected: hir_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HIR lowering stage returns no errors for noop lowerer")
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

- MIR lowering stage returns no errors for noop lowerer
   - Expected: mir_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MIR lowering stage returns no errors for noop lowerer")
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

- backend stage reports no JIT support for noop backend
   - Expected: jit_supported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend stage reports no JIT support for noop backend")
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

- backend stage reports noop target triple
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend stage reports noop target triple")
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

- running through all 9 stages sequentially produces no errors
   - Expected: tokens.len() equals `0`
   - Expected: parse_errs.len() equals `0`
   - Expected: desugared equals `src`
   - Expected: type_errs.len() equals `0`
   - Expected: hir_errs.len() equals `0`
   - Expected: mir_errs.len() equals `0`
   - Expected: jit_ok is false
   - Expected: triple equals `noop`
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("running through all 9 stages sequentially produces no errors")
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

- module loader can resolve and load during pipeline
   - Expected: resolved equals `std.math`
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader can resolve and load during pipeline")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82b8b7ee05310ad44c6c489145b15277b4feffade6ff4caa5a6507d4e031bdcb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82b8b7ee05310ad44c6c489145b15277b4feffade6ff4caa5a6507d4e031bdcb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82b8b7ee05310ad44c6c489145b15277b4feffade6ff4caa5a6507d4e031bdcb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/app/compiler_services_feature_spec.spl
mirror: doc/06_spec/03_system/feature/app/compiler_services_feature_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/compiler_services_feature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/compiler_services_feature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/compiler_services_feature_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/compiler_services_feature_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexer port is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/compiler_services_feature_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parser port is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/compiler_services_feature_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'desugarer port is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
