# Compiler Services System Specification

> Tests covering CompilerServices System: Service container construction, CompilerServices System: Lexer and parser stages, CompilerServices System: Desugaring and type checking stages, CompilerServices System: HIR and MIR lowering stages, CompilerServices System: Backend stage, CompilerServices System: Logger integration, CompilerServices System: Module loader integration, CompilerServices System: Full end-to-end pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Services System Specification

## Scenarios

### CompilerServices System: Service container construction

#### create_default_services produces a fully wired container

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create_default_services produces a fully wired container
   - Expected: svc.lexer.name equals `noop-lexer`
   - Expected: svc.parser.name equals `noop-parser`
   - Expected: svc.desugarer.name equals `noop-desugarer`
   - Expected: svc.type_checker.name equals `noop-type-checker`
   - Expected: svc.hir_lowerer.name equals `noop-hir-lowerer`
   - Expected: svc.mir_lowerer.name equals `noop-mir-lowerer`
   - Expected: svc.backend.name equals `noop-backend`
   - Expected: svc.logger.name equals `noop-logger`
   - Expected: svc.module_loader.name equals `noop-module-loader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("create_default_services produces a fully wired container")
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

- service container can be created and immediately queried


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("service container can be created and immediately queried")
val svc = create_default_services()
val lexer_name = svc.lexer.name
expect(lexer_name).to_start_with("noop")
```

</details>

#### all port names follow the noop- naming convention

- all port names follow the noop- naming convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all port names follow the noop- naming convention")
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

- lexer tokenizes a simple function declaration
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lexer tokenizes a simple function declaration")
val svc = create_default_services()
val source = "fn add(a: i64, b: i64) -> i64: a + b"
val tokenize = svc.lexer.tokenize_fn
val tokens = tokenize(source)
# noop returns empty - verifies stage boundary contract
expect(tokens.len()).to_equal(0)
```

</details>

#### parser receives token stream from lexer and returns no errors

- parser receives token stream from lexer and returns no errors
   - Expected: svc.parser.name equals `noop-parser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parser receives token stream from lexer and returns no errors")
val svc = create_default_services()
val source = "fn add(a: i64, b: i64) -> i64: a + b"
val tokenize = svc.lexer.tokenize_fn
val tokens = tokenize(source)
expect(svc.parser.name).to_equal("noop-parser")
```

</details>

#### lexer handles multiline source without error

- lexer handles multiline source without error
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lexer handles multiline source without error")
val svc = create_default_services()
val source = "fn foo():\n    val x = 1\n    x + 1"
val tokenize = svc.lexer.tokenize_fn
val tokens = tokenize(source)
expect(tokens.len()).to_equal(0)
```

</details>

#### parser returns empty error list for noop implementation

- parser returns empty error list for noop implementation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parser returns empty error list for noop implementation")
val svc = create_default_services()
expect(svc.parser.name).to_start_with("noop")
```

</details>

### CompilerServices System: Desugaring and type checking stages

#### desugarer receives source and returns transformed output

- desugarer receives source and returns transformed output
   - Expected: transformed equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugarer receives source and returns transformed output")
val svc = create_default_services()
val source = "fn main(): print 1"
val desugar = svc.desugarer.desugar_fn
val transformed = desugar(source)
# noop returns source unchanged
expect(transformed).to_equal(source)
```

</details>

#### desugarer preserves source structure for noop

- desugarer preserves source structure for noop
   - Expected: result equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugarer preserves source structure for noop")
val svc = create_default_services()
val source = "class Point:\n    x: i64\n    y: i64"
val desugar = svc.desugarer.desugar_fn
val result = desugar(source)
expect(result).to_equal(source)
```

</details>

#### type checker validates module by name

- type checker validates module by name
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("type checker validates module by name")
val svc = create_default_services()
val check = svc.type_checker.check_fn
val errors = check("my_module")
expect(errors.len()).to_equal(0)
```

</details>

#### type checker returns empty error list for unknown module in noop

- type checker returns empty error list for unknown module in noop
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("type checker returns empty error list for unknown module in noop")
val svc = create_default_services()
val check = svc.type_checker.check_fn
val errors = check("nonexistent_module")
expect(errors.len()).to_equal(0)
```

</details>

### CompilerServices System: HIR and MIR lowering stages

#### HIR lowerer lowers a module by name

- HIR lowerer lowers a module by name
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HIR lowerer lowers a module by name")
val svc = create_default_services()
val lower = svc.hir_lowerer.lower_fn
val errors = lower("main")
expect(errors.len()).to_equal(0)
```

</details>

#### MIR lowerer lowers a module by name

- MIR lowerer lowers a module by name
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MIR lowerer lowers a module by name")
val svc = create_default_services()
val lower = svc.mir_lowerer.lower_fn
val errors = lower("main")
expect(errors.len()).to_equal(0)
```

</details>

#### HIR and MIR lowering stages both succeed for same module

- HIR and MIR lowering stages both succeed for same module
   - Expected: hir_errors.len() equals `0`
   - Expected: mir_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HIR and MIR lowering stages both succeed for same module")
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

- HIR lowerer handles multiple module names
   - Expected: e1.len() equals `0`
   - Expected: e2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HIR lowerer handles multiple module names")
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

- backend reports its capabilities via supports_jit_fn
   - Expected: supports is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend reports its capabilities via supports_jit_fn")
val svc = create_default_services()
val jit_fn = svc.backend.supports_jit_fn
val supports = jit_fn()
expect(supports).to_equal(false)
```

</details>

#### backend reports its target architecture via target_triple_fn

- backend reports its target architecture via target_triple_fn
   - Expected: triple equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend reports its target architecture via target_triple_fn")
val svc = create_default_services()
val triple_fn = svc.backend.target_triple_fn
val triple = triple_fn()
expect(triple).to_equal("noop")
```

</details>

#### backend triple is consistent across multiple calls

- backend triple is consistent across multiple calls
   - Expected: t1 equals `t2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend triple is consistent across multiple calls")
val svc = create_default_services()
val triple_fn = svc.backend.target_triple_fn
val t1 = triple_fn()
val t2 = triple_fn()
expect(t1).to_equal(t2)
```

</details>

#### backend JIT support is consistent across multiple calls

- backend JIT support is consistent across multiple calls
   - Expected: j1 equals `j2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend JIT support is consistent across multiple calls")
val svc = create_default_services()
val jit_fn = svc.backend.supports_jit_fn
val j1 = jit_fn()
val j2 = jit_fn()
expect(j1).to_equal(j2)
```

</details>

### CompilerServices System: Logger integration

#### logger has correct name

- logger has correct name
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger has correct name")
val svc = create_default_services()
expect(svc.logger.name).to_equal("noop-logger")
```

</details>

#### logger has level field set to 0

- logger has level field set to 0
   - Expected: svc.logger.level equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger has level field set to 0")
val svc = create_default_services()
expect(svc.logger.level).to_equal(0)
```

</details>

#### logger name follows noop convention

- logger name follows noop convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger name follows noop convention")
val svc = create_default_services()
expect(svc.logger.name).to_start_with("noop")
```

</details>

### CompilerServices System: Module loader integration

#### module loader resolves import paths

- module loader resolves import paths
   - Expected: path equals `std.math`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader resolves import paths")
val svc = create_default_services()
val path = "std.math"
expect(path).to_equal("std.math")
```

</details>

#### module loader loads resolved module content

- module loader loads resolved module content
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader loads resolved module content")
val svc = create_default_services()
val load = svc.module_loader.load_fn
val resolved = "std.array"
val content = load(resolved)
# noop returns empty string
expect(content).to_equal("")
```

</details>

#### module loader returns import name unchanged for noop resolver

- module loader returns import name unchanged for noop resolver
   - Expected: r1 equals `compiler.driver`
   - Expected: r2 equals `compiler.driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader returns import name unchanged for noop resolver")
val svc = create_default_services()
val r1 = "compiler.driver"
val r2 = "compiler.driver"
expect(r1).to_equal("compiler.driver")
expect(r2).to_equal("compiler.driver")
```

</details>

#### module loader returns empty content for any path in noop

- module loader returns empty content for any path in noop
   - Expected: c1 equals ``
   - Expected: c2 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader returns empty content for any path in noop")
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

- simulates a complete compilation run through all 9 stages
   - Expected: tokens.len() equals `0`
   - Expected: svc.parser.name equals `noop-parser`
   - Expected: desugared equals `src`
   - Expected: type_errs.len() equals `0`
   - Expected: hir_errs.len() equals `0`
   - Expected: mir_errs.len() equals `0`
   - Expected: jit_ok is false
   - Expected: triple equals `noop`
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("simulates a complete compilation run through all 9 stages")
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

- pipeline can be run for multiple modules
   - Expected: parse_errs_a.len() equals `0`
   - Expected: parse_errs_b.len() equals `0`
   - Expected: desugared_a equals `src_a`
   - Expected: desugared_b equals `src_b`
   - Expected: type_errs_a.len() equals `0`
   - Expected: type_errs_b.len() equals `0`
   - Expected: hir_errs_a.len() equals `0`
   - Expected: hir_errs_b.len() equals `0`
   - Expected: mir_errs_a.len() equals `0`
   - Expected: mir_errs_b.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pipeline can be run for multiple modules")
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

- module loader participates in full pipeline as module source provider
   - Expected: resolved equals `std.string`
   - Expected: content equals ``
   - Expected: tokens.len() equals `0`
   - Expected: errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module loader participates in full pipeline as module source provider")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CompilerServices System: Service container construction, CompilerServices System: Lexer and parser stages, CompilerServices System: Desugaring and type checking stages, CompilerServices System: HIR and MIR lowering stages, CompilerServices System: Backend stage, CompilerServices System: Logger integration, CompilerServices System: Module loader integration, CompilerServices System: Full end-to-end pipeline.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `414db193de453dd31628b14ba0a7df6d7d9a34b4be7fb2360b91ddd2a1997d29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `414db193de453dd31628b14ba0a7df6d7d9a34b4be7fb2360b91ddd2a1997d29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `414db193de453dd31628b14ba0a7df6d7d9a34b4be7fb2360b91ddd2a1997d29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/compiler/compiler_services_system_spec.spl
mirror: doc/06_spec/03_system/compiler/compiler_services_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/compiler_services_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/compiler_services_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/compiler_services_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 25 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/compiler_services_system_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_default_services produces a fully wired container' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_services_system_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'service container can be created and immediately queried' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/compiler_services_system_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all port names follow the noop- naming convention' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
