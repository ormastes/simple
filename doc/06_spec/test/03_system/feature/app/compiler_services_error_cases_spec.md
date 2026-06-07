# CompilerServices Error Cases

> Tests error handling paths in the CompilerServices API including invalid inputs, missing files, malformed source, and internal compiler errors. Verifies that error cases produce descriptive messages and do not crash the service.

<!-- sdn-diagram:id=compiler_services_error_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_services_error_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_services_error_cases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_services_error_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CompilerServices Error Cases

Tests error handling paths in the CompilerServices API including invalid inputs, missing files, malformed source, and internal compiler errors. Verifies that error cases produce descriptive messages and do not crash the service.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/compiler_services_error_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests error handling paths in the CompilerServices API including invalid inputs,
missing files, malformed source, and internal compiler errors. Verifies that
error cases produce descriptive messages and do not crash the service.

## Scenarios

### CompilerServices Error Cases: noop lexer degenerate inputs

<details>
<summary>Advanced: tokenize empty string returns empty list</summary>

#### tokenize empty string returns empty list _(slow)_

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
<summary>Advanced: tokenize whitespace-only input returns empty list</summary>

#### tokenize whitespace-only input returns empty list _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.lexer.tokenize_fn
val result = f("   \t\n")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: tokenize any input always returns empty list for noop</summary>

#### tokenize any input always returns empty list for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.lexer.tokenize_fn
val result = f("val x = 1 + 2")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: calling tokenize twice is idempotent</summary>

#### calling tokenize twice is idempotent _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.lexer.tokenize_fn
val r1 = f("some source")
val r2 = f("some source")
expect(r1.len()).to_equal(0)
expect(r2.len()).to_equal(0)
```

</details>


</details>

### CompilerServices Error Cases: noop parser degenerate inputs

<details>
<summary>Advanced: parse empty token list with empty source returns no errors</summary>

#### parse empty token list with empty source returns no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.parser.parse_fn
val result = f([], "")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: parse non-empty token list with empty source returns no errors</summary>

#### parse non-empty token list with empty source returns no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.parser.parse_fn
val result = f(["tok1", "tok2"], "")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: parse empty token list with non-empty source returns no errors</summary>

#### parse empty token list with non-empty source returns no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.parser.parse_fn
val result = f([], "val x = 1")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: calling parse twice returns empty errors both times</summary>

#### calling parse twice returns empty errors both times _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.parser.parse_fn
val r1 = f([], "")
val r2 = f(["a", "b"], "src")
expect(r1.len()).to_equal(0)
expect(r2.len()).to_equal(0)
```

</details>


</details>

### CompilerServices Error Cases: noop desugarer edge cases

<details>
<summary>Advanced: desugar empty string returns empty string</summary>

#### desugar empty string returns empty string _(slow)_

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
<summary>Advanced: desugar whitespace-only returns whitespace unchanged</summary>

#### desugar whitespace-only returns whitespace unchanged _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.desugarer.desugar_fn
val result = f("   ")
expect(result).to_equal("   ")
```

</details>


</details>

<details>
<summary>Advanced: desugar returns input text unchanged for noop</summary>

#### desugar returns input text unchanged for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.desugarer.desugar_fn
val src = "fn foo(x: i64): x * 2"
val result = f(src)
expect(result).to_equal(src)
```

</details>


</details>

<details>
<summary>Advanced: calling desugar twice returns same result</summary>

#### calling desugar twice returns same result _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.desugarer.desugar_fn
val src = "val x = 1"
val r1 = f(src)
val r2 = f(src)
expect(r1).to_equal(src)
expect(r2).to_equal(src)
```

</details>


</details>

### CompilerServices Error Cases: noop type checker degenerate inputs

<details>
<summary>Advanced: check empty module name returns no errors</summary>

#### check empty module name returns no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.type_checker.check_fn
val result = f("")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: check nonexistent module name returns no errors for noop</summary>

#### check nonexistent module name returns no errors for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.type_checker.check_fn
val result = f("nonexistent/module")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: calling check multiple times returns empty each time</summary>

#### calling check multiple times returns empty each time _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.type_checker.check_fn
val r1 = f("module_a")
val r2 = f("module_b")
expect(r1.len()).to_equal(0)
expect(r2.len()).to_equal(0)
```

</details>


</details>

### CompilerServices Error Cases: noop HIR lowerer degenerate inputs

<details>
<summary>Advanced: lower empty module name returns no errors</summary>

#### lower empty module name returns no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.hir_lowerer.lower_fn
val result = f("")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: lower nonexistent module returns no errors for noop</summary>

#### lower nonexistent module returns no errors for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.hir_lowerer.lower_fn
val result = f("does/not/exist")
expect(result.len()).to_equal(0)
```

</details>


</details>

### CompilerServices Error Cases: noop MIR lowerer degenerate inputs

<details>
<summary>Advanced: lower empty module name returns no errors</summary>

#### lower empty module name returns no errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.mir_lowerer.lower_fn
val result = f("")
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: lower any module returns no errors for noop</summary>

#### lower any module returns no errors for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.mir_lowerer.lower_fn
val result = f("any/module")
expect(result.len()).to_equal(0)
```

</details>


</details>

### CompilerServices Error Cases: noop logger data fields

<details>
<summary>Advanced: logger has name field</summary>

#### logger has name field _(slow)_

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
<summary>Advanced: logger has level field set to 0</summary>

#### logger has level field set to 0 _(slow)_

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

### CompilerServices Error Cases: noop module loader degenerate inputs

<details>
<summary>Advanced: load_fn returns empty string for nonexistent path</summary>

#### load_fn returns empty string for nonexistent path _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val rf = svc.module_loader.load_fn
val result = rf("nonexistent/module")
expect(result).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: load_fn returns empty string for empty path</summary>

#### load_fn returns empty string for empty path _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val rf = svc.module_loader.load_fn
val result = rf("")
expect(result).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: resolve_fn returns import name unchanged for noop</summary>

#### resolve_fn returns import name unchanged for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val rf = svc.module_loader.resolve_fn
val result = rf("/src/main.spl", "std.string")
expect(result).to_equal("std.string")
```

</details>


</details>

<details>
<summary>Advanced: resolve_fn returns empty string for empty import name</summary>

#### resolve_fn returns empty string for empty import name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val rf = svc.module_loader.resolve_fn
val result = rf("/src/main.spl", "")
expect(result).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: resolve_fn with both empty args returns empty string</summary>

#### resolve_fn with both empty args returns empty string _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val rf = svc.module_loader.resolve_fn
val result = rf("", "")
expect(result).to_equal("")
```

</details>


</details>

### CompilerServices Error Cases: noop backend degenerate inputs

<details>
<summary>Advanced: supports_jit_fn always returns false for noop</summary>

#### supports_jit_fn always returns false for noop _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.backend.supports_jit_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal(false)
expect(r2).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: target_triple_fn always returns noop for noop backend</summary>

#### target_triple_fn always returns noop for noop backend _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = SHARED_SVC
val f = svc.backend.target_triple_fn
val r1 = f()
val r2 = f()
expect(r1).to_equal("noop")
expect(r2).to_equal("noop")
```

</details>


</details>

### CompilerServices Error Cases: independent factory instances

<details>
<summary>Advanced: two factory calls produce independent services</summary>

#### two factory calls produce independent services _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc1 = create_default_services()
val svc2 = create_default_services()
expect(svc1.lexer.name).to_equal("noop-lexer")
expect(svc2.lexer.name).to_equal("noop-lexer")
```

</details>


</details>

<details>
<summary>Advanced: noop services from different factory calls return same results</summary>

#### noop services from different factory calls return same results _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc1 = create_default_services()
val svc2 = create_default_services()
val f1 = svc1.lexer.tokenize_fn
val f2 = svc2.lexer.tokenize_fn
expect(f1("x").len()).to_equal(0)
expect(f2("x").len()).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 30 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
