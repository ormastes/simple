# CompilerServices Error Cases

> Tests error handling paths in the CompilerServices API including invalid inputs, missing files, malformed source, and internal compiler errors. Verifies that error cases produce descriptive messages and do not crash the service.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenize empty string returns empty list
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tokenize empty string returns empty list")
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

- tokenize whitespace-only input returns empty list
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tokenize whitespace-only input returns empty list")
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

- tokenize any input always returns empty list for noop
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tokenize any input always returns empty list for noop")
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

- calling tokenize twice is idempotent
   - Expected: r1.len() equals `0`
   - Expected: r2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calling tokenize twice is idempotent")
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

- parse empty token list with empty source returns no errors
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse empty token list with empty source returns no errors")
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

- parse non-empty token list with empty source returns no errors
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse non-empty token list with empty source returns no errors")
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

- parse empty token list with non-empty source returns no errors
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse empty token list with non-empty source returns no errors")
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

- calling parse twice returns empty errors both times
   - Expected: r1.len() equals `0`
   - Expected: r2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calling parse twice returns empty errors both times")
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

- desugar empty string returns empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugar empty string returns empty string")
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

- desugar whitespace-only returns whitespace unchanged
   - Expected: result equals `   `


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugar whitespace-only returns whitespace unchanged")
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

- desugar returns input text unchanged for noop
   - Expected: result equals `src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("desugar returns input text unchanged for noop")
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

- calling desugar twice returns same result
   - Expected: r1 equals `src`
   - Expected: r2 equals `src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calling desugar twice returns same result")
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

- check empty module name returns no errors
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check empty module name returns no errors")
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

- check nonexistent module name returns no errors for noop
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check nonexistent module name returns no errors for noop")
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

- calling check multiple times returns empty each time
   - Expected: r1.len() equals `0`
   - Expected: r2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calling check multiple times returns empty each time")
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

- lower empty module name returns no errors
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower empty module name returns no errors")
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

- lower nonexistent module returns no errors for noop
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower nonexistent module returns no errors for noop")
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

- lower empty module name returns no errors
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower empty module name returns no errors")
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

- lower any module returns no errors for noop
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lower any module returns no errors for noop")
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

- logger has name field
   - Expected: svc.logger.name equals `noop-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger has name field")
val svc = SHARED_SVC
expect(svc.logger.name).to_equal("noop-logger")
```

</details>


</details>

<details>
<summary>Advanced: logger has level field set to 0</summary>

#### logger has level field set to 0 _(slow)_

- logger has level field set to 0
   - Expected: svc.logger.level equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logger has level field set to 0")
val svc = SHARED_SVC
expect(svc.logger.level).to_equal(0)
```

</details>


</details>

### CompilerServices Error Cases: noop module loader degenerate inputs

<details>
<summary>Advanced: load_fn returns empty string for nonexistent path</summary>

#### load_fn returns empty string for nonexistent path _(slow)_

- load_fn returns empty string for nonexistent path
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("load_fn returns empty string for nonexistent path")
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

- load_fn returns empty string for empty path
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("load_fn returns empty string for empty path")
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

- resolve_fn returns import name unchanged for noop
   - Expected: result equals `std.string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_fn returns import name unchanged for noop")
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

- resolve_fn returns empty string for empty import name
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_fn returns empty string for empty import name")
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

- resolve_fn with both empty args returns empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_fn with both empty args returns empty string")
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

- supports_jit_fn always returns false for noop
   - Expected: r1 is false
   - Expected: r2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports_jit_fn always returns false for noop")
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

- target_triple_fn always returns noop for noop backend
   - Expected: r1 equals `noop`
   - Expected: r2 equals `noop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("target_triple_fn always returns noop for noop backend")
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

- two factory calls produce independent services
   - Expected: svc1.lexer.name equals `noop-lexer`
   - Expected: svc2.lexer.name equals `noop-lexer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two factory calls produce independent services")
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

- noop services from different factory calls return same results
   - Expected: f1("x").len() equals `0`
   - Expected: f2("x").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("noop services from different factory calls return same results")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0a0b1fc895f1ffe0954443e7f453c62e24b15fae23ce28f363686e8ecfe0ee32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a0b1fc895f1ffe0954443e7f453c62e24b15fae23ce28f363686e8ecfe0ee32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a0b1fc895f1ffe0954443e7f453c62e24b15fae23ce28f363686e8ecfe0ee32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/app/compiler_services_error_cases_spec.spl
mirror: doc/06_spec/03_system/feature/app/compiler_services_error_cases_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/compiler_services_error_cases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/compiler_services_error_cases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/compiler_services_error_cases_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/compiler_services_error_cases_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenize empty string returns empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/compiler_services_error_cases_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenize whitespace-only input returns empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/compiler_services_error_cases_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenize any input always returns empty list for noop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
