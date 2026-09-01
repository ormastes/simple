# Occurs Check Structural Specification

> Tests covering occurs_check — reproducer (T = [T]), occurs_check — detection across every composite shape, occurs_check — nesting and substitution, occurs_check — must not over-report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Occurs Check Structural Specification

## Scenarios

### occurs_check — reproducer (T = [T])

#### detects the variable inside its own array element type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects the variable inside its own array element type
   - Expected: occurs_check(t, arr_of_t) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects the variable inside its own array element type")
val t = fresh_var()
val arr_of_t = array_generic_type_register(t)
expect(occurs_check(t, arr_of_t)).to_equal(true)
```

</details>

#### makes unify_types reject the infinite type T = [T]

- makes unify_types reject the infinite type T = [T]
   - Expected: unify_types(t, arr_of_t) equals `UNIFY_FAIL_OCCURS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes unify_types reject the infinite type T = [T]")
val t = fresh_var()
val arr_of_t = array_generic_type_register(t)
expect(unify_types(t, arr_of_t)).to_equal(UNIFY_FAIL_OCCURS)
```

</details>

#### still unifies a variable with an array that does NOT contain it

- still unifies a variable with an array that does NOT contain it
   - Expected: unify_types(t, arr_of_i64) equals `UNIFY_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still unifies a variable with an array that does NOT contain it")
val t = fresh_var()
val arr_of_i64 = array_generic_type_register(TYPE_I64)
expect(unify_types(t, arr_of_i64)).to_equal(UNIFY_SUCCESS)
```

</details>

### occurs_check — detection across every composite shape

#### detects T inside a tuple (T, i64)

- detects T inside a tuple (T, i64)
   - Expected: occurs_check(t, tuple_type_register([t, TYPE_I64])) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T inside a tuple (T, i64)")
val t = fresh_var()
expect(occurs_check(t, tuple_type_register([t, TYPE_I64]))).to_equal(true)
```

</details>

#### detects T inside a tuple in trailing position (i64, T)

- detects T inside a tuple in trailing position (i64, T)
   - Expected: occurs_check(t, tuple_type_register([TYPE_I64, t])) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T inside a tuple in trailing position (i64, T)")
val t = fresh_var()
expect(occurs_check(t, tuple_type_register([TYPE_I64, t]))).to_equal(true)
```

</details>

#### detects T as a function return type: T = fn() -> T

- detects T as a function return type: T = fn() -> T
   - Expected: occurs_check_fn(t, [], t) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T as a function return type: T = fn() -> T")
val t = fresh_var()
expect(occurs_check_fn(t, [], t)).to_equal(true)
```

</details>

#### detects T as a function parameter type: T = fn(T) -> i64

- detects T as a function parameter type: T = fn(T) -> i64
   - Expected: occurs_check_fn(t, [t], TYPE_I64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T as a function parameter type: T = fn(T) -> i64")
val t = fresh_var()
expect(occurs_check_fn(t, [t], TYPE_I64)).to_equal(true)
```

</details>

#### detects T in a dict key: Dict<T, i64>

- detects T in a dict key: Dict<T, i64>
   - Expected: occurs_check(t, dict_type_register(t, TYPE_I64)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T in a dict key: Dict<T, i64>")
val t = fresh_var()
expect(occurs_check(t, dict_type_register(t, TYPE_I64))).to_equal(true)
```

</details>

#### detects T in a dict value: Dict<text, T>

- detects T in a dict value: Dict<text, T>
   - Expected: occurs_check(t, dict_type_register(TYPE_TEXT, t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T in a dict value: Dict<text, T>")
val t = fresh_var()
expect(occurs_check(t, dict_type_register(TYPE_TEXT, t))).to_equal(true)
```

</details>

#### detects T in a Result ok arm

- detects T in a Result ok arm
   - Expected: occurs_check(t, result_type_register(t, TYPE_TEXT)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T in a Result ok arm")
val t = fresh_var()
expect(occurs_check(t, result_type_register(t, TYPE_TEXT))).to_equal(true)
```

</details>

#### detects T in a Result err arm

- detects T in a Result err arm
   - Expected: occurs_check(t, result_type_register(TYPE_I64, t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T in a Result err arm")
val t = fresh_var()
expect(occurs_check(t, result_type_register(TYPE_I64, t))).to_equal(true)
```

</details>

#### detects T inside an Option<T>

- detects T inside an Option<T>
   - Expected: occurs_check(t, option_generic_type_register(t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T inside an Option<T>")
val t = fresh_var()
expect(occurs_check(t, option_generic_type_register(t))).to_equal(true)
```

</details>

#### detects T inside a union member

- detects T inside a union member
   - Expected: occurs_check(t, union_type_register([TYPE_I64, t])) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T inside a union member")
val t = fresh_var()
expect(occurs_check(t, union_type_register([TYPE_I64, t]))).to_equal(true)
```

</details>

#### detects T behind a reference wrapper

- detects T behind a reference wrapper
   - Expected: occurs_check(t, reference_type_register(t, false)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T behind a reference wrapper")
val t = fresh_var()
expect(occurs_check(t, reference_type_register(t, false))).to_equal(true)
```

</details>

#### detects T behind a pointer wrapper

- detects T behind a pointer wrapper
   - Expected: occurs_check(t, pointer_type_register(t, true)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T behind a pointer wrapper")
val t = fresh_var()
expect(occurs_check(t, pointer_type_register(t, true))).to_equal(true)
```

</details>

#### detects T behind an iso wrapper

- detects T behind an iso wrapper
   - Expected: occurs_check(t, isolated_type_register(t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T behind an iso wrapper")
val t = fresh_var()
expect(occurs_check(t, isolated_type_register(t))).to_equal(true)
```

</details>

#### detects T behind an exclusive wrapper

- detects T behind an exclusive wrapper
   - Expected: occurs_check(t, exclusive_type_register(t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T behind an exclusive wrapper")
val t = fresh_var()
expect(occurs_check(t, exclusive_type_register(t))).to_equal(true)
```

</details>

#### detects T behind an atomic wrapper

- detects T behind an atomic wrapper
   - Expected: occurs_check(t, atomic_type_register(t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T behind an atomic wrapper")
val t = fresh_var()
expect(occurs_check(t, atomic_type_register(t))).to_equal(true)
```

</details>

#### detects T behind a weak wrapper

- detects T behind a weak wrapper
   - Expected: occurs_check(t, weak_type_register(t)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T behind a weak wrapper")
val t = fresh_var()
expect(occurs_check(t, weak_type_register(t))).to_equal(true)
```

</details>

### occurs_check — nesting and substitution

#### detects T nested several composites deep: Dict<i64, [Option<T>]>

- detects T nested several composites deep: Dict<i64, [Option<T>]>
   - Expected: occurs_check(t, dict_type_register(TYPE_I64, arr)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects T nested several composites deep: Dict<i64, [Option<T>]>")
val t = fresh_var()
val opt_t = option_generic_type_register(t)
val arr = array_generic_type_register(opt_t)
expect(occurs_check(t, dict_type_register(TYPE_I64, arr))).to_equal(true)
```

</details>

#### follows substitutions: U bound to [T] makes T occur in U

- follows substitutions: U bound to [T] makes T occur in U
   - Expected: occurs_check(t, u) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows substitutions: U bound to [T] makes T occur in U")
type_var_reset()
unify_reset()
val t = type_var_fresh()
val u = type_var_fresh()
unify_bind(u, array_generic_type_register(t))
expect(occurs_check(t, u)).to_equal(true)
```

</details>

### occurs_check — must not over-report

#### reports false for an unrelated scalar

- reports false for an unrelated scalar
   - Expected: occurs_check(t, TYPE_I64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false for an unrelated scalar")
val t = fresh_var()
expect(occurs_check(t, TYPE_I64)).to_equal(false)
```

</details>

#### reports false for a composite built only from scalars

- reports false for a composite built only from scalars
   - Expected: occurs_check(t, tuple_type_register([inner, TYPE_I64])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false for a composite built only from scalars")
val t = fresh_var()
val inner = dict_type_register(TYPE_TEXT, TYPE_BOOL)
expect(occurs_check(t, tuple_type_register([inner, TYPE_I64]))).to_equal(false)
```

</details>

#### reports false for a DIFFERENT variable nested in a composite

- reports false for a DIFFERENT variable nested in a composite
   - Expected: occurs_check(t, array_generic_type_register(other)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false for a DIFFERENT variable nested in a composite")
type_var_reset()
unify_reset()
val t = type_var_fresh()
val other = type_var_fresh()
expect(occurs_check(t, array_generic_type_register(other))).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_checker/occurs_check_structural_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering occurs_check — reproducer (T = [T]), occurs_check — detection across every composite shape, occurs_check — nesting and substitution, occurs_check — must not over-report.
- occurs_check — reproducer (T = [T])
- occurs_check — detection across every composite shape
- occurs_check — nesting and substitution
- occurs_check — must not over-report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `98dd8f3a3eaac95f0d2ef16ff15b3ee1041c735cbb012ab80b1e6d9f28c69f62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98dd8f3a3eaac95f0d2ef16ff15b3ee1041c735cbb012ab80b1e6d9f28c69f62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98dd8f3a3eaac95f0d2ef16ff15b3ee1041c735cbb012ab80b1e6d9f28c69f62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/type_checker/occurs_check_structural_spec.spl
mirror: doc/06_spec/01_unit/compiler/type_checker/occurs_check_structural_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/type_checker/occurs_check_structural_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/type_checker/occurs_check_structural_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/type_checker/occurs_check_structural_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the variable inside its own array element type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/type_checker/occurs_check_structural_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes unify_types reject the infinite type T = [T]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/type_checker/occurs_check_structural_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still unifies a variable with an array that does NOT contain it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
