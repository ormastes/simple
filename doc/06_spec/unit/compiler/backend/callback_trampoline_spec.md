# Callback Trampoline Specification

> Purpose: Prove that callback trampoline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Callback Trampoline Specification

Purpose: Prove that callback trampoline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR #SFFI-CALLBACK #WS5 |
| Category | Compiler / Backend / Callback Trampoline |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/unit/compiler/backend/callback_trampoline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that callback trampoline.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### callback trampoline

### is_callback_type

#### accepts plain function pointer types

- accepts plain function pointer types
- Verify: accepts plain function pointer types
   - Expected: is_callback_type("Fn<(i64) -> i64>") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts plain function pointer types")
step("Verify: accepts plain function pointer types")
# @req: REQ-COMP-CALLBACK-TRAMPOLINE-001
expect(is_callback_type("Fn<(i64) -> i64>")).to_equal(true)
```

</details>

#### accepts multi-param function pointers

- accepts multi-param function pointers
- Verify: accepts multi-param function pointers
   - Expected: is_callback_type("Fn<(i64, f64) -> bool>") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts multi-param function pointers")
step("Verify: accepts multi-param function pointers")
expect(is_callback_type("Fn<(i64, f64) -> bool>")).to_equal(true)
```

</details>

#### accepts no-arg function pointers

- accepts no-arg function pointers
- Verify: accepts no-arg function pointers
   - Expected: is_callback_type("Fn<() -> void>") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts no-arg function pointers")
step("Verify: accepts no-arg function pointers")
expect(is_callback_type("Fn<() -> void>")).to_equal(true)
```

</details>

#### rejects closures with captures

- rejects closures with captures
- Verify: rejects closures with captures
   - Expected: is_callback_type("Fn<(i64) -> i64>[x, y]") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects closures with captures")
step("Verify: rejects closures with captures")
expect(is_callback_type("Fn<(i64) -> i64>[x, y]")).to_equal(false)
```

</details>

#### rejects non-function types

- rejects non-function types
- Verify: rejects non-function types
   - Expected: is_callback_type("i64") is false
   - Expected: is_callback_type("text") is false
   - Expected: is_callback_type("List<i64>") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-function types")
step("Verify: rejects non-function types")
expect(is_callback_type("i64")).to_equal(false)
expect(is_callback_type("text")).to_equal(false)
expect(is_callback_type("List<i64>")).to_equal(false)
```

</details>

### is_closure_with_captures

#### detects closures with capture lists

- detects closures with capture lists
- Verify: detects closures with capture lists
   - Expected: is_closure_with_captures("Fn<(i64) -> i64>[x, y]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects closures with capture lists")
step("Verify: detects closures with capture lists")
expect(is_closure_with_captures("Fn<(i64) -> i64>[x, y]")).to_equal(true)
```

</details>

#### rejects plain function pointers

- rejects plain function pointers
- Verify: rejects plain function pointers
   - Expected: is_closure_with_captures("Fn<(i64) -> i64>") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects plain function pointers")
step("Verify: rejects plain function pointers")
expect(is_closure_with_captures("Fn<(i64) -> i64>")).to_equal(false)
```

</details>

#### rejects non-function types

- rejects non-function types
- Verify: rejects non-function types
   - Expected: is_closure_with_captures("i64") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-function types")
step("Verify: rejects non-function types")
expect(is_closure_with_captures("i64")).to_equal(false)
```

</details>

### callback_typedef_name

#### generates name for single-param callback

- generates name for single-param callback
- Verify: generates name for single-param callback
   - Expected: name equals `spl_callback_i64_to_i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates name for single-param callback")
step("Verify: generates name for single-param callback")
val name = callback_typedef_name(["i64"], "i64")
expect(name).to_equal("spl_callback_i64_to_i64")
```

</details>

#### generates name for multi-param callback

- generates name for multi-param callback
- Verify: generates name for multi-param callback
   - Expected: name equals `spl_callback_i64_f64_to_bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates name for multi-param callback")
step("Verify: generates name for multi-param callback")
val name = callback_typedef_name(["i64", "f64"], "bool")
expect(name).to_equal("spl_callback_i64_f64_to_bool")
```

</details>

#### generates name for void-param callback

- generates name for void-param callback
- Verify: generates name for void-param callback
   - Expected: name equals `spl_callback_void_to_void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates name for void-param callback")
step("Verify: generates name for void-param callback")
val name = callback_typedef_name([], "void")
expect(name).to_equal("spl_callback_void_to_void")
```

</details>

### extract_callback_params

#### extracts single parameter

- extracts single parameter
- Verify: extracts single parameter
   - Expected: params.len() equals `1`
   - Expected: params[0] equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts single parameter")
step("Verify: extracts single parameter")
val params = extract_callback_params("Fn<(i64) -> i64>")
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("i64")
```

</details>

#### extracts multiple parameters

- extracts multiple parameters
- Verify: extracts multiple parameters
   - Expected: params.len() equals `2`
   - Expected: params[0] equals `i64`
   - Expected: params[1] equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple parameters")
step("Verify: extracts multiple parameters")
val params = extract_callback_params("Fn<(i64, f64) -> bool>")
expect(params.len()).to_equal(2)
expect(params[0]).to_equal("i64")
expect(params[1]).to_equal("f64")
```

</details>

#### returns empty list for no-arg function

- returns empty list for no-arg function
- Verify: returns empty list for no-arg function
   - Expected: params.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list for no-arg function")
step("Verify: returns empty list for no-arg function")
val params = extract_callback_params("Fn<() -> void>")
expect(params.len()).to_equal(0)
```

</details>

### extract_callback_return

#### extracts return type

- extracts return type
- Verify: extracts return type
   - Expected: ret equals `bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts return type")
step("Verify: extracts return type")
val ret = extract_callback_return("Fn<(i64) -> bool>")
expect(ret).to_equal("bool")
```

</details>

#### extracts void return

- extracts void return
- Verify: extracts void return
   - Expected: ret equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts void return")
step("Verify: extracts void return")
val ret = extract_callback_return("Fn<() -> void>")
expect(ret).to_equal("void")
```

</details>

#### extracts i64 return

- extracts i64 return
- Verify: extracts i64 return
   - Expected: ret equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts i64 return")
step("Verify: extracts i64 return")
val ret = extract_callback_return("Fn<(i64, f64) -> i64>")
expect(ret).to_equal("i64")
```

</details>

### emit_callback_typedef

#### generates correct C typedef for single-param callback

- generates correct C typedef for single-param callback
- Verify: generates correct C typedef for single-param callback
   - Expected: result equals `typedef int64_t (*spl_callback_i64_to_i64)(int64_t);`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates correct C typedef for single-param callback")
step("Verify: generates correct C typedef for single-param callback")
val cb = CallbackTypedef(
    name: "spl_callback_i64_to_i64",
    return_type: "int64_t",
    param_types: ["int64_t"]
)
val result = emit_callback_typedef(cb)
expect(result).to_equal("typedef int64_t (*spl_callback_i64_to_i64)(int64_t);")
```

</details>

#### generates correct C typedef for multi-param callback

- generates correct C typedef for multi-param callback
- Verify: generates correct C typedef for multi-param callback
   - Expected: result equals `typedef int64_t (*spl_callback_i64_f64_to_bool)(int64_t, double);`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates correct C typedef for multi-param callback")
step("Verify: generates correct C typedef for multi-param callback")
val cb = CallbackTypedef(
    name: "spl_callback_i64_f64_to_bool",
    return_type: "int64_t",
    param_types: ["int64_t", "double"]
)
val result = emit_callback_typedef(cb)
expect(result).to_equal("typedef int64_t (*spl_callback_i64_f64_to_bool)(int64_t, double);")
```

</details>

#### generates void param list for no-arg callback

- generates void param list for no-arg callback
- Verify: generates void param list for no-arg callback
   - Expected: result equals `typedef void (*spl_callback_void_to_void)(void);`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates void param list for no-arg callback")
step("Verify: generates void param list for no-arg callback")
val cb = CallbackTypedef(
    name: "spl_callback_void_to_void",
    return_type: "void",
    param_types: []
)
val result = emit_callback_typedef(cb)
expect(result).to_equal("typedef void (*spl_callback_void_to_void)(void);")
```

</details>

### emit_callback_trampoline

#### generates null-check and invocation

- generates null-check and invocation
- Verify: generates null-check and invocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates null-check and invocation")
step("Verify: generates null-check and invocation")
val cb = CallbackTypedef(
    name: "spl_callback_i64_to_i64",
    return_type: "int64_t",
    param_types: ["int64_t"]
)
val result = emit_callback_trampoline("_spl_trampoline_test", cb)
expect(result).to_contain("if (!_cb)")
expect(result).to_contain("return _cb(_a0)")
```

</details>

#### generates void return for void callback

- generates void return for void callback
- Verify: generates void return for void callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates void return for void callback")
step("Verify: generates void return for void callback")
val cb = CallbackTypedef(
    name: "spl_callback_void_to_void",
    return_type: "void",
    param_types: []
)
val result = emit_callback_trampoline("_spl_trampoline_void", cb)
expect(result).to_contain("if (!_cb)")
expect(result).to_contain("_cb()")
```

</details>

### build_callback_typedef

#### builds typedef from Fn type string

- builds typedef from Fn type string
- Verify: builds typedef from Fn type string
   - Expected: cb.return_type equals `int64_t`
   - Expected: cb.param_types.len() equals `1`
   - Expected: cb.param_types[0] equals `int64_t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds typedef from Fn type string")
step("Verify: builds typedef from Fn type string")
val cb = build_callback_typedef("Fn<(i64) -> i64>")
expect(cb.name).to_contain("spl_callback")
expect(cb.return_type).to_equal("int64_t")
expect(cb.param_types.len()).to_equal(1)
expect(cb.param_types[0]).to_equal("int64_t")
```

</details>

#### builds typedef from multi-param Fn type

- builds typedef from multi-param Fn type
- Verify: builds typedef from multi-param Fn type
   - Expected: cb.return_type equals `int64_t`
   - Expected: cb.param_types.len() equals `2`
   - Expected: cb.param_types[0] equals `int64_t`
   - Expected: cb.param_types[1] equals `double`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds typedef from multi-param Fn type")
step("Verify: builds typedef from multi-param Fn type")
val cb = build_callback_typedef("Fn<(i64, f64) -> bool>")
expect(cb.return_type).to_equal("int64_t")
expect(cb.param_types.len()).to_equal(2)
expect(cb.param_types[0]).to_equal("int64_t")
expect(cb.param_types[1]).to_equal("double")
```

</details>

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
- `REQ-COMP-CALLBACK-TRAMPOLINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d408681cf1211fdfb042e4685235ec99b4eb40ef3803cb8c6fabe66cea2e7522`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d408681cf1211fdfb042e4685235ec99b4eb40ef3803cb8c6fabe66cea2e7522`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d408681cf1211fdfb042e4685235ec99b4eb40ef3803cb8c6fabe66cea2e7522`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/callback_trampoline_spec.spl
mirror: doc/06_spec/unit/compiler/backend/callback_trampoline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/callback_trampoline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/callback_trampoline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/callback_trampoline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/callback_trampoline_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts plain function pointer types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/callback_trampoline_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts multi-param function pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/callback_trampoline_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts no-arg function pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
