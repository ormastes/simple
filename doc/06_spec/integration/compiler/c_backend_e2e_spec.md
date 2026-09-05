# C Backend E2e Specification

> Tests covering C Backend - Type Mapper, C Backend - IR Builder, C Backend - Registration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Backend E2e Specification

## Scenarios

### C Backend - Type Mapper

#### primitive types

<details>
<summary>Advanced: maps i64</summary>

#### maps i64 _(slow)_

- maps i64
   - Expected: result equals `int64_t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps i64")
if _can_run:
    val mapper = CTypeMapper.create()
    val result = mapper.map_primitive(PrimitiveType.I64)
    expect(result).to_equal("int64_t")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: maps f64</summary>

#### maps f64 _(slow)_

- maps f64
   - Expected: result equals `double`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps f64")
if _can_run:
    val mapper = CTypeMapper.create()
    val result = mapper.map_primitive(PrimitiveType.F64)
    expect(result).to_equal("double")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: maps bool as int64_t</summary>

#### maps bool as int64_t _(slow)_

- maps bool as int64_t
   - Expected: result equals `int64_t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps bool as int64_t")
if _can_run:
    val mapper = CTypeMapper.create()
    val result = mapper.map_primitive(PrimitiveType.Bool)
    expect(result).to_equal("int64_t")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: maps unit as void</summary>

#### maps unit as void _(slow)_

- maps unit as void
   - Expected: result equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps unit as void")
if _can_run:
    val mapper = CTypeMapper.create()
    val result = mapper.map_primitive(PrimitiveType.Unit)
    expect(result).to_equal("void")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### pointer types

<details>
<summary>Advanced: maps pointers to void*</summary>

#### maps pointers to void* _(slow)_

- maps pointers to void*
   - Expected: result equals `void*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps pointers to void*")
if _can_run:
    val mapper = CTypeMapper.create()
    val result = mapper.map_pointer("int64_t", Mutability.Mutable)
    expect(result).to_equal("void*")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### backend name

<details>
<summary>Advanced: returns C</summary>

#### returns C _(slow)_

- returns C
   - Expected: mapper.backend_name() equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns C")
if _can_run:
    val mapper = CTypeMapper.create()
    expect(mapper.backend_name()).to_equal("C")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

### C Backend - IR Builder

#### file header

<details>
<summary>Advanced: emits includes and runtime header</summary>

#### emits includes and runtime header _(slow)_

- emits includes and runtime header


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits includes and runtime header")
if _can_run:
    var builder = CIRBuilder.create("test_module")
    builder.emit_file_header()
    val output = builder.build()
    expect(output).to_contain("#include <cstdint>")
    expect(output).to_contain("#include \"runtime.h\"")
    expect(output).to_contain("test_module")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### function generation

<details>
<summary>Advanced: emits function definition</summary>

#### emits function definition _(slow)_

- emits function definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits function definition")
if _can_run:
    var builder = CIRBuilder.create("test")
    builder.start_function("int64_t", "my_func", "int64_t _l0")
    builder.emit_assign("_l1", "_l0 + 1")
    builder.emit_return(Some("_l1"))
    builder.end_function()
    val output = builder.build()
    expect(output).to_contain("int64_t my_func(int64_t _l0)")
    expect(output).to_contain("_l1 = _l0 + 1")
    expect(output).to_contain("return _l1")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### control flow

<details>
<summary>Advanced: emits labels and gotos</summary>

#### emits labels and gotos _(slow)_

- emits labels and gotos


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits labels and gotos")
if _can_run:
    var builder = CIRBuilder.create("test")
    builder.start_function("void", "test_fn", "void")
    builder.emit_label("bb0")
    builder.emit_goto("bb1")
    builder.emit_label("bb1")
    builder.emit_return(nil)
    builder.end_function()
    val output = builder.build()
    expect(output).to_contain("bb0:")
    expect(output).to_contain("goto bb1")
    expect(output).to_contain("bb1:")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### string literals

<details>
<summary>Advanced: adds string constants</summary>

#### adds string constants _(slow)_

- adds string constants
   - Expected: name equals `_str_0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds string constants")
if _can_run:
    var builder = CIRBuilder.create("test")
    val name = builder.add_string_literal("hello")
    expect(name).to_equal("_str_0")
    val output = builder.build()
    expect(output).to_contain("static const char _str_0[]")
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

### C Backend - Registration

#### backend lookup

<details>
<summary>Advanced: finds C backend by name 'c'</summary>

#### finds C backend by name 'c' _(slow)_

- finds C backend by name 'c'
   - Expected: kind == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("finds C backend by name 'c'")
if _can_run:
    val kind = backend_for_name("c")
    expect(kind == nil).to_equal(false)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: finds C backend by name 'cpp'</summary>

#### finds C backend by name 'cpp' _(slow)_

- finds C backend by name 'cpp'
   - Expected: kind == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("finds C backend by name 'cpp'")
if _can_run:
    val kind = backend_for_name("cpp")
    expect(kind == nil).to_equal(false)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: finds C backend by name 'ccodegen'</summary>

#### finds C backend by name 'ccodegen' _(slow)_

- finds C backend by name 'ccodegen'
   - Expected: kind == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("finds C backend by name 'ccodegen'")
if _can_run:
    val kind = backend_for_name("ccodegen")
    expect(kind == nil).to_equal(false)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### available backends

<details>
<summary>Advanced: includes CCodegen in available backends</summary>

#### includes CCodegen in available backends _(slow)_

- includes CCodegen in available backends
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes CCodegen in available backends")
if _can_run:
    val backends = available_backends()
    var found = false
    for b in backends:
        if b == BackendKind.CCodegen:
            found = true
    expect(found).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### backend kind

<details>
<summary>Advanced: has correct integer tag</summary>

#### has correct integer tag _(slow)_

- has correct integer tag
   - Expected: BACKEND_CCODEGEN equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has correct integer tag")
if _can_run:
    expect(BACKEND_CCODEGEN).to_equal(9)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/c_backend_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C Backend - Type Mapper, C Backend - IR Builder, C Backend - Registration.
- C Backend - Type Mapper
- C Backend - IR Builder
- C Backend - Registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 15 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c4405181a7707764e06d8d94308cc86a112b1442ffa346c88c4ebfe8fb7ef84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c4405181a7707764e06d8d94308cc86a112b1442ffa346c88c4ebfe8fb7ef84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c4405181a7707764e06d8d94308cc86a112b1442ffa346c88c4ebfe8fb7ef84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/compiler/c_backend_e2e_spec.spl
mirror: doc/06_spec/integration/compiler/c_backend_e2e_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/c_backend_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/c_backend_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/c_backend_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/compiler/c_backend_e2e_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/c_backend_e2e_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps f64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/c_backend_e2e_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps bool as int64_t' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
