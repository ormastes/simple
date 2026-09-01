# Header Generator Specification

> Tests C header (.h) and C++ wrapper (.hpp) generation for @export("C") classes. The C header provides opaque handles and function declarations. The C++ header wraps them in RAII classes with move semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Header Generator Specification

Tests C header (.h) and C++ wrapper (.hpp) generation for @export("C") classes. The C header provides opaque handles and function declarations. The C++ header wraps them in RAII classes with move semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-HEADER-001 |
| Category | Compiler / Tools / Header Generation |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | SFFI bidirectional class interop — C/C++ header generation |
| Plan | parsed-questing-goose.md |
| Design | sffi_external_library_pattern.md |
| Source | `test/unit/compiler/tools/header_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests C header (.h) and C++ wrapper (.hpp) generation for @export("C")
classes. The C header provides opaque handles and function declarations.
The C++ header wraps them in RAII classes with move semantics.

## Key Concepts

| Concept | Description |
|---------|-------------|
| emit_c_header | Generate complete .h file |
| emit_cpp_header | Generate complete .hpp file |
| Opaque handle | C typedef struct* pattern |
| RAII wrapper | C++ class with ctor/dtor delegation |

## Scenarios

### Header Generator

### C header

#### includes include guards

- includes include guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes include guards")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("#ifndef CALCULATOR_H")
expect(header).to_contain("#define CALCULATOR_H")
expect(header).to_contain("#endif")
```

</details>

#### includes standard headers

- includes standard headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes standard headers")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("#include <stdint.h>")
expect(header).to_contain("#include <stddef.h>")
expect(header).to_contain("#include <stdbool.h>")
```

</details>

#### includes extern C block

- includes extern C block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes extern C block")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("#ifdef __cplusplus")
expect(header).to_contain("extern")
```

</details>

#### emits opaque handle typedef

- emits opaque handle typedef


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opaque handle typedef")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("typedef struct spl_Calculator")
expect(header).to_contain("spl_Calculator_t")
```

</details>

#### emits create/destroy declarations

- emits create/destroy declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits create/destroy declarations")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("spl_Calculator_create")
expect(header).to_contain("spl_Calculator_destroy")
```

</details>

#### emits method declarations

- emits method declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits method declarations")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("spl_Calculator_add")
expect(header).to_contain("spl_Calculator_multiply")
```

</details>

#### emits library lifecycle functions

- emits library lifecycle functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits library lifecycle functions")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("spl_library_init")
expect(header).to_contain("spl_library_shutdown")
```

</details>

#### emits _Static_assert layout checks

- emits _Static_assert layout checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits _Static_assert layout checks")
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("_Static_assert")
expect(header).to_contain("sizeof")
```

</details>

#### emits C bitfield syntax for explicit @bits fields

- emits C bitfield syntax for explicit @bits fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits C bitfield syntax for explicit @bits fields")
val module = make_test_module()
val header = emit_c_header("gpio", [], [make_gpio_type_def()], module)
expect(header).to_contain("typedef struct spl_GpioRegister")
expect(header).to_contain("uint8_t mode : 4;")
expect(header).to_contain("uint8_t output : 1;")
expect(header).to_contain("uint8_t input : 1;")
expect(header).to_contain("uint8_t speed : 2;")
```

</details>

#### emits standalone function declarations

- emits standalone function declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits standalone function declarations")
val module = make_test_module()
val standalone = make_standalone_func()
val header = emit_c_header("mylib", [standalone], [], module)
expect(header).to_contain("spl_add_numbers")
```

</details>

#### converts guard name to uppercase

- converts guard name to uppercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts guard name to uppercase")
val module = make_test_module()
val header = emit_c_header("my-lib.v2", [], [], module)
expect(header).to_contain("#ifndef MY_LIB_V2_H")
```

</details>

### C++ header

#### emits pragma once

- emits pragma once


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits pragma once")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("#pragma once")
```

</details>

#### includes C header

- includes C header


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes C header")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("#include \"mylib.h\"")
```

</details>

#### emits namespace spl

- emits namespace spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits namespace spl")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("namespace spl")
expect(header).to_contain("} // namespace spl")
```

</details>

#### emits RAII wrapper class

- emits RAII wrapper class


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits RAII wrapper class")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("class Calculator")
expect(header).to_contain("handle_")
```

</details>

#### emits constructor

- emits constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits constructor")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("explicit Calculator")
expect(header).to_contain("spl_Calculator_create")
```

</details>

#### emits destructor

- emits destructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits destructor")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("~Calculator")
expect(header).to_contain("spl_Calculator_destroy")
```

</details>

#### emits move constructor

- emits move constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits move constructor")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("Calculator&&")
expect(header).to_contain("noexcept")
expect(header).to_contain("nullptr")
```

</details>

#### emits deleted copy

- emits deleted copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits deleted copy")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("= delete")
```

</details>

#### emits method wrappers

- emits method wrappers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits method wrappers")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("add(")
expect(header).to_contain("multiply(")
```

</details>

#### emits Library RAII guard

- emits Library RAII guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Library RAII guard")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("class Library")
expect(header).to_contain("spl_library_init")
expect(header).to_contain("spl_library_shutdown")
```

</details>

#### emits C++ static_assert layout checks

- emits C++ static_assert layout checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits C++ static_assert layout checks")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("static_assert")
expect(header).to_contain("alignof")
```

</details>

#### includes standard C++ headers

- includes standard C++ headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes standard C++ headers")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("#include <memory>")
expect(header).to_contain("#include <string>")
expect(header).to_contain("#include <utility>")
```

</details>

#### emits move assignment operator

- emits move assignment operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits move assignment operator")
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("operator=")
expect(header).to_contain("Calculator&&")
```

</details>

### shared MIR function-param helpers

#### mir_function_params returns the signature's param list in order

- mir_function_params returns the signature's param list in order
   - Expected: params.len() equals `3`
   - Expected: params[0].kind equals `MirTypeKind.I64`
   - Expected: params[1].kind equals `MirTypeKind.F64`
   - Expected: params[2].kind equals `MirTypeKind.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mir_function_params returns the signature's param list in order")
val func = make_calc_add_func()
val params = mir_function_params(func)
expect(params.len()).to_equal(3)
expect(params[0].kind).to_equal(MirTypeKind.I64)
expect(params[1].kind).to_equal(MirTypeKind.F64)
expect(params[2].kind).to_equal(MirTypeKind.F64)
```

</details>

#### mir_function_param_count matches the number of declared params

- mir_function_param_count matches the number of declared params
   - Expected: mir_function_param_count(func) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mir_function_param_count matches the number of declared params")
val func = make_standalone_func()
expect(mir_function_param_count(func)).to_equal(2)
```

</details>

#### mir_function_param indexes into the params list like params[idx]

- mir_function_param indexes into the params list like params[idx]
   - Expected: mir_function_param(func, 0).kind equals `MirTypeKind.I32`
   - Expected: mir_function_param(func, 1).kind equals `MirTypeKind.I32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mir_function_param indexes into the params list like params[idx]")
val func = make_standalone_func()
expect(mir_function_param(func, 0).kind).to_equal(MirTypeKind.I32)
expect(mir_function_param(func, 1).kind).to_equal(MirTypeKind.I32)
```

</details>

### entry-point ordering

#### sorts exported functions and types without array method dispatch

- sorts exported functions and types without array method dispatch
   - Expected: funcs[0].name equals `__simple_Calculator_add`
   - Expected: funcs[1].name equals `__simple_Calculator_multiply`
   - Expected: types[0].name equals `Calculator`
   - Expected: types[1].name equals `GpioRegister`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts exported functions and types without array method dispatch")
val funcs = sort_exported_functions([make_calc_multiply_func(), make_calc_add_func()])
expect(funcs[0].name).to_equal("__simple_Calculator_add")
expect(funcs[1].name).to_equal("__simple_Calculator_multiply")

val types = sort_exported_types([make_gpio_type_def(), make_calc_type_def()])
expect(types[0].name).to_equal("Calculator")
expect(types[1].name).to_equal("GpioRegister")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `SFFI bidirectional class interop — C/C++ header generation`
- **Plan:** `parsed-questing-goose.md`
- **Design:** `sffi_external_library_pattern.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f09f1cb56f60386c7b0756495742c7100a51e4bbe94a0375b3a4fd1511f1d96f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f09f1cb56f60386c7b0756495742c7100a51e4bbe94a0375b3a4fd1511f1d96f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f09f1cb56f60386c7b0756495742c7100a51e4bbe94a0375b3a4fd1511f1d96f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/tools/header_gen_spec.spl
mirror: doc/06_spec/unit/compiler/tools/header_gen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/tools/header_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/tools/header_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/tools/header_gen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/tools/header_gen_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes include guards' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/tools/header_gen_spec.spl:217:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes standard headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/tools/header_gen_spec.spl:226:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes extern C block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
