# Header Generator Specification

> Tests C header (.h) and C++ wrapper (.hpp) generation for @export("C") classes. The C header provides opaque handles and function declarations. The C++ header wraps them in RAII classes with move semantics.

<!-- sdn-diagram:id=header_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=header_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

header_gen_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=header_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

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
| Source | `test/01_unit/compiler/tools/header_gen_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("#ifndef CALCULATOR_H")
expect(header).to_contain("#define CALCULATOR_H")
expect(header).to_contain("#endif")
```

</details>

#### includes standard headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("#include <stdint.h>")
expect(header).to_contain("#include <stddef.h>")
expect(header).to_contain("#include <stdbool.h>")
```

</details>

#### includes extern C block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("#ifdef __cplusplus")
expect(header).to_contain("extern")
```

</details>

#### emits opaque handle typedef

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("typedef struct spl_Calculator")
expect(header).to_contain("spl_Calculator_t")
```

</details>

#### emits create/destroy declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("spl_Calculator_create")
expect(header).to_contain("spl_Calculator_destroy")
```

</details>

#### emits method declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("spl_Calculator_add")
expect(header).to_contain("spl_Calculator_multiply")
```

</details>

#### emits library lifecycle functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("spl_library_init")
expect(header).to_contain("spl_library_shutdown")
```

</details>

#### emits _Static_assert layout checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("calculator", [], [make_calc_type_def()], module)
expect(header).to_contain("_Static_assert")
expect(header).to_contain("sizeof")
```

</details>

#### emits C bitfield syntax for explicit @bits fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val standalone = make_standalone_func()
val header = emit_c_header("mylib", [standalone], [], module)
expect(header).to_contain("spl_add_numbers")
```

</details>

#### converts guard name to uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_c_header("my-lib.v2", [], [], module)
expect(header).to_contain("#ifndef MY_LIB_V2_H")
```

</details>

### C++ header

#### emits pragma once

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("#pragma once")
```

</details>

#### includes C header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("#include \"mylib.h\"")
```

</details>

#### emits namespace spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("namespace spl")
expect(header).to_contain("} // namespace spl")
```

</details>

#### emits RAII wrapper class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("class Calculator")
expect(header).to_contain("handle_")
```

</details>

#### emits constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("explicit Calculator")
expect(header).to_contain("spl_Calculator_create")
```

</details>

#### emits destructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("~Calculator")
expect(header).to_contain("spl_Calculator_destroy")
```

</details>

#### emits move constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("Calculator&&")
expect(header).to_contain("noexcept")
expect(header).to_contain("nullptr")
```

</details>

#### emits deleted copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("= delete")
```

</details>

#### emits method wrappers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("add(")
expect(header).to_contain("multiply(")
```

</details>

#### emits Library RAII guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("class Library")
expect(header).to_contain("spl_library_init")
expect(header).to_contain("spl_library_shutdown")
```

</details>

#### emits C++ static_assert layout checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("static_assert")
expect(header).to_contain("alignof")
```

</details>

#### includes standard C++ headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("#include <memory>")
expect(header).to_contain("#include <string>")
expect(header).to_contain("#include <utility>")
```

</details>

#### emits move assignment operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_test_module()
val header = emit_cpp_header("mylib", [make_calc_type_def()], [], "mylib.h", module)
expect(header).to_contain("operator=")
expect(header).to_contain("Calculator&&")
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


## Related Documentation

- **Requirements:** [SFFI bidirectional class interop — C/C++ header generation](SFFI bidirectional class interop — C/C++ header generation)
- **Plan:** [parsed-questing-goose.md](parsed-questing-goose.md)
- **Design:** [sffi_external_library_pattern.md](sffi_external_library_pattern.md)


</details>
