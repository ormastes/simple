# C Backend E2e Specification

> <details>

<!-- sdn-diagram:id=c_backend_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=c_backend_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

c_backend_e2e_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=c_backend_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = CIRBuilder create
2. builder emit file header


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = CIRBuilder create
2. builder start function
3. builder emit assign
4. builder emit return
5. builder end function


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = CIRBuilder create
2. builder start function
3. builder emit label
4. builder emit goto
5. builder emit label
6. builder emit return
7. builder end function


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = CIRBuilder create
   - Expected: name equals `_str_0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val kind = backend_for_name("c")
    expect(kind.?).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: finds C backend by name 'cpp'</summary>

#### finds C backend by name 'cpp' _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val kind = backend_for_name("cpp")
    expect(kind.?).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

<details>
<summary>Advanced: finds C backend by name 'ccodegen'</summary>

#### finds C backend by name 'ccodegen' _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val kind = backend_for_name("ccodegen")
    expect(kind.?).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### available backends

<details>
<summary>Advanced: includes CCodegen in available backends</summary>

#### includes CCodegen in available backends _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/02_integration/compiler/c_backend_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
