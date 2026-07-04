# LLVM Backend Codegen Specification

> The LLVM backend:

<!-- sdn-diagram:id=llvm_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_backend_spec -> compiler
llvm_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend Codegen Specification

The LLVM backend:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4000 |
| Category | Infrastructure |
| Difficulty | 5/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/llvm_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Concepts

| Concept | Description |
|---------|-------------|
| LLVM IR | Intermediate representation compatible with LLVM compiler framework |
| MIR to LLVM | Conversion pipeline from Simple's MIR to LLVM IR |
| Optimization Passes | LLVM-level optimizations (inlining, dead code elimination, etc) |
| Code Generation | Conversion of LLVM IR to native machine code |
| Target Platform | Architecture and OS-specific code generation (x86_64, ARM, etc) |
| Linking | Integration with system linker and native libraries |

## Behavior

The LLVM backend:
- Translates MIR instructions to equivalent LLVM IR constructs
- Preserves type information and memory semantics
- Enables high-level optimizations through LLVM optimization passes
- Generates platform-specific machine code
- Integrates with native linkers for final executable generation
- Supports multiple target architectures and operating systems

## Implementation Notes

- LLVM IR generation uses the `inkwell` Rust bindings
- Optimization level controlled via compiler flags
- Target triple determines platform-specific behavior
- Function attributes affect code generation and optimization
- Debug information preserved for debugging support

## Related Specifications

- Intermediate Representation (MIR format specification)
- Memory Model (reference capabilities and ownership rules)
- FFI Integration (native function calling conventions)
- Type System (type information preservation in codegen)

## Scenarios

### LLVM Backend Codegen

#### env_skip: LLVM not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_LLVM_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### basic arithmetic operations

#### generates code for integer addition

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i32, b: i32) -> i32:
    a + b
expect add(5, 3) == 8
```

</details>

#### generates code for integer multiplication

1. fn multiply
2. expect multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(a: i32, b: i32) -> i32:
    a * b
expect multiply(5, 3) == 15
```

</details>

#### generates code for floating-point operations

1. fn divide
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn divide(a: f64, b: f64) -> f64:
    a / b
val result = divide(10.0, 2.0)
expect (result - 5.0).abs() < 0.001
```

</details>

#### control flow generation

#### generates code for if-else branches

1. fn classify
2. expect classify
3. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i32) -> text:
    if x > 0:
        "positive"
    else:
        "non-positive"
expect classify(5) == "positive"
expect classify(-3) == "non-positive"
```

</details>

<details>
<summary>Advanced: generates code for loops</summary>

#### generates code for loops

1. fn count up
2. expect count up


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn count_up(n: i32) -> i32:
    var sum = 0
    var i = 0
    while i < n:
        sum = sum + i
        i = i + 1
    sum
expect count_up(5) == 10
```

</details>


</details>

#### function calls and stack management

#### handles function calls

1. fn outer
2. fn inner
3. inner
4. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer(x: i32) -> i32:
    fn inner(y: i32) -> i32:
        y * 2
    inner(x) + 5
expect outer(3) == 11
```

</details>

#### handles recursive function calls

1. fn fibonacci
2. fibonacci
3. expect fibonacci


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn fibonacci(n: i32) -> i32:
    if n <= 1:
        n
    else:
        fibonacci(n - 1) + fibonacci(n - 2)
expect fibonacci(6) == 8
```

</details>

#### memory operations

#### generates code for variable assignment

1. fn variable ops
2. expect variable ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn variable_ops():
    var x = 5
    x = x + 3
    x
expect variable_ops() == 8
```

</details>

#### handles mutable struct fields

1. fn move point
2. var p = Point
3.


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i32
    y: i32
fn move_point():
    var p = Point(x: 0, y: 0)
    p.x = 10
    p.y = 20
    (p.x, p.y)
val (x, y) = move_point()
expect x == 10
expect y == 20
```

</details>

#### collection operations

#### generates code for list operations

1. fn list ops
2. expect list ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn list_ops():
    val items = [1, 2, 3, 4, 5]
    items.length
expect list_ops() == 5
```

</details>

#### generates code for map operations

1. fn map ops
2. expect map ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn map_ops():
    val items = {"a": 1, "b": 2}
    items["a"]
expect map_ops() == 1
```

</details>

#### type operations

#### generates code for type conversions

1. fn convert
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn convert():
    val i = 42
    val f = i.to_f64()
    f
val result = convert()
expect (result - 42.0).abs() < 0.001
```

</details>

#### optimization preservation

#### preserves correct semantics under optimization

1. fn optimizable
2. expect optimizable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn optimizable(n: i32) -> i32:
    val x = 5
    val y = 3
    x + y + n
expect optimizable(2) == 10
```

</details>

<details>
<summary>Advanced: maintains correct results with loop optimization</summary>

#### maintains correct results with loop optimization

1. fn loop opt
2. expect loop opt


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn loop_opt(n: i32) -> i32:
    var result = 1
    var i = 1
    while i <= n:
        result = result * i
        i = i + 1
    result
expect loop_opt(5) == 120
```

</details>


</details>

#### optimization

#### generates passes for optimization levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_passes = passes_for_level(OptimizationLevel.Debug)
expect(debug_passes.len()).to_equal(2)
val speed_passes = passes_for_level(OptimizationLevel.Speed)
expect(speed_passes.len()).to_be_greater_than(4)
val aggressive_passes = passes_for_level(OptimizationLevel.Aggressive)
expect(aggressive_passes.len()).to_be_greater_than(8)
```

</details>

#### debug info

#### emits debug info header

1. var builder = LlvmIRBuilder  create
2. builder emit debug info header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_debug_info_header("test.spl", "/home/user")
val ir = builder.instructions.join("\n")
expect(ir).to_contain("DICompileUnit")
expect(ir).to_contain("test.spl")
```

</details>

#### ABI

#### emits typed function calls

1. var builder = LlvmIRBuilder  create
2. builder emit module header
3. builder start function
4. builder emit
5. builder end function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
builder.start_function("main", [], "i64")
builder.emit("  %0 = call i64 @add(i32 1, i64 2)")
builder.end_function()
val ir = builder.instructions.join("\n")
expect(ir).to_contain("call i64 @add")
```

</details>

#### target datalayout

#### emits datalayout for x86_64

1. var builder = LlvmIRBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.instructions.join("\n")
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("n8:16:32:64-S128")
```

</details>

#### emits datalayout for i686

1. var builder = LlvmIRBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.instructions.join("\n")
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("p:32:32")
```

</details>

#### emits datalayout for aarch64

1. var builder = LlvmIRBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.instructions.join("\n")
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("n32:64-S128")
```

</details>

#### emits datalayout before target triple

1. var builder = LlvmIRBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.instructions.join("\n")
val dl_pos = ir.find("target datalayout")
val tt_pos = ir.find("target triple")
expect(dl_pos).to_be_less_than(tt_pos)
```

</details>

#### 32-bit type handling

#### native_int_type is i32 for 32-bit targets

1. var translator = MirToLlvm  create
   - Expected: translator.native_int() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var translator = MirToLlvm__create("test", CodegenTarget.X86, nil)
expect(translator.native_int()).to_equal("i32")
```

</details>

#### native_int_type is i64 for 64-bit targets

1. var translator = MirToLlvm  create
   - Expected: translator.native_int() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var translator = MirToLlvm__create("test", CodegenTarget.X86_64, nil)
expect(translator.native_int()).to_equal("i64")
```

</details>

#### type mapper uses 32-bit pointers for i686

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86)
expect(mapper.target_bits).to_equal(32)
```

</details>

#### type mapper uses 64-bit pointers for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86_64)
expect(mapper.target_bits).to_equal(64)
```

</details>

#### builder size_type is i32 for 32-bit targets

1. var builder = LlvmIRBuilder  create
   - Expected: builder.size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test", target)
expect(builder.size_type).to_equal("i32")
```

</details>

#### builder size_type is i64 for 64-bit targets

1. var builder = LlvmIRBuilder  create
   - Expected: builder.size_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
expect(builder.size_type).to_equal("i64")
```

</details>

#### compatibility build

#### selects correct CPU for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86_64)
expect(config.cpu).to_equal("x86-64")
```

</details>

#### selects correct CPU for i686

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86)
expect(config.cpu).to_equal("i686")
```

</details>

#### selects correct CPU for aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.AArch64)
expect(config.cpu).to_equal("generic")
```

</details>

#### selects correct CPU for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.Riscv64)
expect(config.cpu).to_equal("generic-rv64")
```

</details>

#### selects correct CPU for riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.Riscv32)
expect(config.cpu).to_equal("generic-rv32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
