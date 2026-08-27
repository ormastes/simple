# LLVM Backend Codegen Specification

> The LLVM backend:

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
| Source | `test/feature/usage/llvm_backend_spec.spl` |
| Updated | 2026-08-26 |
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

- env_skip: LLVM not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env_skip: LLVM not available")
val reason = test_env_gate_skip("SIMPLE_LLVM_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### basic arithmetic operations

#### generates code for integer addition

- generates code for integer addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for integer addition")
fn add(a: i32, b: i32) -> i32:
    a + b
expect add(5, 3) == 8
```

</details>

#### generates code for integer multiplication

- generates code for integer multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for integer multiplication")
fn multiply(a: i32, b: i32) -> i32:
    a * b
expect multiply(5, 3) == 15
```

</details>

#### generates code for floating-point operations

- generates code for floating-point operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for floating-point operations")
fn divide(a: f64, b: f64) -> f64:
    a / b
val result = divide(10.0, 2.0)
expect((result - 5.0).abs()).to_be_less_than(0.001)
```

</details>

#### control flow generation

#### generates code for if-else branches

- generates code for if-else branches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for if-else branches")
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

- generates code for loops


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for loops")
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

- handles function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles function calls")
fn outer(x: i32) -> i32:
    fn inner(y: i32) -> i32:
        y * 2
    inner(x) + 5
expect outer(3) == 11
```

</details>

#### handles recursive function calls

- handles recursive function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles recursive function calls")
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

- generates code for variable assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for variable assignment")
fn variable_ops():
    var x = 5
    x = x + 3
    x
expect variable_ops() == 8
```

</details>

#### handles mutable struct fields

- handles mutable struct fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles mutable struct fields")
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

- generates code for list operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for list operations")
fn list_ops():
    val items = [1, 2, 3, 4, 5]
    items.length
expect list_ops() == 5
```

</details>

#### generates code for map operations

- generates code for map operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for map operations")
fn map_ops():
    val items = {"a": 1, "b": 2}
    items["a"]
expect map_ops() == 1
```

</details>

#### type operations

#### generates code for type conversions

- generates code for type conversions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates code for type conversions")
fn convert():
    val i = 42
    val f = i.to_f64()
    f
val result = convert()
expect((result - 42.0).abs()).to_be_less_than(0.001)
```

</details>

#### optimization preservation

#### preserves correct semantics under optimization

- preserves correct semantics under optimization


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves correct semantics under optimization")
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

- maintains correct results with loop optimization


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maintains correct results with loop optimization")
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

- generates passes for optimization levels
   - Expected: debug_passes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates passes for optimization levels")
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

- emits debug info header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits debug info header")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_debug_info_header("test.spl", "/home/user")
val ir = builder.build()
expect(ir).to_contain("DICompileUnit")
expect(ir).to_contain("test.spl")
```

</details>

#### ABI

#### emits typed function calls

- emits typed function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits typed function calls")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
builder.start_function("main", [], "i64")
builder.emit("  %0 = call i64 @add(i32 1, i64 2)")
builder.end_function()
val ir = builder.build()
expect(ir).to_contain("call i64 @add")
```

</details>

#### target datalayout

#### emits datalayout for x86_64

- emits datalayout for x86_64


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits datalayout for x86_64")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.build()
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("n8:16:32:64-S128")
```

</details>

#### emits datalayout for i686

- emits datalayout for i686


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits datalayout for i686")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.build()
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("p:32:32")
```

</details>

#### emits datalayout for aarch64

- emits datalayout for aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits datalayout for aarch64")
val target = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.build()
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("n32:64-S128")
```

</details>

#### emits datalayout before target triple

- emits datalayout before target triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("emits datalayout before target triple")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
builder.emit_module_header()
val ir = builder.build()
val dl_pos = ir.find("target datalayout")
val tt_pos = ir.find("target triple")
expect(dl_pos).to_be_less_than(tt_pos)
```

</details>

#### 32-bit type handling

#### native_int_type is i32 for 32-bit targets

- native_int_type is i32 for 32-bit targets
   - Expected: translator.native_int() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("native_int_type is i32 for 32-bit targets")
var translator = MirToLlvm__create("test", CodegenTarget.X86, nil)
expect(translator.native_int()).to_equal("i32")
```

</details>

#### native_int_type is i64 for 64-bit targets

- native_int_type is i64 for 64-bit targets
   - Expected: translator.native_int() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("native_int_type is i64 for 64-bit targets")
var translator = MirToLlvm__create("test", CodegenTarget.X86_64, nil)
expect(translator.native_int()).to_equal("i64")
```

</details>

#### type mapper uses 32-bit pointers for i686

- type mapper uses 32-bit pointers for i686
   - Expected: mapper.target_bits equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("type mapper uses 32-bit pointers for i686")
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86)
expect(mapper.target_bits).to_equal(32)
```

</details>

#### type mapper uses 64-bit pointers for x86_64

- type mapper uses 64-bit pointers for x86_64
   - Expected: mapper.target_bits equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("type mapper uses 64-bit pointers for x86_64")
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86_64)
expect(mapper.target_bits).to_equal(64)
```

</details>

#### builder size_type is i32 for 32-bit targets

- builder size_type is i32 for 32-bit targets
   - Expected: builder.size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builder size_type is i32 for 32-bit targets")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test", target)
expect(builder.size_type).to_equal("i32")
```

</details>

#### builder size_type is i64 for 64-bit targets

- builder size_type is i64 for 64-bit targets
   - Expected: builder.size_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builder size_type is i64 for 64-bit targets")
val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
var builder = LlvmIRBuilder__create("test", target)
expect(builder.size_type).to_equal("i64")
```

</details>

#### compatibility build

#### selects correct CPU for x86_64

- selects correct CPU for x86_64
   - Expected: config.cpu equals `x86-64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects correct CPU for x86_64")
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86_64)
expect(config.cpu).to_equal("x86-64")
```

</details>

#### selects correct CPU for i686

- selects correct CPU for i686
   - Expected: config.cpu equals `i686`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects correct CPU for i686")
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86)
expect(config.cpu).to_equal("i686")
```

</details>

#### selects correct CPU for aarch64

- selects correct CPU for aarch64
   - Expected: config.cpu equals `generic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects correct CPU for aarch64")
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.AArch64)
expect(config.cpu).to_equal("generic")
```

</details>

#### selects correct CPU for riscv64

- selects correct CPU for riscv64
   - Expected: config.cpu equals `generic-rv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects correct CPU for riscv64")
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.Riscv64)
expect(config.cpu).to_equal("generic-rv64")
```

</details>

#### selects correct CPU for riscv32

- selects correct CPU for riscv32
   - Expected: config.cpu equals `generic-rv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects correct CPU for riscv32")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a36dd5cb9ef49af9c66a7c36c09249395a8ad464406459acc3e853a88799f3df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a36dd5cb9ef49af9c66a7c36c09249395a8ad464406459acc3e853a88799f3df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a36dd5cb9ef49af9c66a7c36c09249395a8ad464406459acc3e853a88799f3df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/llvm_backend_spec.spl
mirror: doc/06_spec/feature/usage/llvm_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/llvm_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/llvm_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/llvm_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/llvm_backend_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: LLVM not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates code for integer addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates code for integer multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
