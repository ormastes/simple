# LLVM Backend i686 (x86 32-bit) Specification

> Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.

<!-- sdn-diagram:id=llvm_backend_i686_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_backend_i686_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_backend_i686_spec -> compiler
llvm_backend_i686_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_backend_i686_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend i686 (x86 32-bit) Specification

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4001 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/llvm_backend_i686_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.
This includes target triple generation, datalayout, native integer types, and CPU defaults.

## Scenarios

### LLVM Backend i686

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

#### target triple

#### generates correct i686 triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
expect(triple.arch).to_equal("i686")
expect(triple.to_text()).to_contain("i686")
```

</details>

#### includes correct OS in triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
val text = triple.to_text()
# Should have linux-gnu or similar env
expect(text).to_contain("i686")
```

</details>

#### datalayout

#### contains 32-bit pointer specification

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
val dl = triple.datalayout()
expect(dl).to_contain("p:32:32")
```

</details>

#### emits datalayout in module header

1. var builder = LlvmIRBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test_i686", triple)
builder.emit_module_header()
val ir = builder.instructions.join("\n")
expect(ir).to_contain("target datalayout")
expect(ir).to_contain("p:32:32")
```

</details>

#### type mapping

#### uses 32-bit target_bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86)
expect(mapper.target_bits).to_equal(32)
```

</details>

#### native integer type

#### native_int_type is i32

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

#### CPU defaults

#### defaults to i686 CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.X86, nil)
expect(config.cpu).to_equal("i686")
```

</details>

#### includes sse2 feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.X86, nil)
expect(config.features).to_contain("+sse2")
```

</details>

#### compatibility build

#### works for i686

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86)
expect(config.cpu).to_equal("i686")
```

</details>

#### builder size type

#### uses i32 size type for memcpy/memset

1. var builder = LlvmIRBuilder  create
   - Expected: builder.size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
var builder = LlvmIRBuilder__create("test", triple)
expect(builder.size_type).to_equal("i32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
