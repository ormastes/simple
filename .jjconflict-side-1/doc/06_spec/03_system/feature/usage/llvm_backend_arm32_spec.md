# LLVM Backend ARM 32-bit Specification

> Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

<!-- sdn-diagram:id=llvm_backend_arm32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_backend_arm32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_backend_arm32_spec -> compiler
llvm_backend_arm32_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_backend_arm32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend ARM 32-bit Specification

Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4004 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/llvm_backend_arm32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

## Scenarios

### LLVM Backend ARM32

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

#### generates correct armv7 triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
expect(triple.arch).to_equal("armv7")
expect(triple.to_text()).to_contain("armv7")
```

</details>

#### includes gnueabihf env on linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
val text = triple.to_text()
expect(text).to_contain("armv7")
```

</details>

#### datalayout

#### contains correct arm32 layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
val dl = triple.datalayout()
expect(dl).to_contain("p:32:32")
```

</details>

#### CPU defaults

#### defaults to cortex-a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.Arm, nil)
expect(config.cpu).to_equal("cortex-a7")
```

</details>

#### includes neon feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.Arm, nil)
expect(config.features).to_contain("+neon")
```

</details>

#### includes vfp4 feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.Arm, nil)
expect(config.features).to_contain("+vfp4")
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
var translator = MirToLlvm__create("test", CodegenTarget.Arm, nil)
expect(translator.native_int()).to_equal("i32")
```

</details>

#### type mapping

#### uses 32-bit target_bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.Arm)
expect(mapper.target_bits).to_equal(32)
```

</details>

#### bare-metal entry

#### uses wfi instruction for halt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val halt = halt_instruction_for_target(CodegenTarget.Arm)
expect(halt).to_equal("wfi")
```

</details>

#### builder size type

#### uses i32 size type

1. var builder = LlvmIRBuilder  create
   - Expected: builder.size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
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
