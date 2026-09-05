# LLVM Backend AArch64 Specification

> Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

<!-- sdn-diagram:id=llvm_backend_aarch64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_backend_aarch64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_backend_aarch64_spec -> compiler
llvm_backend_aarch64_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_backend_aarch64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend AArch64 Specification

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4002 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/llvm_backend_aarch64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## Scenarios

### LLVM Backend AArch64

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

#### generates correct aarch64 triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
expect(triple.arch).to_equal("aarch64")
expect(triple.to_text()).to_contain("aarch64")
```

</details>

#### datalayout

#### contains correct aarch64 layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
val dl = triple.datalayout()
expect(dl).to_contain("n32:64-S128")
```

</details>

#### emits datalayout in module header

1. var builder = LlvmIRBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
var builder = LlvmIRBuilder__create("test_aarch64", triple)
builder.emit_module_header()
val ir = builder.instructions.join("\n")
expect(ir).to_contain("target datalayout")
```

</details>

#### CPU defaults

#### defaults to cortex-a53

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
expect(config.cpu).to_equal("cortex-a53")
```

</details>

#### includes neon feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
expect(config.features).to_contain("+neon")
```

</details>

#### includes fp-armv8 feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
expect(config.features).to_contain("+fp-armv8")
```

</details>

#### native integer type

#### native_int_type is i64

1. var translator = MirToLlvm  create
   - Expected: translator.native_int() equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var translator = MirToLlvm__create("test", CodegenTarget.AArch64, nil)
expect(translator.native_int()).to_equal("i64")
```

</details>

#### type mapping

#### uses 64-bit target_bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.AArch64)
expect(mapper.target_bits).to_equal(64)
```

</details>

#### bare-metal entry

#### uses wfi instruction for halt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val halt = halt_instruction_for_target(CodegenTarget.AArch64)
expect(halt).to_equal("wfi")
```

</details>

#### builder size type

#### uses i64 size type

1. var builder = LlvmIRBuilder  create
   - Expected: builder.size_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
var builder = LlvmIRBuilder__create("test", triple)
expect(builder.size_type).to_equal("i64")
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
