# LLVM Backend RISC-V 64-bit Specification

> Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

<!-- sdn-diagram:id=llvm_backend_riscv64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_backend_riscv64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_backend_riscv64_spec -> compiler
llvm_backend_riscv64_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_backend_riscv64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend RISC-V 64-bit Specification

Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4005 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/llvm_backend_riscv64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

## Scenarios

### LLVM Backend RISC-V 64

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

#### generates correct riscv64 triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
expect(triple.arch).to_equal("riscv64")
expect(triple.to_text()).to_equal("riscv64-unknown-linux-gnu")
```

</details>

#### datalayout

#### contains correct riscv64 layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
val dl = triple.datalayout()
expect(dl).to_contain("p:64:64")
```

</details>

#### CPU defaults

#### defaults to generic-rv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv64, nil)
expect(config.cpu).to_equal("generic-rv64")
expect(config.abi.unwrap()).to_equal("lp64d")
```

</details>

#### includes standard extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv64, nil)
expect(config.features).to_contain("+m")
expect(config.features).to_contain("+a")
expect(config.features).to_contain("+f")
expect(config.features).to_contain("+d")
expect(config.features).to_contain("+c")
```

</details>

#### matches the shared RV64 Linux target contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("lp64d")
expect(contract.march).to_equal("rv64gc")
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
var translator = MirToLlvm__create("test", CodegenTarget.Riscv64, nil)
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
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.Riscv64)
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
val halt = halt_instruction_for_target(CodegenTarget.Riscv64)
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
val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
var builder = LlvmIRBuilder__create("test", triple)
expect(builder.size_type).to_equal("i64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
