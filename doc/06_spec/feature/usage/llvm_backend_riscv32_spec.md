# LLVM Backend RISC-V 32-bit Specification

> Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend RISC-V 32-bit Specification

Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4003 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_riscv32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

## Scenarios

### LLVM Backend RISC-V 32

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

#### target triple

#### generates correct riscv32 triple

- generates correct riscv32 triple
   - Expected: triple.arch equals `riscv32`
   - Expected: triple.to_text() equals `riscv32-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates correct riscv32 triple")
val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv32)
expect(triple.arch).to_equal("riscv32")
expect(triple.to_text()).to_equal("riscv32-unknown-linux-gnu")
```

</details>

#### datalayout

#### contains correct riscv32 layout

- contains correct riscv32 layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("contains correct riscv32 layout")
val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv32)
val dl = triple.datalayout()
expect(dl).to_contain("p:32:32")
```

</details>

#### CPU defaults

#### defaults to generic-rv32

- defaults to generic-rv32
   - Expected: config.cpu equals `generic-rv32`
   - Expected: config.abi.unwrap() equals `ilp32d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defaults to generic-rv32")
val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv32, nil)
expect(config.cpu).to_equal("generic-rv32")
expect(config.abi.unwrap()).to_equal("ilp32d")
```

</details>

#### includes standard extensions

- includes standard extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes standard extensions")
val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv32, nil)
expect(config.features).to_contain("+m")
expect(config.features).to_contain("+a")
expect(config.features).to_contain("+f")
expect(config.features).to_contain("+d")
expect(config.features).to_contain("+c")
```

</details>

#### matches the shared RV32 Linux target contract

- matches the shared RV32 Linux target contract
   - Expected: contract.triple() equals `riscv32-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `ilp32d`
   - Expected: contract.march equals `rv32gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches the shared RV32 Linux target contract")
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.triple()).to_equal("riscv32-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("ilp32d")
expect(contract.march).to_equal("rv32gc")
```

</details>

#### native integer type

#### native_int_type is i32

- native_int_type is i32
   - Expected: translator.native_int() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("native_int_type is i32")
var translator = MirToLlvm__create("test", CodegenTarget.Riscv32, nil)
expect(translator.native_int()).to_equal("i32")
```

</details>

#### type mapping

#### uses 32-bit target_bits

- uses 32-bit target_bits
   - Expected: mapper.target_bits equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses 32-bit target_bits")
val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.Riscv32)
expect(mapper.target_bits).to_equal(32)
```

</details>

#### bare-metal entry

#### uses wfi instruction for halt

- uses wfi instruction for halt
   - Expected: halt equals `wfi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses wfi instruction for halt")
val halt = halt_instruction_for_target(CodegenTarget.Riscv32)
expect(halt).to_equal("wfi")
```

</details>

#### builder size type

#### uses i32 size type

- uses i32 size type
   - Expected: builder.size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses i32 size type")
val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv32)
var builder = LlvmIRBuilder__create("test", triple)
expect(builder.size_type).to_equal("i32")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e76090787421d31b827eb0274e4741df5ab5a241de8995e59accfe97a25586e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e76090787421d31b827eb0274e4741df5ab5a241de8995e59accfe97a25586e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e76090787421d31b827eb0274e4741df5ab5a241de8995e59accfe97a25586e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/usage/llvm_backend_riscv32_spec.spl
mirror: doc/06_spec/feature/usage/llvm_backend_riscv32_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/llvm_backend_riscv32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/llvm_backend_riscv32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/llvm_backend_riscv32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/llvm_backend_riscv32_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: LLVM not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_riscv32_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates correct riscv32 triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/llvm_backend_riscv32_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains correct riscv32 layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
