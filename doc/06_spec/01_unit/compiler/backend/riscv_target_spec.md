# riscv_target_spec

> Purpose: Prove that RISC-V backend target contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_target_spec

Purpose: Prove that RISC-V backend target contracts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/riscv_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RISC-V backend target contracts.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### RISC-V backend target contracts

#### uses the typed contract ABI text in LLVM target configuration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the typed contract ABI text in LLVM target configuration
- Verify: uses the typed contract ABI text in LLVM target configuration
   - Expected: linux.abi ?? "" equals `lp64d`
   - Expected: baremetal.abi ?? "" equals `lp64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the typed contract ABI text in LLVM target configuration")
step("Verify: uses the typed contract ABI text in LLVM target configuration")
# @req: REQ-COMP-RISC-V-BACKEND-TARGET-CONTRACTS-001
val linux = LlvmTargetConfig.for_target_with_mode(CodegenTarget.Riscv64, nil, bare_metal: false)
val baremetal = LlvmTargetConfig.for_target_with_mode(CodegenTarget.Riscv64, nil, bare_metal: true)
expect(linux.abi ?? "").to_equal("lp64d")
expect(baremetal.abi ?? "").to_equal("lp64")
```

</details>

#### defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc

- defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc
- Verify: defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc
   - Expected: contract.triple() equals `riscv64-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `lp64d`
   - Expected: contract.march equals `rv64gc`
   - Expected: contract.abi_flag() equals `-mabi=lp64d`
   - Expected: contract.march_flag() equals `-march=rv64gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc")
step("Verify: defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc")
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("lp64d")
expect(contract.march).to_equal("rv64gc")
expect(contract.abi_flag()).to_equal("-mabi=lp64d")
expect(contract.march_flag()).to_equal("-march=rv64gc")
```

</details>

#### defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc

- defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc
- Verify: defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc
   - Expected: contract.triple() equals `riscv32-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `ilp32d`
   - Expected: contract.march equals `rv32gc`
   - Expected: contract.pointer_bits equals `32`
   - Expected: contract.linker equals ``
   - Expected: contract.sysroot equals ``
   - Expected: contract.crt_dir equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc")
step("Verify: defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc")
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.triple()).to_equal("riscv32-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("ilp32d")
expect(contract.march).to_equal("rv32gc")
expect(contract.pointer_bits).to_equal(32)
expect(contract.linker).to_equal("")
expect(contract.sysroot).to_equal("")
expect(contract.crt_dir).to_equal("")
```

</details>

#### fails hosted RV32 linking closed and points to bare metal

- fails hosted RV32 linking closed and points to bare metal
- Verify: fails hosted RV32 linking closed and points to bare metal
   - Expected: toolchain.triple equals `riscv32-unknown-linux-gnu`
   - Expected: toolchain.linker equals ``
   - Expected: toolchain.sysroot equals ``
   - Expected: toolchain.crt_dir equals ``
   - Expected: toolchain.default_flags.len() equals `0`
   - Expected: toolchain.requires_external is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails hosted RV32 linking closed and points to bare metal")
step("Verify: fails hosted RV32 linking closed and points to bare metal")
val toolchain = toolchain_for_target(CodegenTarget.Riscv32)
expect(toolchain.triple).to_equal("riscv32-unknown-linux-gnu")
expect(toolchain.linker).to_equal("")
expect(toolchain.sysroot).to_equal("")
expect(toolchain.crt_dir).to_equal("")
expect(toolchain.default_flags.len()).to_equal(0)
expect(toolchain.requires_external).to_equal(true)
expect(toolchain.install_hint).to_contain("unsupported")
expect(toolchain.install_hint).to_contain("riscv32-unknown-none-elf")
expect(toolchain.diagnostic()).to_contain("No linker configured")
```

</details>

#### does not advertise RV64 link tools for unsupported RV32 rows

- does not advertise RV64 link tools for unsupported RV32 rows
- Verify: does not advertise RV64 link tools for unsupported RV32 rows
   - Expected: entry.level.is_usable() is false
   - Expected: tool does not contain `riscv64-linux-gnu`
   - Expected: rv32_rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not advertise RV64 link tools for unsupported RV32 rows")
step("Verify: does not advertise RV64 link tools for unsupported RV32 rows")
var rv32_rows = 0
for entry in get_support_matrix():
    if entry.target == CodegenTarget.Riscv32:
        rv32_rows = rv32_rows + 1
        expect(entry.level.is_usable()).to_equal(false)
        for tool in entry.required_tools:
            expect(tool.contains("riscv64-linux-gnu")).to_equal(false)
expect(rv32_rows).to_equal(2)
```

</details>

#### keeps compiler and hardware aligned on the RV32 Linux contract

- keeps compiler and hardware aligned on the RV32 Linux contract
- Verify: keeps compiler and hardware aligned on the RV32 Linux contract
   - Expected: compiler_contract.pointer_bits equals `platform.linux.xlen`
   - Expected: compiler_contract.abi equals `platform.linux.abi`
   - Expected: platform.name equals `qemu_virt_rv32`
   - Expected: platform.linux.mmu_mode.to_text() equals `sv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps compiler and hardware aligned on the RV32 Linux contract")
step("Verify: keeps compiler and hardware aligned on the RV32 Linux contract")
val compiler_contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
val platform = qemu_virt_rv32_platform_profile()
expect(compiler_contract.pointer_bits).to_equal(platform.linux.xlen)
expect(compiler_contract.abi).to_equal(platform.linux.abi)
expect(platform.name).to_equal("qemu_virt_rv32")
expect(platform.linux.mmu_mode.to_text()).to_equal("sv32")
```

</details>

#### keeps compiler and hardware aligned on the RV64-first Linux contract

- keeps compiler and hardware aligned on the RV64-first Linux contract
- Verify: keeps compiler and hardware aligned on the RV64-first Linux contract
   - Expected: compiler_contract.pointer_bits equals `platform.linux.xlen`
   - Expected: compiler_contract.abi equals `platform.linux.abi`
   - Expected: platform.name equals `qemu_virt_rv64`
   - Expected: platform.linux.mmu_mode.to_text() equals `sv39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps compiler and hardware aligned on the RV64-first Linux contract")
step("Verify: keeps compiler and hardware aligned on the RV64-first Linux contract")
val compiler_contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
val platform = qemu_virt_rv64_platform_profile()
expect(compiler_contract.pointer_bits).to_equal(platform.linux.xlen)
expect(compiler_contract.abi).to_equal(platform.linux.abi)
expect(platform.name).to_equal("qemu_virt_rv64")
expect(platform.linux.mmu_mode.to_text()).to_equal("sv39")
```

</details>

#### keeps bare-metal contracts on none-elf triples

- keeps bare-metal contracts on none-elf triples
- Verify: keeps bare-metal contracts on none-elf triples
   - Expected: contract.triple() equals `riscv64-unknown-none-elf`
   - Expected: contract.sysroot equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bare-metal contracts on none-elf triples")
step("Verify: keeps bare-metal contracts on none-elf triples")
val contract = riscv_baremetal_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-none-elf")
expect(contract.sysroot).to_equal("")
```

</details>

#### keeps RV64 bare-metal soft-float — no gc march, no lp64d ABI

- keeps RV64 bare-metal soft-float — no gc march, no lp64d ABI
- Verify: keeps RV64 bare-metal soft-float — no gc march, no lp64d ABI
   - Expected: contract.march equals `rv64imac`
   - Expected: contract.abi.to_text() equals `lp64`
   - Expected: contract.abi_text_value equals `lp64`
   - Expected: contract.features does not contain `+d`
   - Expected: contract.features does not contain `+f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps RV64 bare-metal soft-float — no gc march, no lp64d ABI")
step("Verify: keeps RV64 bare-metal soft-float — no gc march, no lp64d ABI")
val contract = riscv_baremetal_target_contract(CodegenTarget.Riscv64)
expect(contract.march).to_equal("rv64imac")
expect(contract.abi.to_text()).to_equal("lp64")
expect(contract.abi_text_value).to_equal("lp64")
expect(contract.features.contains("+d")).to_equal(false)
expect(contract.features.contains("+f")).to_equal(false)
```

</details>

#### keeps RV32 on its supported bare-metal contract

- keeps RV32 on its supported bare-metal contract
- Verify: keeps RV32 on its supported bare-metal contract
   - Expected: contract.triple() equals `riscv32-unknown-none-elf`
   - Expected: contract.abi.to_text() equals `ilp32`
   - Expected: contract.sysroot equals ``
   - Expected: contract.crt_dir equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps RV32 on its supported bare-metal contract")
step("Verify: keeps RV32 on its supported bare-metal contract")
val contract = riscv_baremetal_target_contract(CodegenTarget.Riscv32)
expect(contract.triple()).to_equal("riscv32-unknown-none-elf")
expect(contract.abi.to_text()).to_equal("ilp32")
expect(contract.sysroot).to_equal("")
expect(contract.crt_dir).to_equal("")
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-RISC-V-BACKEND-TARGET-CONTRACTS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0c723454381e51cd86d599ee717d7bfe2b6bd595d7d923536182ce6911efb40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0c723454381e51cd86d599ee717d7bfe2b6bd595d7d923536182ce6911efb40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0c723454381e51cd86d599ee717d7bfe2b6bd595d7d923536182ce6911efb40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/riscv_target_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/riscv_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/riscv_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/riscv_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/riscv_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/riscv_target_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the typed contract ABI text in LLVM target configuration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/riscv_target_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/riscv_target_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
