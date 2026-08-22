# baremetal_build_spec

> Verifies the baremetal build behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# baremetal_build_spec

Verifies the baremetal build behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/02_integration/baremetal/baremetal_build_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the baremetal build behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Bare-Metal Build System

### Linker Scripts

<details>
<summary>Advanced: ARM linker script exists</summary>

#### ARM linker script exists _(slow)_

- Verify: ARM linker script exists
   - Expected: file_exists("src/compiler/baremetal/arm/linker.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: ARM linker script exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(file_exists("src/compiler/baremetal/arm/linker.ld")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: x86_64 linker script exists</summary>

#### x86_64 linker script exists _(slow)_

- Verify: x86_64 linker script exists
   - Expected: file_exists("src/compiler/baremetal/x86_64/linker.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: x86_64 linker script exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(file_exists("src/compiler/baremetal/x86_64/linker.ld")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: RISC-V linker script exists</summary>

#### RISC-V linker script exists _(slow)_

- Verify: RISC-V linker script exists
   - Expected: file_exists("src/compiler/baremetal/riscv/linker.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: RISC-V linker script exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(file_exists("src/compiler/baremetal/riscv/linker.ld")).to_equal(true)
```

</details>


</details>

### Startup Code

<details>
<summary>Advanced: ARM crt0.s exists</summary>

#### ARM crt0.s exists _(slow)_

- Verify: ARM crt0.s exists
   - Expected: file_exists("src/compiler/baremetal/arm/crt0.s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: ARM crt0.s exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(file_exists("src/compiler/baremetal/arm/crt0.s")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: x86_64 crt0.s exists</summary>

#### x86_64 crt0.s exists _(slow)_

- Verify: x86_64 crt0.s exists
   - Expected: file_exists("src/compiler/baremetal/x86_64/crt0.s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: x86_64 crt0.s exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(file_exists("src/compiler/baremetal/x86_64/crt0.s")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: RISC-V crt0.s exists</summary>

#### RISC-V crt0.s exists _(slow)_

- Verify: RISC-V crt0.s exists
   - Expected: file_exists("src/compiler/baremetal/riscv/crt0.s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: RISC-V crt0.s exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(file_exists("src/compiler/baremetal/riscv/crt0.s")).to_equal(true)
```

</details>


</details>

### Configuration

<details>
<summary>Advanced: ARM config has correct paths</summary>

#### ARM config has correct paths _(slow)_

- Verify: ARM config has correct paths
   - Expected: config.linker_script equals `src/compiler/baremetal/arm/linker.ld`
   - Expected: config.crt0_path equals `src/compiler/baremetal/arm/crt0.s`
   - Expected: config.entry_point equals `reset_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: ARM config has correct paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_arm()
expect(config.linker_script).to_equal("src/compiler/baremetal/arm/linker.ld")
expect(config.crt0_path).to_equal("src/compiler/baremetal/arm/crt0.s")
expect(config.entry_point).to_equal("reset_handler")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 config has correct paths</summary>

#### x86_64 config has correct paths _(slow)_

- Verify: x86_64 config has correct paths
   - Expected: config.linker_script equals `src/compiler/baremetal/x86_64/linker.ld`
   - Expected: config.crt0_path equals `src/compiler/baremetal/x86_64/crt0.s`
   - Expected: config.entry_point equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: x86_64 config has correct paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_x86_64()
expect(config.linker_script).to_equal("src/compiler/baremetal/x86_64/linker.ld")
expect(config.crt0_path).to_equal("src/compiler/baremetal/x86_64/crt0.s")
expect(config.entry_point).to_equal("_start")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V config has correct paths</summary>

#### RISC-V config has correct paths _(slow)_

- Verify: RISC-V config has correct paths
   - Expected: config.linker_script equals `src/compiler/baremetal/riscv/linker.ld`
   - Expected: config.crt0_path equals `src/compiler/baremetal/riscv/crt0.s`
   - Expected: config.entry_point equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: RISC-V config has correct paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_riscv()
expect(config.linker_script).to_equal("src/compiler/baremetal/riscv/linker.ld")
expect(config.crt0_path).to_equal("src/compiler/baremetal/riscv/crt0.s")
expect(config.entry_point).to_equal("_start")
```

</details>


</details>

### Target Triples

<details>
<summary>Advanced: ARM target triple</summary>

#### ARM target triple _(slow)_

- Verify: ARM target triple
   - Expected: config.target_triple() equals `armv7m-none-eabi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: ARM target triple")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_arm()
expect(config.target_triple()).to_equal("armv7m-none-eabi")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 target triple</summary>

#### x86_64 target triple _(slow)_

- Verify: x86_64 target triple
   - Expected: config.target_triple() equals `x86_64-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: x86_64 target triple")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_x86_64()
expect(config.target_triple()).to_equal("x86_64-unknown-none")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V target triple</summary>

#### RISC-V target triple _(slow)_

- Verify: RISC-V target triple
   - Expected: config.target_triple() equals `riscv64gc-unknown-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: RISC-V target triple")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_riscv()
expect(config.target_triple()).to_equal("riscv64gc-unknown-none-elf")
```

</details>


</details>

### Test Output Parsing

<details>
<summary>Advanced: parses passing tests</summary>

#### parses passing tests _(slow)_

- Verify: parses passing tests
   - Expected: result.tests_run equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result.tests_passed equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result.tests_failed equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: parses passing tests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val output = "[TEST START]\n[PASS] test_one\n[PASS] test_two\n[TEST END] passed=2 failed=0"
val result = parse_test_output(output, 1)
expect(result.tests_run).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result.tests_passed).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result.tests_failed).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result.success).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses failing tests</summary>

#### parses failing tests _(slow)_

- Verify: parses failing tests
   - Expected: result.tests_run equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result.tests_passed equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result.tests_failed equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: parses failing tests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val output = "[TEST START]\n[PASS] test_one\n[FAIL] test_two: assertion failed\n[TEST END] passed=1 failed=1"
val result = parse_test_output(output, 1)
expect(result.tests_run).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result.tests_passed).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result.tests_failed).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(result.success).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: adjusts QEMU exit codes correctly</summary>

#### adjusts QEMU exit codes correctly _(slow)_

- Verify: adjusts QEMU exit codes correctly
   - Expected: result1.exit_code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: result2.exit_code equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: adjusts QEMU exit codes correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# isa-debug-exit: exit code 0 becomes 1
val result1 = parse_test_output("", 1)
expect(result1.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

# isa-debug-exit: exit code 1 becomes 3
val result2 = parse_test_output("", 3)
expect(result2.exit_code).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>


</details>

### QEMU Runner

<details>
<summary>Advanced: ARM QEMU executable</summary>

#### ARM QEMU executable _(slow)_

- Verify: ARM QEMU executable
   - Expected: runner.qemu_executable() equals `qemu-system-arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: ARM QEMU executable")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_arm()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-arm")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 QEMU executable</summary>

#### x86_64 QEMU executable _(slow)_

- Verify: x86_64 QEMU executable
   - Expected: runner.qemu_executable() equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: x86_64 QEMU executable")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_x86_64()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-x86_64")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V QEMU executable</summary>

#### RISC-V QEMU executable _(slow)_

- Verify: RISC-V QEMU executable
   - Expected: runner.qemu_executable() equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-BAREMETAL_BAREMETAL_BUILD-001
step("Verify: RISC-V QEMU executable")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = baremetal_config_riscv()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-riscv64")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5275f47050de488d82cb8694a85e1d049e0395844e31e0f35782cf950895a45d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5275f47050de488d82cb8694a85e1d049e0395844e31e0f35782cf950895a45d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5275f47050de488d82cb8694a85e1d049e0395844e31e0f35782cf950895a45d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/baremetal/baremetal_build_spec.spl
mirror: doc/06_spec/02_integration/baremetal/baremetal_build_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/baremetal/baremetal_build_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/baremetal/baremetal_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/baremetal/baremetal_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
