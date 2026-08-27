# Bootstrap Pipeline Specification

> Tests covering AC-6 — x86_64 bootstrap lane succeeds, AC-6 — i686 bootstrap lane succeeds, AC-6 — aarch64 bootstrap lane succeeds, AC-6 — armv7 bootstrap lane succeeds, AC-6 — riscv64 bootstrap lane succeeds, AC-6 — riscv32imac bootstrap lane succeeds, AC-6 — qemu_runner backend dispatch routes 32-bit to LLVM.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Pipeline Specification

## Scenarios

### AC-6 — x86_64 bootstrap lane succeeds

#### result file exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- result file exists
   - Expected: file_exists(_bootstrap_path("x86_64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result file exists")
expect(file_exists(_bootstrap_path("x86_64"))).to_equal(true)
```

</details>

#### exit code is 0

- exit code is 0
   - Expected: r contains `"exit_code": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exit code is 0")
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### bootable image artifact path is recorded

- bootable image artifact path is recorded
   - Expected: r contains `"image_path"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bootable image artifact path is recorded")
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"image_path\"")).to_equal(true)
```

</details>

#### post-deploy smoke is green

- post-deploy smoke is green
   - Expected: r contains `"smoke_status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("post-deploy smoke is green")
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"smoke_status\": \"pass\"")).to_equal(true)
```

</details>

#### uses Limine boot loader

- uses Limine boot loader
   - Expected: r contains `"loader": "limine"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses Limine boot loader")
val r: text = file_read(_bootstrap_path("x86_64"))
expect(r.contains("\"loader\": \"limine\"")).to_equal(true)
```

</details>

### AC-6 — i686 bootstrap lane succeeds

#### result file exists

- result file exists
   - Expected: file_exists(_bootstrap_path("i686")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result file exists")
expect(file_exists(_bootstrap_path("i686"))).to_equal(true)
```

</details>

#### exit code is 0

- exit code is 0
   - Expected: r contains `"exit_code": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exit code is 0")
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### post-deploy smoke is green

- post-deploy smoke is green
   - Expected: r contains `"smoke_status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("post-deploy smoke is green")
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"smoke_status\": \"pass\"")).to_equal(true)
```

</details>

#### uses Limine boot loader

- uses Limine boot loader
   - Expected: r contains `"loader": "limine"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses Limine boot loader")
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"loader\": \"limine\"")).to_equal(true)
```

</details>

#### 32-bit lane used LLVM backend

- 32-bit lane used LLVM backend
   - Expected: r contains `"backend": "Llvm"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("32-bit lane used LLVM backend")
val r: text = file_read(_bootstrap_path("i686"))
expect(r.contains("\"backend\": \"Llvm\"")).to_equal(true)
```

</details>

### AC-6 — aarch64 bootstrap lane succeeds

#### result file exists

- result file exists
   - Expected: file_exists(_bootstrap_path("aarch64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result file exists")
expect(file_exists(_bootstrap_path("aarch64"))).to_equal(true)
```

</details>

#### exit code is 0

- exit code is 0
   - Expected: r contains `"exit_code": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exit code is 0")
val r: text = file_read(_bootstrap_path("aarch64"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses U-Boot + DTB

- uses U-Boot + DTB
   - Expected: r contains `"loader": "u-boot"`
   - Expected: r contains `"dtb"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses U-Boot + DTB")
val r: text = file_read(_bootstrap_path("aarch64"))
expect(r.contains("\"loader\": \"u-boot\"")).to_equal(true)
expect(r.contains("\"dtb\"")).to_equal(true)
```

</details>

### AC-6 — armv7 bootstrap lane succeeds

#### result file exists

- result file exists
   - Expected: file_exists(_bootstrap_path("armv7")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result file exists")
expect(file_exists(_bootstrap_path("armv7"))).to_equal(true)
```

</details>

#### exit code is 0

- exit code is 0
   - Expected: r contains `"exit_code": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exit code is 0")
val r: text = file_read(_bootstrap_path("armv7"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses U-Boot + DTB

- uses U-Boot + DTB
   - Expected: r contains `"loader": "u-boot"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses U-Boot + DTB")
val r: text = file_read(_bootstrap_path("armv7"))
expect(r.contains("\"loader\": \"u-boot\"")).to_equal(true)
```

</details>

#### 32-bit lane used LLVM backend

- 32-bit lane used LLVM backend
   - Expected: r contains `"backend": "Llvm"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("32-bit lane used LLVM backend")
val r: text = file_read(_bootstrap_path("armv7"))
expect(r.contains("\"backend\": \"Llvm\"")).to_equal(true)
```

</details>

### AC-6 — riscv64 bootstrap lane succeeds

#### result file exists

- result file exists
   - Expected: file_exists(_bootstrap_path("riscv64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result file exists")
expect(file_exists(_bootstrap_path("riscv64"))).to_equal(true)
```

</details>

#### exit code is 0

- exit code is 0
   - Expected: r contains `"exit_code": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exit code is 0")
val r: text = file_read(_bootstrap_path("riscv64"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses OpenSBI

- uses OpenSBI
   - Expected: r contains `"loader": "opensbi"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses OpenSBI")
val r: text = file_read(_bootstrap_path("riscv64"))
expect(r.contains("\"loader\": \"opensbi\"")).to_equal(true)
```

</details>

### AC-6 — riscv32imac bootstrap lane succeeds

#### result file exists

- result file exists
   - Expected: file_exists(_bootstrap_path("riscv32")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result file exists")
expect(file_exists(_bootstrap_path("riscv32"))).to_equal(true)
```

</details>

#### exit code is 0

- exit code is 0
   - Expected: r contains `"exit_code": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exit code is 0")
val r: text = file_read(_bootstrap_path("riscv32"))
expect(r.contains("\"exit_code\": 0")).to_equal(true)
```

</details>

#### uses OpenSBI

- uses OpenSBI
   - Expected: r contains `"loader": "opensbi"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses OpenSBI")
val r: text = file_read(_bootstrap_path("riscv32"))
expect(r.contains("\"loader\": \"opensbi\"")).to_equal(true)
```

</details>

#### 32-bit lane used LLVM backend

- 32-bit lane used LLVM backend
   - Expected: r contains `"backend": "Llvm"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("32-bit lane used LLVM backend")
val r: text = file_read(_bootstrap_path("riscv32"))
expect(r.contains("\"backend\": \"Llvm\"")).to_equal(true)
```

</details>

### AC-6 — qemu_runner backend dispatch routes 32-bit to LLVM

#### qemu_runner.spl exists

- qemu_runner.spl exists
   - Expected: file_exists("src/os/qemu_runner.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("qemu_runner.spl exists")
expect(file_exists("src/os/qemu_runner.spl")).to_equal(true)
```

</details>

#### qemu_runner declares the backend dispatch helper

- qemu_runner declares the backend dispatch helper
   - Expected: body contains `_os_build_backend_for_target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("qemu_runner declares the backend dispatch helper")
val body: text = file_read("src/os/qemu_runner.spl")
expect(body.contains("_os_build_backend_for_target")).to_equal(true)
```

</details>

#### qemu_runner mentions Llvm as a backend choice

- qemu_runner mentions Llvm as a backend choice
   - Expected: body contains `Llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("qemu_runner mentions Llvm as a backend choice")
val body: text = file_read("src/os/_QemuRunner/runner_targets.spl")
expect(body.contains("Llvm")).to_equal(true)
```

</details>

#### qemu_runner handles i686 target

- qemu_runner handles i686 target
   - Expected: body contains `i686`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("qemu_runner handles i686 target")
val body: text = file_read("src/os/_QemuRunner/runner_targets.spl")
expect(body.contains("i686")).to_equal(true)
```

</details>

#### qemu_runner handles armv7 target

- qemu_runner handles armv7 target
   - Expected: body contains `armv7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("qemu_runner handles armv7 target")
val body: text = file_read("src/os/_QemuRunner/runner_targets.spl")
expect(body.contains("armv7")).to_equal(true)
```

</details>

#### qemu_runner handles riscv32 target

- qemu_runner handles riscv32 target
   - Expected: body contains `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("qemu_runner handles riscv32 target")
val body: text = file_read("src/os/qemu_runner.spl")
expect(body.contains("riscv32")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/multiarch/bootstrap_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-6 — x86_64 bootstrap lane succeeds, AC-6 — i686 bootstrap lane succeeds, AC-6 — aarch64 bootstrap lane succeeds, AC-6 — armv7 bootstrap lane succeeds, AC-6 — riscv64 bootstrap lane succeeds, AC-6 — riscv32imac bootstrap lane succeeds, AC-6 — qemu_runner backend dispatch routes 32-bit to LLVM.
- AC-6 — x86_64 bootstrap lane succeeds
- AC-6 — i686 bootstrap lane succeeds
- AC-6 — aarch64 bootstrap lane succeeds
- AC-6 — armv7 bootstrap lane succeeds
- AC-6 — riscv64 bootstrap lane succeeds
- AC-6 — riscv32imac bootstrap lane succeeds
- AC-6 — qemu_runner backend dispatch routes 32-bit to LLVM

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ab271068371b77994052757cf1684dc67414c74894dc2ed668f83da005b3460`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ab271068371b77994052757cf1684dc67414c74894dc2ed668f83da005b3460`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ab271068371b77994052757cf1684dc67414c74894dc2ed668f83da005b3460`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/multiarch/bootstrap_pipeline_spec.spl
mirror: doc/06_spec/03_system/os/multiarch/bootstrap_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/multiarch/bootstrap_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/multiarch/bootstrap_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/multiarch/bootstrap_pipeline_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'result file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/multiarch/bootstrap_pipeline_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exit code is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/multiarch/bootstrap_pipeline_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bootable image artifact path is recorded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
