# Six Arch Boot Specification

> Tests covering AC-4 — x86_64-unknown-simpleos boots + smoke green, AC-4 — i686-unknown-simpleos (x86_32) boots + smoke green, AC-4 — aarch64-unknown-simpleos boots + smoke green, AC-4 — armv7-unknown-simpleos boots + smoke green, AC-4 — riscv64gc-unknown-simpleos boots + smoke green, AC-4 — riscv32imac-unknown-simpleos boots + smoke green, AC-4 — x86_64 baseline regression gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Six Arch Boot Specification

## Scenarios

### AC-4 — x86_64-unknown-simpleos boots + smoke green

#### smoke result file exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- smoke result file exists
   - Expected: file_exists(_smoke_path("x86_64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke result file exists")
expect(file_exists(_smoke_path("x86_64"))).to_equal(true)
```

</details>

#### boot banner printed

- boot banner printed
   - Expected: r contains `"banner": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner printed")
val r: text = file_read(_smoke_path("x86_64"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

- NVFS mounted
   - Expected: r contains `"nvfs_mounted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NVFS mounted")
val r: text = file_read(_smoke_path("x86_64"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

- smoke suite green
   - Expected: r contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke suite green")
val r: text = file_read(_smoke_path("x86_64"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — i686-unknown-simpleos (x86_32) boots + smoke green

#### smoke result file exists

- smoke result file exists
   - Expected: file_exists(_smoke_path("i686")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke result file exists")
expect(file_exists(_smoke_path("i686"))).to_equal(true)
```

</details>

#### boot banner printed

- boot banner printed
   - Expected: r contains `"banner": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner printed")
val r: text = file_read(_smoke_path("i686"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

- NVFS mounted
   - Expected: r contains `"nvfs_mounted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NVFS mounted")
val r: text = file_read(_smoke_path("i686"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

- smoke suite green
   - Expected: r contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke suite green")
val r: text = file_read(_smoke_path("i686"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — aarch64-unknown-simpleos boots + smoke green

#### smoke result file exists

- smoke result file exists
   - Expected: file_exists(_smoke_path("aarch64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke result file exists")
expect(file_exists(_smoke_path("aarch64"))).to_equal(true)
```

</details>

#### boot banner printed

- boot banner printed
   - Expected: r contains `"banner": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner printed")
val r: text = file_read(_smoke_path("aarch64"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

- NVFS mounted
   - Expected: r contains `"nvfs_mounted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NVFS mounted")
val r: text = file_read(_smoke_path("aarch64"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

- smoke suite green
   - Expected: r contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke suite green")
val r: text = file_read(_smoke_path("aarch64"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — armv7-unknown-simpleos boots + smoke green

#### smoke result file exists

- smoke result file exists
   - Expected: file_exists(_smoke_path("armv7")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke result file exists")
expect(file_exists(_smoke_path("armv7"))).to_equal(true)
```

</details>

#### boot banner printed

- boot banner printed
   - Expected: r contains `"banner": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner printed")
val r: text = file_read(_smoke_path("armv7"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

- NVFS mounted
   - Expected: r contains `"nvfs_mounted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NVFS mounted")
val r: text = file_read(_smoke_path("armv7"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

- smoke suite green
   - Expected: r contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke suite green")
val r: text = file_read(_smoke_path("armv7"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — riscv64gc-unknown-simpleos boots + smoke green

#### smoke result file exists

- smoke result file exists
   - Expected: file_exists(_smoke_path("riscv64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke result file exists")
expect(file_exists(_smoke_path("riscv64"))).to_equal(true)
```

</details>

#### boot banner printed

- boot banner printed
   - Expected: r contains `"banner": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner printed")
val r: text = file_read(_smoke_path("riscv64"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

- NVFS mounted
   - Expected: r contains `"nvfs_mounted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NVFS mounted")
val r: text = file_read(_smoke_path("riscv64"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

- smoke suite green
   - Expected: r contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke suite green")
val r: text = file_read(_smoke_path("riscv64"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — riscv32imac-unknown-simpleos boots + smoke green

#### smoke result file exists

- smoke result file exists
   - Expected: file_exists(_smoke_path("riscv32")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke result file exists")
expect(file_exists(_smoke_path("riscv32"))).to_equal(true)
```

</details>

#### boot banner printed

- boot banner printed
   - Expected: r contains `"banner": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner printed")
val r: text = file_read(_smoke_path("riscv32"))
expect(r.contains("\"banner\": true")).to_equal(true)
```

</details>

#### NVFS mounted

- NVFS mounted
   - Expected: r contains `"nvfs_mounted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NVFS mounted")
val r: text = file_read(_smoke_path("riscv32"))
expect(r.contains("\"nvfs_mounted\": true")).to_equal(true)
```

</details>

#### smoke suite green

- smoke suite green
   - Expected: r contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("smoke suite green")
val r: text = file_read(_smoke_path("riscv32"))
expect(r.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

### AC-4 — x86_64 baseline regression gate

#### x86_64 baseline checkpoint file exists

- x86_64 baseline checkpoint file exists
   - Expected: file_exists(_baseline_path("x86_64")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64 baseline checkpoint file exists")
expect(file_exists(_baseline_path("x86_64"))).to_equal(true)
```

</details>

#### x86_64 baseline matches current smoke result

- x86_64 baseline matches current smoke result
   - Expected: current contains `"baseline_match": true`
   - Expected: baseline contains `"status": "pass"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64 baseline matches current smoke result")
val current:  text = file_read(_smoke_path("x86_64"))
val baseline: text = file_read(_baseline_path("x86_64"))
expect(current.contains("\"baseline_match\": true")).to_equal(true)
expect(baseline.contains("\"status\": \"pass\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/multiarch/six_arch_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-4 — x86_64-unknown-simpleos boots + smoke green, AC-4 — i686-unknown-simpleos (x86_32) boots + smoke green, AC-4 — aarch64-unknown-simpleos boots + smoke green, AC-4 — armv7-unknown-simpleos boots + smoke green, AC-4 — riscv64gc-unknown-simpleos boots + smoke green, AC-4 — riscv32imac-unknown-simpleos boots + smoke green, AC-4 — x86_64 baseline regression gate.
- AC-4 — x86_64-unknown-simpleos boots + smoke green
- AC-4 — i686-unknown-simpleos (x86_32) boots + smoke green
- AC-4 — aarch64-unknown-simpleos boots + smoke green
- AC-4 — armv7-unknown-simpleos boots + smoke green
- AC-4 — riscv64gc-unknown-simpleos boots + smoke green
- AC-4 — riscv32imac-unknown-simpleos boots + smoke green
- AC-4 — x86_64 baseline regression gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `10c97585f8baee4e416526a03a21f49decfa053130f9a66a498751b9c752d6a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10c97585f8baee4e416526a03a21f49decfa053130f9a66a498751b9c752d6a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10c97585f8baee4e416526a03a21f49decfa053130f9a66a498751b9c752d6a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/multiarch/six_arch_boot_spec.spl
mirror: doc/06_spec/03_system/os/multiarch/six_arch_boot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/multiarch/six_arch_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/multiarch/six_arch_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/multiarch/six_arch_boot_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'smoke result file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/multiarch/six_arch_boot_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boot banner printed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/multiarch/six_arch_boot_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NVFS mounted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
