# Executable Source Specification

> Tests covering executable source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executable Source Specification

## Scenarios

### executable source

#### resolves the canonical rv64 proof binary path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the canonical rv64 proof binary path
   - Expected: result.is_ok() is true
   - Expected: image.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the canonical rv64 proof binary path")
val result = resolve_executable_bytes(RV64_PROOF_BINARY_PATH, Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves rv64 bytes for known binaries

- resolves rv64 bytes for known binaries
   - Expected: result.is_ok() is true
   - Expected: image.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves rv64 bytes for known binaries")
val result = resolve_executable_bytes("/sys/services/vfs", Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves rv32 bytes for known binaries

- resolves rv32 bytes for known binaries
   - Expected: result.is_ok() is true
   - Expected: image.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves rv32 bytes for known binaries")
val result = resolve_executable_bytes("/sys/apps/desktop", Architecture.Riscv32)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv32)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves the canonical rv32 proof binary path

- resolves the canonical rv32 proof binary path
   - Expected: result.is_ok() is true
   - Expected: image.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the canonical rv32 proof binary path")
val result = resolve_executable_bytes(RV32_PROOF_BINARY_PATH, Architecture.Riscv32)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv32)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves x86_64 synthetic initramfs bytes by exact path

- resolves x86_64 synthetic initramfs bytes by exact path
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x11.to_u8()`
   - Expected: bytes[3] equals `0x44.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves x86_64 synthetic initramfs bytes by exact path")
_clear_synthetic_initramfs_for_test()
var payload: [u8] = []
payload.push(0x11.to_u8())
payload.push(0x22.to_u8())
payload.push(0x33.to_u8())
payload.push(0x44.to_u8())
_set_synthetic_initramfs_for_test("/usr/bin/x86_exec_probe", payload)

val result = resolve_executable_bytes("/usr/bin/x86_exec_probe", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x11.to_u8())
expect(bytes[3]).to_equal(0x44.to_u8())
_clear_synthetic_initramfs_for_test()
```

</details>

#### canonicalizes info path bytes through the VFS executable reader

- canonicalizes info path bytes through the VFS executable reader
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `5`
   - Expected: bytes[4] equals `0x10.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonicalizes info path bytes through the VFS executable reader")
_clear_synthetic_vfs_for_test()
var path_bytes: [u8] = []
for ch in "/sys/apps/info":
    path_bytes.push(ch.to_u8())
var payload: [u8] = []
payload.push(0x7F.to_u8())
payload.push(0x45.to_u8())
payload.push(0x4C.to_u8())
payload.push(0x46.to_u8())
payload.push(0x10.to_u8())
_set_synthetic_vfs_file_for_test("/sys/apps/info", payload)

val result = resolve_executable_bytes_from_path_bytes(path_bytes, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(5)
expect(bytes[4]).to_equal(0x10.to_u8())
_clear_synthetic_vfs_for_test()
```

</details>

#### rejects unknown binary paths

- rejects unknown binary paths
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown binary paths")
val result = resolve_executable_bytes("/sys/apps/missing", Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects unsupported host architectures

- rejects unsupported host architectures
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported host architectures")
val result = resolve_executable_bytes("/sys/services/vfs", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/executable_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering executable source.
- executable source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da5509ee175814d041f0252804397493847f040352064d1d05f004815464aed8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da5509ee175814d041f0252804397493847f040352064d1d05f004815464aed8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da5509ee175814d041f0252804397493847f040352064d1d05f004815464aed8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/loader/executable_source_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/executable_source_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/executable_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/executable_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/executable_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/loader/executable_source_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the canonical rv64 proof binary path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/executable_source_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves rv64 bytes for known binaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/executable_source_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves rv32 bytes for known binaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
