# Nvfs Elf Load Specification

> Tests covering ELF binary from NVFS arena — store and load chain.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Elf Load Specification

## Scenarios

### ELF binary from NVFS arena — store and load chain

#### synthetic ELF64 x86 round-trips through NVMe arena

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- synthetic ELF64 x86 round-trips through NVMe arena
   - Expected: elf_bytes.len() as i64 equals `120`
   - Expected: elf_bytes[0] equals `0x7F`
   - Expected: elf_bytes[1] equals `0x45`
   - Expected: aid > 0 is true
   - Expected: w equals `120`
   - Expected: arena_total_bytes_impl(aid) equals `120`
   - Expected: readback.len() as i64 equals `120`
   - Expected: readback[0] equals `0x7F`
   - Expected: readback[1] equals `0x45`
   - Expected: readback[2] equals `0x4C`
   - Expected: readback[3] equals `0x46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic ELF64 x86 round-trips through NVMe arena")
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val elf_bytes = _make_elf64_x86()
expect(elf_bytes.len() as i64).to_equal(120)
expect(elf_bytes[0]).to_equal(0x7F)
expect(elf_bytes[1]).to_equal(0x45)
val aid = arena_create_nvme_impl(0, 4096, 4, 32)
expect(aid > 0).to_equal(true)
val w = arena_append_impl(aid, elf_bytes, 0)
expect(w).to_equal(120)
expect(arena_total_bytes_impl(aid)).to_equal(120)
val readback = arena_readv_impl(aid, 0, 120)
expect(readback.len() as i64).to_equal(120)
expect(readback[0]).to_equal(0x7F)
expect(readback[1]).to_equal(0x45)
expect(readback[2]).to_equal(0x4C)
expect(readback[3]).to_equal(0x46)
```

</details>

#### ELF loader parses bytes read from NVMe arena

- ELF loader parses bytes read from NVMe arena
   - Expected: aid > 0 is true
   - Expected: w equals `120`
   - Expected: readback.len() as i64 equals `120`
   - Expected: result.is_ok() is true
   - Expected: image.entry > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ELF loader parses bytes read from NVMe arena")
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val elf_bytes = _make_elf64_x86()
val aid = arena_create_nvme_impl(0, 4096, 40, 32)
expect(aid > 0).to_equal(true)
val w = arena_append_impl(aid, elf_bytes, 0)
expect(w).to_equal(120)
val readback = arena_readv_impl(aid, 0, 120)
expect(readback.len() as i64).to_equal(120)
val result = load_user_executable(readback, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val image = result.unwrap()
expect(image.entry > 0).to_equal(true)
```

</details>

#### boot_fs_load_and_validate_elf rejects too-small arena data

- boot_fs_load_and_validate_elf rejects too-small arena data
   - Expected: aid > 0 is true
   - Expected: w equals `2`
   - Expected: readback.len() as i64 equals `2`
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot_fs_load_and_validate_elf rejects too-small arena data")
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 76, 8)
expect(aid > 0).to_equal(true)
val tiny: [u8] = [0x00, 0x01]
val w = arena_append_impl(aid, tiny, 0)
expect(w).to_equal(2)
val readback = arena_readv_impl(aid, 0, 2)
expect(readback.len() as i64).to_equal(2)
val result = load_user_executable(readback, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/nvfs_elf_load_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ELF binary from NVFS arena — store and load chain.
- ELF binary from NVFS arena — store and load chain

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `998e1be00e7819737be66c8f30f32aee406fc580d58ffd7627083abb25041a4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `998e1be00e7819737be66c8f30f32aee406fc580d58ffd7627083abb25041a4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `998e1be00e7819737be66c8f30f32aee406fc580d58ffd7627083abb25041a4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/kernel/nvfs_elf_load_spec.spl
mirror: doc/06_spec/03_system/os/kernel/nvfs_elf_load_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/kernel/nvfs_elf_load_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/kernel/nvfs_elf_load_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/kernel/nvfs_elf_load_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/kernel/nvfs_elf_load_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'synthetic ELF64 x86 round-trips through NVMe arena' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/kernel/nvfs_elf_load_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ELF loader parses bytes read from NVMe arena' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/kernel/nvfs_elf_load_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boot_fs_load_and_validate_elf rejects too-small arena data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
