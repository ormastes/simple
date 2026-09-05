# Nvfs Dbfs Backed Root Source Specification

> Tests covering SimpleOS NVFS DBFS-backed production root source contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Dbfs Backed Root Source Specification

## Scenarios

### SimpleOS NVFS DBFS-backed production root source contract

#### mounts the canonical NVFS driver through the MountTable root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mounts the canonical NVFS driver through the MountTable root
   - Expected: source contains `NvfsDriver.new_on_device(`
   - Expected: source contains `vfs_mount_rootfs(DriverInstance.Nvfs(driver_r.unwrap()))`
   - Expected: source contains `nvfs_boot_select_valid_superblock(dev)`
   - Expected: source contains `nvfs_superblock_read_from_bytes(bytes.unwrap())`
   - Expected: source contains `dbfs_superblock_validate(backing_sb)`
   - Expected: source contains `backing_sb.block_count.to_i64()`
   - Expected: source contains `shim_positioned_install_backend_route_v1(`
   - Expected: source contains `SosixPositionedBackendKindV1.Nvfs`
   - Expected: source contains `SosixPositionedBackendKindV1.Dbfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("mounts the canonical NVFS driver through the MountTable root")
val source = _source("src/os/kernel/boot/boot_fs.spl")
expect(source.contains("NvfsDriver.new_on_device(")).to_equal(true)
expect(source.contains("vfs_mount_rootfs(DriverInstance.Nvfs(driver_r.unwrap()))")).to_equal(true)
expect(source.contains("nvfs_boot_select_valid_superblock(dev)")).to_equal(true)
expect(source.contains("nvfs_superblock_read_from_bytes(bytes.unwrap())")).to_equal(true)
expect(source.contains("dbfs_superblock_validate(backing_sb)")).to_equal(true)
expect(source.contains("backing_sb.block_count.to_i64()")).to_equal(true)
expect(source.contains("shim_positioned_install_backend_route_v1(")).to_equal(true)
expect(source.contains("SosixPositionedBackendKindV1.Nvfs")).to_equal(true)
expect(source.contains("SosixPositionedBackendKindV1.Dbfs")).to_equal(true)
```

</details>

#### fails over from a checksum-corrupt primary replica

- fails over from a checksum-corrupt primary replica
   - Expected: nvfs_superblock_format_disk(11u64, 22u64) is true
   - Expected: dev.write_sector(0u64, primary).is_ok() is true
   - Expected: selected.? is true
   - Expected: selected.unwrap().replica_id equals `1u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails over from a checksum-corrupt primary replica")
val dev = MemBlockDevice.new(8u64, 512u32)
nvfs_superblock_set_device(dev)
expect(nvfs_superblock_format_disk(11u64, 22u64)).to_equal(true)
var primary = dev.read_sector(0u64).unwrap()
primary[50] = primary[50] ^ 0x01u8
expect(dev.write_sector(0u64, primary).is_ok()).to_equal(true)

val selected = nvfs_boot_select_valid_superblock(dev)
expect(selected.?).to_equal(true)
expect(selected.unwrap().replica_id).to_equal(1u8)
```

</details>

#### names the DBFS-backed provider and exact persistence boundaries

- names the DBFS-backed provider and exact persistence boundaries
   - Expected: source contains `[NVFS] mounted as root filesystem provider=nvfs-dbfs-backed-v1`
   - Expected: source contains `[boot-fs] NVFS persistence check: written:first-boot`
   - Expected: source contains `[boot-fs] NVFS persistence check: persisted:match content=nvfs-persist-ok`
   - Expected: source contains `[boot-fs] NVFS persistence check: FAILED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("names the DBFS-backed provider and exact persistence boundaries")
val source = _source("src/os/kernel/boot/boot_fs.spl")
expect(source.contains("[NVFS] mounted as root filesystem provider=nvfs-dbfs-backed-v1")).to_equal(true)
expect(source.contains("[boot-fs] NVFS persistence check: written:first-boot")).to_equal(true)
expect(source.contains("[boot-fs] NVFS persistence check: persisted:match content=nvfs-persist-ok")).to_equal(true)
expect(source.contains("[boot-fs] NVFS persistence check: FAILED")).to_equal(true)
```

</details>

#### exercises byte-exact positioned I/O through canonical SOSIX dispatch

- exercises byte-exact positioned I/O through canonical SOSIX dispatch
   - Expected: source contains `sosix_positioned_acceptance_round_trip_v1(`
   - Expected: source contains `SosixPositionedBackendKindV1.Nvfs`
   - Expected: source does not contain `g_vfs_nvfs_write_at(`
   - Expected: source does not contain `g_vfs_nvfs_read_at(`
   - Expected: source contains `data[0] == 0u8 and data[1] == 0u8 and data[2] == 11u8 and data[3] == 22u8`
   - Expected: source contains `[boot-fs] NVFS positioned I/O: cursor-independent round-trip`
   - Expected: source contains `[boot-fs] NVFS positioned I/O: FAILED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exercises byte-exact positioned I/O through canonical SOSIX dispatch")
val source = _source("src/os/kernel/boot/boot_fs.spl")
expect(source.contains("sosix_positioned_acceptance_round_trip_v1(")).to_equal(true)
expect(source.contains("SosixPositionedBackendKindV1.Nvfs")).to_equal(true)
expect(source.contains("g_vfs_nvfs_write_at(")).to_equal(false)
expect(source.contains("g_vfs_nvfs_read_at(")).to_equal(false)
expect(source.contains("data[0] == 0u8 and data[1] == 0u8 and data[2] == 11u8 and data[3] == 22u8")).to_equal(true)
expect(source.contains("[boot-fs] NVFS positioned I/O: cursor-independent round-trip")).to_equal(true)
expect(source.contains("[boot-fs] NVFS positioned I/O: FAILED")).to_equal(true)
```

</details>

#### propagates both boot oracles before emitting the mount success marker

- propagates both boot oracles before emitting the mount success marker
   - Expected: source contains `if not _nvfs_root_persistence_check():\n        return false`
   - Expected: source contains `if not _nvfs_root_positioned_io_check():\n        return false`
   - Expected: source does not contain `val _ = _nvfs_root_persistence_check()`
   - Expected: source does not contain `val _ = _nvfs_root_positioned_io_check()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("propagates both boot oracles before emitting the mount success marker")
val source = _source("src/os/kernel/boot/boot_fs.spl")
expect(source.contains("if not _nvfs_root_persistence_check():\n        return false")).to_equal(true)
expect(source.contains("if not _nvfs_root_positioned_io_check():\n        return false")).to_equal(true)
expect(source.contains("val _ = _nvfs_root_persistence_check()")).to_equal(false)
expect(source.contains("val _ = _nvfs_root_positioned_io_check()")).to_equal(false)
```

</details>

#### requires an admitted runtime and emits an adjacent closed image manifest

- requires an admitted runtime and emits an adjacent closed image manifest
   - Expected: source contains `SIMPLE_RUNTIME_PATH`
   - Expected: source contains `SIMPLE_RUNTIME_RECEIPT`
   - Expected: source contains `check-sosix-qemu-runtime-admission.shs`
   - Expected: source contains `provider=nvfs-dbfs-backed-v1`
   - Expected: source contains `image_sha256=%s`
   - Expected: source contains `runtime_sha256=%s`
   - Expected: source does not contain `exec bin/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires an admitted runtime and emits an adjacent closed image manifest")
val source = _source("scripts/os/mkfs-nvfs.shs")
expect(source.contains("SIMPLE_RUNTIME_PATH")).to_equal(true)
expect(source.contains("SIMPLE_RUNTIME_RECEIPT")).to_equal(true)
expect(source.contains("check-sosix-qemu-runtime-admission.shs")).to_equal(true)
expect(source.contains("provider=nvfs-dbfs-backed-v1")).to_equal(true)
expect(source.contains("image_sha256=%s")).to_equal(true)
expect(source.contains("runtime_sha256=%s")).to_equal(true)
expect(source.contains("exec bin/simple")).to_equal(false)
```

</details>

#### builds a dedicated entry that reaches the production boot sequence

- builds a dedicated entry that reaches the production boot sequence
   - Expected: entry contains `boot_fs_sequence()`
   - Expected: entry contains `NVFS_POSITIONED_QEMU_PASSED`
   - Expected: builder contains `check-post-bootstrap-stage4-sspec.shs`
   - Expected: builder contains `check-sosix-qemu-runtime-admission.shs`
   - Expected: builder contains `entry=examples/09_embedded/simple_os/arch/x86_64/nvfs_positioned_entry.spl`
   - Expected: builder contains `compiler_path=%s`
   - Expected: builder contains `source_revision=%s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds a dedicated entry that reaches the production boot sequence")
val entry = _source(
    "examples/09_embedded/simple_os/arch/x86_64/nvfs_positioned_entry.spl")
val builder = _source(
    "scripts/check/build-simpleos-nvfs-positioned-qemu.shs")
expect(entry.contains("boot_fs_sequence()")).to_equal(true)
expect(entry.contains("NVFS_POSITIONED_QEMU_PASSED")).to_equal(true)
expect(builder.contains("check-post-bootstrap-stage4-sspec.shs")).to_equal(true)
expect(builder.contains("check-sosix-qemu-runtime-admission.shs")).to_equal(true)
expect(builder.contains("entry=examples/09_embedded/simple_os/arch/x86_64/nvfs_positioned_entry.spl")).to_equal(true)
expect(builder.contains("compiler_path=%s")).to_equal(true)
expect(builder.contains("source_revision=%s")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS NVFS DBFS-backed production root source contract.
- SimpleOS NVFS DBFS-backed production root source contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f11ae35357f994761a6e055a62cfb6aa73c3115899128f85dca7195a935b5358`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f11ae35357f994761a6e055a62cfb6aa73c3115899128f85dca7195a935b5358`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f11ae35357f994761a6e055a62cfb6aa73c3115899128f85dca7195a935b5358`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mounts the canonical NVFS driver through the MountTable root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails over from a checksum-corrupt primary replica' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/nvfs_dbfs_backed_root_source_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the DBFS-backed provider and exact persistence boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
