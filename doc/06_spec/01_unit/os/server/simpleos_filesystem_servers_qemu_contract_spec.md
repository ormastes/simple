# Simpleos Filesystem Servers Qemu Contract Specification

> Tests covering multi-architecture filesystem server QEMU admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Filesystem Servers Qemu Contract Specification

## Scenarios

### multi-architecture filesystem server QEMU admission

#### rejects kernel-resident evidence and requires all three architectures

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects kernel-resident evidence and requires all three architectures
   - Expected: umbrella does not contain `env SKIP_KERNEL=1 SKIP_STAGE=1 sh scripts/check/check-simpleos-servers-qemu.shs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects kernel-resident evidence and requires all three architectures")
val gate = file_read("scripts/check/check-simpleos-filesystem-servers-qemu.shs")
val umbrella = file_read("scripts/check/check-simpleos-nonbootstrap-acceptance.shs")
expect(gate).to_contain("filesystem_launch_verified")
expect(gate).to_contain("filesystem_launch_path")
expect(gate).to_contain("host_fallback_used")
expect(gate).to_contain("SIMPLEOS_X86_64_FS_SERVERS_RECEIPT")
expect(gate).to_contain("SIMPLEOS_ARM64_FS_SERVERS_RECEIPT")
expect(gate).to_contain("SIMPLEOS_RISCV64_FS_SERVERS_RECEIPT")
expect(gate).to_contain("openssl dgst -sha256 -verify")
expect(gate).to_contain("SIMPLEOS_FS_SERVERS_TRUST_KEY")
expect(umbrella).to_contain("check-simpleos-filesystem-servers-qemu.shs")
expect(umbrella.contains("env SKIP_KERNEL=1 SKIP_STAGE=1 sh scripts/check/check-simpleos-servers-qemu.shs")).to_equal(false)
```

</details>

#### requires HTTP filesystem bytes DB commit reboot and evidence hashes

- requires HTTP filesystem bytes DB commit reboot and evidence hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires HTTP filesystem bytes DB commit reboot and evidence hashes")
val gate = file_read("scripts/check/check-simpleos-filesystem-servers-qemu.shs")
expect(gate).to_contain("http_file_verified")
expect(gate).to_contain("db_commit_verified")
expect(gate).to_contain("db_boot2_read_verified")
expect(gate).to_contain("credential_image_destroyed_after_run")
expect(gate).to_contain("source_manifest_sha256")
expect(gate).to_contain("boot1_serial_sha256")
expect(gate).to_contain("boot2_serial_sha256")
expect(gate).to_contain("require_bound_file")
expect(gate).to_contain("zero-sha256-forbidden")
expect(gate).to_contain("selftest-accepted-mutated-signed-receipt")
expect(gate).to_contain("selftest-accepted-mutated-artifact")
expect(gate).to_contain("selftest-accepted-forged-trust-key")
expect(gate).to_contain("selftest-accepted-aliased-evidence-files")
expect(gate).to_contain("selftest-accepted-unverified-target-credential-zeroization")
expect(gate).to_contain("selftest-accepted-target-zeroization-residual")
expect(gate).to_contain("selftest-accepted-unzeroized-hash-workspace")
expect(gate).to_contain("require_eq target_credential_zeroization verified")
expect(gate).to_contain("require_target_zeroization")
expect(gate).to_contain("target_credential_zeroization_boot1_sha256")
expect(gate).to_contain("simpleos-filesystem-server-receipt.env")
expect(gate).to_contain("source_manifest_path")
expect(gate).to_contain("image_staged_path")
```

</details>

#### wires an architecture-matched server payload producer for every 64-bit QEMU lane

- wires an architecture-matched server payload producer for every 64-bit QEMU lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires an architecture-matched server payload producer for every 64-bit QEMU lane")
val producer = file_read("scripts/os/build_simpleos_servers_payload.shs")
val disk = file_read("scripts/os/make_os_disk.shs")
val server = file_read("src/os/apps/servers_user/main.spl")
expect(producer).to_contain("x86_64-unknown-simpleos")
expect(producer).to_contain("aarch64-unknown-simpleos")
expect(producer).to_contain("riscv64-unknown-simpleos")
expect(producer).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
expect(producer).to_contain("server payload retained undefined strong symbols")
expect(disk).to_contain("build_simpleos_servers_payload.shs")
expect(disk).to_contain("validate_elf_payload \"$SIMPLEOS_SERVERS_BINARY\" 62 Servers")
expect(disk).to_contain("validate_elf_payload \"$SIMPLEOS_SERVERS_BINARY\" 243 Servers")
expect(server).to_contain("[simpleos-servers-user] executable=/SERVERS.ELF launch=ok")
```

</details>

#### has fail-closed x86_64 and RV64 filesystem server boot entries

- has fail-closed x86_64 and RV64 filesystem server boot entries
   - Expected: x86 does not contain `x86_64_fs_exec_spawn_scheduler_owned`
   - Expected: rv does not contain `riscv64_fs_exec_spawn_capture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has fail-closed x86_64 and RV64 filesystem server boot entries")
val x86 = file_read("examples/09_embedded/simple_os/arch/x86_64/filesystem_servers_entry.spl")
val rv = file_read("examples/09_embedded/simple_os/arch/riscv64/servers_entry.spl")
expect(x86).to_contain("x86_64_authenticated_media_execute_path_v1")
expect(x86.contains("x86_64_fs_exec_spawn_scheduler_owned")).to_equal(false)
expect(x86).to_contain("/SERVERS.ELF")
expect(x86).to_contain("rt_debug_exit_failure")
expect(rv).to_contain("riscv64_authenticated_media_execute_server_v1")
expect(rv.contains("riscv64_fs_exec_spawn_capture")).to_equal(false)
expect(rv).to_contain("vfs_boot_init_riscv64_virtio_fat32")
expect(rv).to_contain("rt_qemu_exit_failure")
```

</details>

#### selects authenticated server entries and sidecars in the rebuild owner

- selects authenticated server entries and sidecars in the rebuild owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects authenticated server entries and sidecars in the rebuild owner")
val rebuild = file_read("scripts/check/rebuild-sosix-qemu-media.shs")
val disk = file_read("scripts/os/make_os_disk.c")
expect(rebuild).to_contain("SOSIX_QEMU_SERVERS")
expect(rebuild).to_contain("filesystem_servers_entry.spl")
expect(rebuild).to_contain("riscv64/servers_entry.spl")
expect(rebuild).to_contain("sign_simpleos_servers_payload.shs")
expect(rebuild).to_contain("SIMPLEOS_SERVERS_MANIFEST")
expect(disk).to_contain("SERVER  MAN")
expect(disk).to_contain("SERVER  SIG")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering multi-architecture filesystem server QEMU admission.
- multi-architecture filesystem server QEMU admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9144b450609abce76dcd4dc23a095071eca95a0008bebdf350abaefcd326155c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9144b450609abce76dcd4dc23a095071eca95a0008bebdf350abaefcd326155c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9144b450609abce76dcd4dc23a095071eca95a0008bebdf350abaefcd326155c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.spl
mirror: doc/06_spec/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects kernel-resident evidence and requires all three architectures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires HTTP filesystem bytes DB commit reboot and evidence hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_filesystem_servers_qemu_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires an architecture-matched server payload producer for every 64-bit QEMU lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
