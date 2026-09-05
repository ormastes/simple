# Simpleos Arm64 Server Qemu Gate Contract Specification

> Tests covering ARM64 SimpleOS server QEMU gate contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Arm64 Server Qemu Gate Contract Specification

## Scenarios

### ARM64 SimpleOS server QEMU gate contract

#### should bind compiler admission to the complete current worktree manifest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should bind compiler admission to the complete current worktree manifest
   - Expected: gate does not contain `build/bootstrap/stage2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should bind compiler admission to the complete current worktree manifest")
val gate = file_read("scripts/check/check-simpleos-arm64-servers-qemu.shs")
expect(gate).to_contain("simpleos-arm64-current-source-compiler-admission-v1")
expect(gate).to_contain("source_manifest_sha256")
expect(gate).to_contain("source_manifest_roots")
expect(gate).to_contain("qemu_admission_source_snapshot")
expect(gate).to_contain("sh scripts/os/build_arm64_servers_payload.shs")
expect(gate.contains("build/bootstrap/stage2")).to_equal(false)
```

</details>

#### should reject every strong undefined symbol and review every weak one

- should reject every strong undefined symbol and review every weak one


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject every strong undefined symbol and review every weak one")
val gate = file_read("scripts/check/check-simpleos-arm64-servers-qemu.shs")
expect(gate).to_contain("UNDEFINED_STRONG")
expect(gate).to_contain("UNDEFINED_WEAK")
expect(gate).to_contain("simpleos_arm64_servers_weak_undefined_allowlist.sdn")
expect(gate).to_contain("rt_simpleos_file_atomic_caps")
expect(gate).to_contain("rt_process_is_running")
```

</details>

#### should destroy every credential-bearing image after both normal and crash boots

- should destroy every credential-bearing image after both normal and crash boots
   - Expected: server does not contain `extern fn rt_array_data_ptr`
   - Expected: server does not contain `extern fn rt_volatile_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should destroy every credential-bearing image after both normal and crash boots")
val gate = file_read("scripts/check/check-simpleos-arm64-servers-qemu.shs")
val server = file_read("src/os/apps/servers_user/main.spl")
expect(gate).to_contain("image_contains_credential=true")
expect(gate).to_contain("credential_image_sensitive=true")
expect(gate).to_contain("credential_image_destroyed_after_run=true")
expect(gate).to_contain("target_credential_zeroization=verified")
expect(gate).to_contain("simpleos_server_zeroization_canonical")
expect(gate).to_contain("target_credential_zeroization_boot1_sha256")
expect(gate).to_contain("target_credential_zeroization_boot2_sha256")
expect(server).to_contain("secure_zero_u8_slots")
expect(server).to_contain("read_file_bytes_direct_owned")
expect(server).to_contain("hash_workspace={hash_status}")
expect(server.contains("extern fn rt_array_data_ptr")).to_equal(false)
expect(server.contains("extern fn rt_volatile_")).to_equal(false)
expect(gate).to_contain("retained artifact contains the database credential")
expect(gate).to_contain("for sensitive_image in $SENSITIVE_IMAGES")
```

</details>

#### should exercise every frozen FAT32 crash seam and require replay state

- should exercise every frozen FAT32 crash seam and require replay state


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should exercise every frozen FAT32 crash seam and require replay state")
val gate = file_read("scripts/check/check-simpleos-arm64-servers-qemu.shs")
val entry = file_read("examples/09_embedded/simple_os/arch/arm64/servers_entry.spl")
expect(gate).to_contain("crash_replay_seam_count=13")
expect(gate).to_contain("fat-copies-reread")
expect(gate).to_contain("done-header-flush")
expect(gate).to_contain("generation=[0-9]+ state=3 recovered=(true|false)")
expect(gate).to_contain("pre-existing committed DB state lost")
expect(gate).to_contain("acknowledged commit was not public after replay")
expect(entry).to_contain("fat32_replace_fault_injection_set")
expect(entry).to_contain("[far-crash] seam=")
expect(entry).to_contain("[far-replay] generation=")
```

</details>

#### should bind readiness to the filesystem read scheduler spawn and user entry

- should bind readiness to the filesystem read scheduler spawn and user entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should bind readiness to the filesystem read scheduler spawn and user entry")
val gate = file_read("scripts/check/check-simpleos-arm64-servers-qemu.shs")
expect(gate).to_contain("require_filesystem_launch_markers")
expect(gate).to_contain("executable read=ok path=/SERVERS.ELF bytes=")
expect(gate).to_contain("[fs-exec] spawn:pid=")
expect(gate).to_contain("executable=/SERVERS.ELF launch=ok")
expect(gate).to_contain("filesystem_launch_verified=true")
expect(gate).to_contain("host_fallback_used=false")
expect(gate).to_contain("receipt signature self-verification failed")
expect(gate).to_contain("producer_sha256=")
expect(gate).to_contain("boot1_serial_path=")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 SimpleOS server QEMU gate contract.
- ARM64 SimpleOS server QEMU gate contract

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c43cbb4d0869f35ecf0af4ece2356120c678fd1e622467cb5c7dff26c844a7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c43cbb4d0869f35ecf0af4ece2356120c678fd1e622467cb5c7dff26c844a7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c43cbb4d0869f35ecf0af4ece2356120c678fd1e622467cb5c7dff26c844a7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl
mirror: doc/06_spec/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:16:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind compiler admission to the complete current worktree manifest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind compiler admission to the complete current worktree manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every strong undefined symbol and review every weak one' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject every strong undefined symbol and review every weak one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should destroy every credential-bearing image after both normal and crash boots' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should destroy every credential-bearing image after both normal and crash boots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise every frozen FAT32 crash seam and require replay state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind readiness to the filesystem read scheduler spawn and user entry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
