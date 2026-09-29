# Database Persistence Adapter Specification

> Tests covering SimpleOS database persistence adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Persistence Adapter Specification

## Scenarios

### SimpleOS database persistence adapter

#### admits linked runtime and RecoverableReplaceV1 capabilities together

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits linked runtime and RecoverableReplaceV1 capabilities together
   - Expected: simpleos_database_persistence_ready(caps) is true
   - Expected: simpleos_database_persistence_blocker(caps) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits linked runtime and RecoverableReplaceV1 capabilities together")
val caps = simpleos_database_persistence_caps_for(31, _structural_replace_caps())
expect(simpleos_database_persistence_ready(caps)).to_equal(true)
expect(simpleos_database_persistence_blocker(caps)).to_equal("")
```

</details>

#### requires every canonical atomic-save capability

- requires every canonical atomic-save capability
   - Expected: simpleos_database_persistence_ready(ready) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires every canonical atomic-save capability")
val ready = SimpleOsDatabasePersistenceCaps(
    exclusive_create: true,
    bounded_lock_wait: true,
    private_temp_write: true,
    durable_file_sync: true,
    runtime_rename_owner_linked: true,
    atomic_replace_rename: true,
    crash_recovery: true
)
expect(simpleos_database_persistence_ready(ready)).to_equal(true)
```

</details>

#### does not accept non-atomic replacement as durable

- does not accept non-atomic replacement as durable
   - Expected: simpleos_database_persistence_ready(non_atomic) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not accept non-atomic replacement as durable")
val non_atomic = SimpleOsDatabasePersistenceCaps(
    exclusive_create: true,
    bounded_lock_wait: true,
    private_temp_write: true,
    durable_file_sync: true,
    runtime_rename_owner_linked: true,
    atomic_replace_rename: false,
    crash_recovery: true
)
expect(simpleos_database_persistence_ready(non_atomic)).to_equal(false)
expect(simpleos_database_persistence_blocker(non_atomic)).to_equal(
    "atomic-replace-rename-unavailable")
```

</details>

#### distinguishes an unlinked runtime symbol from FAT32 replace semantics

- distinguishes an unlinked runtime symbol from FAT32 replace semantics
   - Expected: simpleos_database_persistence_rename_blocker(caps) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("distinguishes an unlinked runtime symbol from FAT32 replace semantics")
val caps = simpleos_database_persistence_caps_for(31, _structural_replace_caps())
expect(simpleos_database_persistence_rename_blocker(caps)).to_equal("")

val unlinked = SimpleOsDatabasePersistenceCaps(
    exclusive_create: true,
    bounded_lock_wait: true,
    private_temp_write: true,
    durable_file_sync: true,
    runtime_rename_owner_linked: false,
    atomic_replace_rename: false,
    crash_recovery: false
)
expect(simpleos_database_persistence_rename_blocker(unlinked)).to_equal(
    "runtime-rename-owner-unlinked")
```

</details>

#### keeps unpublished mounted truth distinct from a pure structural projection

- keeps unpublished mounted truth distinct from a pure structural projection
   - Expected: simpleos_database_persistence_ready(mounted) is false
   - Expected: simpleos_database_persistence_ready(structural) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps unpublished mounted truth distinct from a pure structural projection")
val mounted = simpleos_database_persistence_caps_for(31, fat32_atomic_replace_caps())
expect(simpleos_database_persistence_ready(mounted)).to_equal(false)
expect(simpleos_database_persistence_blocker(mounted)).to_equal(
    "durable-file-sync-unavailable")

val structural = simpleos_database_persistence_caps_for(31, _structural_replace_caps())
expect(simpleos_database_persistence_ready(structural)).to_equal(true)
```

</details>

#### validates the exact provisioner descriptor and rejects malformed fields

- validates the exact provisioner descriptor and rejects malformed fields
   - Expected: descriptor.len() equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("validates the exact provisioner descriptor and rejects malformed fields")
val descriptor = fat32_atomic_replace_provisioned_descriptor()
expect(descriptor.len()).to_equal(512)
expect(fat32_atomic_replace_caps_probe(
    descriptor, 524288u32, 32u32, true, true).level).to_equal(
        AtomicReplaceRecoveryLevel.RecoverableReplaceV1)

var corrupt_crc = descriptor
corrupt_crc[20] = corrupt_crc[20] ^ 1u8
expect(fat32_atomic_replace_caps_probe(
    corrupt_crc, 524288u32, 32u32, true, true).level).to_equal(
        AtomicReplaceRecoveryLevel.Unsupported)
expect(fat32_atomic_replace_caps_probe(
    _descriptor_with_field(8, 15u32), 524288u32, 32u32,
    true, true).level).to_equal(AtomicReplaceRecoveryLevel.Unsupported)
expect(fat32_atomic_replace_caps_probe(
    _descriptor_with_field(12, 15u32), 524288u32, 32u32,
    true, true).level).to_equal(AtomicReplaceRecoveryLevel.Unsupported)
expect(fat32_atomic_replace_caps_probe(
    _descriptor_with_field(16, 4096u32), 524288u32, 32u32,
    true, true).level).to_equal(AtomicReplaceRecoveryLevel.Unsupported)
```

</details>

#### maps the exact database route through sync then RecoverableReplaceV1

- maps the exact database route through sync then RecoverableReplaceV1


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps the exact database route through sync then RecoverableReplaceV1")
val atomic = file_read("src/lib/nogc_sync_mut/database/atomic.spl")
expect(atomic).to_contain("if path == \"/SERVER.DB\"")
expect(atomic).to_contain("return \"/SERVER.TMP\"")
expect(atomic).to_contain("if not rt_file_sync(temp_path)")

val runtime = file_read("src/runtime/simple_core/core_fs.spl")
expect(runtime).to_contain("pub fn rt_file_create_excl")
expect(runtime).to_contain("val fd = open(path_ptr, 193)")
expect(runtime).to_contain("pub fn rt_file_sync")
expect(runtime).to_contain("val fd = open(path_ptr, 2)")
val runtime_owner = runtime.split("pub fn rt_file_rename")[1]
expect(runtime_owner).to_contain("val result = rename(src, dst)")

val libc = file_read("src/os/libc/simpleos_fs.c")
val libc_owner = libc.split("int rename(")[1]
expect(libc_owner).to_contain("simpleos_syscall(44")

val syscall = file_read("src/os/kernel/ipc/syscall_file.spl")
val rename_owner = syscall.split("fn _handle_file_rename")[1]
expect(rename_owner).to_contain("fs.atomic_replace_at(dev, old_resolved, new_resolved)")
expect(rename_owner).to_contain("there is no delete+rename or ordinary-rename fallback")
```

</details>

#### uses scheduler-owned task liveness without turning signal zero into termination

- uses scheduler-owned task liveness without turning signal zero into termination
   - Expected: atomic does not contain `rt_process_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses scheduler-owned task liveness without turning signal zero into termination")
val atomic = file_read("src/lib/nogc_sync_mut/database/atomic.spl")
expect(atomic).to_contain("rt_process_is_running(pid)")
expect(atomic.contains("rt_process_run")).to_equal(false)

val signal = file_read("src/os/libc/simpleos_signal.c")
expect(signal).to_contain("if (sig == 0)")
expect(signal).to_contain("simpleos_syscall(6, (int64_t)pid, 0, 0, 0, 0)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/servers_user/database_persistence_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS database persistence adapter.
- SimpleOS database persistence adapter

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b4ef0ed23f1991c31d18389f8bfa250820d1dfc02f832539ddb260460dfc4f3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4ef0ed23f1991c31d18389f8bfa250820d1dfc02f832539ddb260460dfc4f3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4ef0ed23f1991c31d18389f8bfa250820d1dfc02f832539ddb260460dfc4f3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/apps/servers_user/database_persistence_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/apps/servers_user/database_persistence_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/servers_user/database_persistence_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/servers_user/database_persistence_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/servers_user/database_persistence_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/apps/servers_user/database_persistence_adapter_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits linked runtime and RecoverableReplaceV1 capabilities together' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/servers_user/database_persistence_adapter_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires every canonical atomic-save capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/servers_user/database_persistence_adapter_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not accept non-atomic replacement as durable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
