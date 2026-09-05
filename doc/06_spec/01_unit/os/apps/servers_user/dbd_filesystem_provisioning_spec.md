# Filesystem-launched DBD provisioning and DBFS/VFS admission

> The combined server payload is only a transport adapter. It must provision the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Filesystem-launched DBD provisioning and DBFS/VFS admission

The combined server payload is only a transport adapter. It must provision the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The combined server payload is only a transport adapter. It must provision the
canonical DBD owner from owned boot files, destroy all source buffers, and
admit persistence only from a DBFS VFS capability that proves durable sync and
transactional namespace replacement.

## Scenarios

### filesystem DBD boot secret ownership

#### calls the canonical provision_service and wipes every source buffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls the canonical provision_service and wipes every source buffer
   - Expected: source does not contain `DbServerCapsule`
   - Expected: source does not contain `--credential=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("calls the canonical provision_service and wipes every source buffer")
val source = file_read("src/os/apps/servers_user/main.spl")
expect(source).to_contain("server.provision_service(")
expect(source).to_contain("read_file_bytes_direct_owned(DB_CREDENTIAL_PATH")
expect(source).to_contain("read_file_bytes_direct_owned(DB_CERTIFICATE_PATH")
expect(source).to_contain("read_file_bytes_direct_owned(DB_PRIVATE_KEY_PATH")
expect(source).to_contain("secure_zero_u8_slots(credential)")
expect(source).to_contain("secure_zero_u8_slots(cert)")
expect(source).to_contain("secure_zero_u8_slots(key)")
expect(source.contains("DbServerCapsule")).to_equal(false)
expect(source.contains("--credential=")).to_equal(false)
```

</details>

### filesystem DBD DBFS VFS capability

#### fails closed unless mount identity sync and transaction facts agree

- fails closed unless mount identity sync and transaction facts agree
   - Expected: projection does not contain `FILE_ATOMIC_DBFS_ROOT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed unless mount identity sync and transaction facts agree")
val adapter = file_read("src/os/apps/dbd/dbd_dbfs_adapter.spl")
expect(adapter).to_contain("if not dbfs_root:")
expect(adapter).to_contain("if not durable_sync:")
expect(adapter).to_contain("if not transactional_replace:")
expect(adapter).to_contain("dbfs-vfs-transactional-replace-unavailable")
val projection = file_read("src/os/apps/servers_user/database_persistence_adapter.spl")
expect(projection).to_contain("dbfs_vfs_mount_capability_v1()")
expect(projection.contains("FILE_ATOMIC_DBFS_ROOT")).to_equal(false)
```

</details>

#### admits the complete least-authority capability without a driver copy

- admits the complete least-authority capability without a driver copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits the complete least-authority capability without a driver copy")
val adapter = file_read("src/os/apps/dbd/dbd_dbfs_adapter.spl")
expect(adapter).to_contain("state: DbdDbfsAdapterState.MountedDurable")
expect(adapter).to_contain("driver: nil")
expect(adapter).to_contain("filesystem_vfs: true")
```

</details>

#### publishes readiness only from an actually mounted durable DBFS driver

- publishes readiness only from an actually mounted durable DBFS driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("publishes readiness only from an actually mounted durable DBFS driver")
val mount = file_read("src/os/services/vfs/vfs_init.spl")
val owner = file_read("src/os/services/vfs/dbfs_mount_capability.spl")
expect(mount).to_contain("case DbFs(dbfs):")
expect(mount).to_contain("dbfs.durability_serialization_ready()")
expect(mount).to_contain("dbfs_vfs_mount_capability_clear_v1()")
expect(owner).to_contain("DbfsMountedRecoveryCompleteDurableTransactionalReplace")
```

</details>

#### shares one contract type while keeping wire encode and decode separated

- shares one contract type while keeping wire encode and decode separated


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("shares one contract type while keeping wire encode and decode separated")
val contract = file_read("src/lib/common/contracts/os/dbfs_vfs_mount_capability_v1.spl")
val owner = file_read("src/os/services/vfs/dbfs_mount_capability.spl")
val userlib = file_read("src/os/userlib/fs.spl")
expect(contract).to_contain("pub enum DbfsVfsMountCapabilityV1")
expect(owner).to_contain("pub use std.common.contracts.os.dbfs_vfs_mount_capability_v1")
expect(owner).to_contain("dbfs_vfs_mount_capability_code_v1()")
expect(userlib).to_contain("pub use std.common.contracts.os.dbfs_vfs_mount_capability_v1")
expect(userlib).to_contain("match syscall(79, 0, 0, 0, 0, 0)")
```

</details>

### filesystem DBD authenticated durable transaction path

#### routes TLS AUTH and persistent write/read through the canonical owner

- routes TLS AUTH and persistent write/read through the canonical owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes TLS AUTH and persistent write/read through the canonical owner")
val source = file_read("src/os/apps/servers_user/main.spl")
val dbd = file_read("src/os/apps/dbd/dbd.spl")
expect(source).to_contain("db_server.replay_log()")
expect(source).to_contain("db_server.bind_listener")
expect(source).to_contain("db_server.accept_and_handle_once()")
expect(dbd).to_contain("self.dbfs_adapter.commit_and_sync(")
expect(dbd).to_contain("return self.engine.dispatch(args)")
expect(dbd).to_contain("self.engine.replay_journal(self.log_text)")
```

</details>

#### uses exclusive staging namespace sync and whole-owner close

- uses exclusive staging namespace sync and whole-owner close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses exclusive staging namespace sync and whole-owner close")
val source = file_read("src/os/apps/servers_user/main.spl")
val dbd = file_read("src/os/apps/dbd/dbd.spl")
val adapter = file_read("src/os/apps/dbd/dbd_dbfs_adapter.spl")
expect(adapter).to_contain("self.generation.to_text()")
expect(adapter).to_contain("file_open_direct(temp_path, 0xC1u32)")
expect(adapter).to_contain("file_sync_direct(directory.unwrap())")
expect(dbd).to_contain("pub me close_service() -> bool:")
expect(dbd).to_contain("self.provisioning.close()")
expect(source).to_contain("db_server.close_service()")
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `467ef1c1bbf12588b85b4bfd6ca0cef889577bfdff51d7d169b4955cc3479232`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `467ef1c1bbf12588b85b4bfd6ca0cef889577bfdff51d7d169b4955cc3479232`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `467ef1c1bbf12588b85b4bfd6ca0cef889577bfdff51d7d169b4955cc3479232`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl
mirror: doc/06_spec/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls the canonical provision_service and wipes every source buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed unless mount identity sync and transaction facts agree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the complete least-authority capability without a driver copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
