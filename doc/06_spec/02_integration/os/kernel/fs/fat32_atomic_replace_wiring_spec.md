# fat32_atomic_replace_wiring_spec

> Integration wiring checks for FAT32 RecoverableReplaceV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fat32_atomic_replace_wiring_spec

Integration wiring checks for FAT32 RecoverableReplaceV1.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Integration wiring checks for FAT32 RecoverableReplaceV1.

Live crash/reboot behavior belongs to the red system runner; these checks keep
the provisioner, mount gate, syscall adapter, and ordinary rename boundary
connected in source builds.

## Scenarios

### FAT32 atomic-replace integration wiring

#### should provision exactly sixteen reserved journal sectors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should provision exactly sixteen reserved journal sectors
- Inspect the native FAT32 image provisioner


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should provision exactly sixteen reserved journal sectors")
step("Inspect the native FAT32 image provisioner")
val source = _source("scripts/os/make_os_disk.c")
expect(source).to_contain("SIMPLEOS_REPLACE_DESCRIPTOR_SECTOR = 2")
expect(source).to_contain("SIMPLEOS_REPLACE_JOURNAL_START = 16")
expect(source).to_contain("SIMPLEOS_REPLACE_JOURNAL_SECTORS = 16")
expect(source).to_contain("write_atomic_replace_descriptor();")
```

</details>

#### should recover before root cache load and mount publication

- should recover before root cache load and mount publication
- Inspect the FAT32 mount and boot publication order
   - Expected: fs.index_of("fat32_atomic_replace_recover_device(") < fs.index_of("# Stash root dir cluster sectors for readdir") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should recover before root cache load and mount publication")
step("Inspect the FAT32 mount and boot publication order")
val fs = _fat32_source()
val boot = _source("src/os/kernel/boot/boot_fs_mount.spl")
expect(fs).to_contain("fat32_atomic_replace_recover_device(")
expect(fs).to_contain("# Stash root dir cluster sectors for readdir")
expect(boot).to_contain("fat32_mount_publish(fs, dev)")
expect(fs.index_of("fat32_atomic_replace_recover_device(") < fs.index_of("# Stash root dir cluster sectors for readdir")).to_equal(true)
```

</details>

#### should route only allowlisted DB destinations to recoverable replace

- should route only allowlisted DB destinations to recoverable replace
- Inspect syscall dispatch without changing ordinary rename


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should route only allowlisted DB destinations to recoverable replace")
step("Inspect syscall dispatch without changing ordinary rename")
val syscall = _source("src/os/kernel/ipc/syscall_file.spl")
val fs = _fat32_source()
expect(syscall).to_contain("if fat32_atomic_replace_path_allowed(new_resolved):")
expect(syscall).to_contain("fs.atomic_replace_at(dev, old_resolved, new_resolved)")
expect(syscall).to_contain("fs.rename_at(dev, old_resolved, new_resolved)")
expect(fs).to_contain("The two directory-entry writes are NOT atomic as a pair")
```

</details>

#### should persist payload before header and cursor before FAT free

- should persist payload before header and cursor before FAT free
- Inspect the device-backed journal owner ordering
   - Expected: owner.index_of("dev.write_sector(bank_lba + 1u64") < owner.index_of("dev.write_sector(bank_lba, header)") is true
   - Expected: owner.index_of("_publish_raw_bank(dev, js, bank, header, payload)?") < owner.index_of("_free_fat_cluster(dev") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should persist payload before header and cursor before FAT free")
step("Inspect the device-backed journal owner ordering")
val owner = _source("src/os/kernel/fs/fat32_atomic_replace.spl")
expect(owner.index_of("dev.write_sector(bank_lba + 1u64") < owner.index_of("dev.write_sector(bank_lba, header)")).to_equal(true)
expect(owner.index_of("_publish_raw_bank(dev, js, bank, header, payload)?") < owner.index_of("_free_fat_cluster(dev")).to_equal(true)
expect(owner).to_contain("3u32, generation, 0u32, 0u32")
```

</details>

#### should publish database durability only from recovered filesystem caps

- should publish database durability only from recovered filesystem caps
- Inspect the server database capability adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should publish database durability only from recovered filesystem caps")
step("Inspect the server database capability adapter")
val adapter = _source("src/os/apps/servers_user/database_persistence_adapter.spl")
expect(adapter).to_contain("replace.mount_recovery_complete")
expect(adapter).to_contain("atomic_replace_rename: recoverable")
expect(adapter).to_contain("crash_recovery: recoverable")
```

</details>

#### should validate and repair every FAT copy before cursor advancement

- should validate and repair every FAT copy before cursor advancement
- Inspect all-copy recovery and post-flush reread gates
   - Expected: owner.index_of("while verify_copy < fat_count") < owner.index_of("current = next") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should validate and repair every FAT copy before cursor advancement")
step("Inspect all-copy recovery and post-flush reread gates")
val owner = _source("src/os/kernel/fs/fat32_atomic_replace.spl")
expect(owner).to_contain("while copy < fat_count")
expect(owner).to_contain("_fat_reclaim_observation")
expect(owner).to_contain("while verify_copy < fat_count")
expect(owner).to_contain("FatCopiesReread")
expect(owner.index_of("while verify_copy < fat_count") < owner.index_of("current = next")).to_equal(true)
```

</details>

#### should restrict replay images to exact root-directory sectors

- should restrict replay images to exact root-directory sectors
- Inspect replay LBA admission and exact database route


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should restrict replay images to exact root-directory sectors")
step("Inspect replay LBA admission and exact database route")
val owner = _source("src/os/kernel/fs/fat32_atomic_replace.spl")
expect(owner).to_contain("fat32_replace_image_lba_allowed")
expect(owner).to_contain("source_tmp == \"/SERVER.TMP\" and destination == \"/SERVER.DB\"")
expect(owner).to_contain("start > reserved_sectors - count")
expect(owner).to_contain("start > total_sectors - count")
```

</details>

#### should validate bounded acyclic disjoint chains before COMMITTED

- should validate bounded acyclic disjoint chains before COMMITTED
- Inspect consensus chain validation and full alias traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should validate bounded acyclic disjoint chains before COMMITTED")
step("Inspect consensus chain validation and full alias traversal")
val owner = _source("src/os/kernel/fs/fat32_atomic_replace.spl")
val fs = _fat32_source()
expect(owner).to_contain("fat32_replace_validate_disjoint_chains")
expect(owner).to_contain("_fat_consensus_value")
expect(fs).to_contain("val alias_chain = alias_chain_r.unwrap()")
expect(fs).to_contain("while ai < alias_chain.len()")
```

</details>

#### should serialize all namespace mutation and revalidate after lock

- should serialize all namespace mutation and revalidate after lock
- Inspect the shared filesystem mutation owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should serialize all namespace mutation and revalidate after lock")
step("Inspect the shared filesystem mutation owner")
val fs = _fat32_source()
expect(fs).to_contain("mutation_active: bool")
expect(fs).to_contain("fn _mutation_enter")
expect(fs).to_contain("fn _mutation_leave")
expect(fs).to_contain("fn _atomic_replace_at_locked")
expect(fs).to_contain("source.dirent_sector != expected_source_lba")
expect(fs).to_contain("dest.dirent_sector != expected_destination_lba")
expect(fs).to_contain("val root_scan_data = root_scan_r.unwrap()")
```

</details>

#### should reserve only safe fixed V1 sectors and keep probing non-publishing

- should reserve only safe fixed V1 sectors and keep probing non-publishing
- Inspect descriptor and capability probe boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should reserve only safe fixed V1 sectors and keep probing non-publishing")
step("Inspect descriptor and capability probe boundaries")
val owner = _source("src/os/kernel/fs/fat32_atomic_replace.spl")
expect(owner).to_contain("start != 16u32")
expect(owner).to_contain("fn fat32_atomic_replace_caps_probe")
expect(owner).to_contain("never publishes or overrides mounted truth")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ddf16253930b429020b2105269b9c2b650237b2236998335baa155a1ef1f03c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ddf16253930b429020b2105269b9c2b650237b2236998335baa155a1ef1f03c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ddf16253930b429020b2105269b9c2b650237b2236998335baa155a1ef1f03c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl
mirror: doc/06_spec/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should provision exactly sixteen reserved journal sectors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should provision exactly sixteen reserved journal sectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recover before root cache load and mount publication' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should recover before root cache load and mount publication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route only allowlisted DB destinations to recoverable replace' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route only allowlisted DB destinations to recoverable replace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should persist payload before header and cursor before FAT free' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish database durability only from recovered filesystem caps' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate and repair every FAT copy before cursor advancement' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
