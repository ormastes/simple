# Boot Fs Mount Specification

> Tests covering CNvmeBlockAdapterFs — freestanding adapter initial state, FsMountResult — result type structure, boot_fs_mount module-level state — initial values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Fs Mount Specification

## Scenarios

### CNvmeBlockAdapterFs — freestanding adapter initial state

#### new adapter is not ready

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new adapter is not ready
   - Expected: adapter.ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("new adapter is not ready")
val adapter = CNvmeBlockAdapterFs(sector_buf_addr: 0, ready: false)
expect(adapter.ready).to_equal(false)
```

</details>

#### new adapter has zero sector_buf_addr

- new adapter has zero sector_buf_addr
   - Expected: adapter.sector_buf_addr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("new adapter has zero sector_buf_addr")
val adapter = CNvmeBlockAdapterFs(sector_buf_addr: 0, ready: false)
expect(adapter.sector_buf_addr).to_equal(0)
```

</details>

#### static new produces same zero state

- static new produces same zero state
   - Expected: adapter.ready is false
   - Expected: adapter.sector_buf_addr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("static new produces same zero state")
val adapter = CNvmeBlockAdapterFs.new()
expect(adapter.ready).to_equal(false)
expect(adapter.sector_buf_addr).to_equal(0)
```

</details>

### FsMountResult — result type structure

#### mounted NVFS result carries correct type

- mounted NVFS result carries correct type
   - Expected: r.mounted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mounted NVFS result carries correct type")
val r = FsMountResult(mounted: true, fs_type: FsMountType.Nvfs, provider: "c-boot-bridge", pure_simple: false)
expect(r.mounted).to_equal(true)
```

</details>

#### mounted DBFS result carries correct type

- mounted DBFS result carries correct type
   - Expected: r.mounted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mounted DBFS result carries correct type")
val r = FsMountResult(mounted: true, fs_type: FsMountType.Dbfs, provider: "c-boot-bridge", pure_simple: false)
expect(r.mounted).to_equal(true)
```

</details>

#### unmounted result has None_ type

- unmounted result has None_ type
   - Expected: r.mounted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unmounted result has None_ type")
val r = FsMountResult(mounted: false, fs_type: FsMountType.None_, provider: "none", pure_simple: false)
expect(r.mounted).to_equal(false)
```

</details>

#### rejects C bridge mount result as pure Simple boot-storage evidence

- rejects C bridge mount result as pure Simple boot-storage evidence
   - Expected: boot_fs_mount_provider_is_pure_simple("c-boot-bridge") is false
   - Expected: boot_fs_mount_acceptance_reason(c_bridge) equals `boot-storage-not-pure-simple:c-boot-bridge`
   - Expected: boot_fs_mount_acceptance_reason(pure) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects C bridge mount result as pure Simple boot-storage evidence")
val c_bridge = FsMountResult(mounted: true, fs_type: FsMountType.Nvfs, provider: "c-boot-bridge", pure_simple: false)
val pure = FsMountResult(mounted: true, fs_type: FsMountType.Nvfs, provider: "simple-driver", pure_simple: true)
expect(boot_fs_mount_provider_is_pure_simple("c-boot-bridge")).to_equal(false)
expect(boot_fs_mount_acceptance_reason(c_bridge)).to_equal("boot-storage-not-pure-simple:c-boot-bridge")
expect(boot_fs_mount_acceptance_reason(pure)).to_equal("ready")
```

</details>

### boot_fs_mount module-level state — initial values

#### fs_mount_done starts false

- fs_mount_done starts false
   - Expected: fs_mount_done() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fs_mount_done starts false")
expect(fs_mount_done()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/boot_fs_mount_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CNvmeBlockAdapterFs — freestanding adapter initial state, FsMountResult — result type structure, boot_fs_mount module-level state — initial values.
- CNvmeBlockAdapterFs — freestanding adapter initial state
- FsMountResult — result type structure
- boot_fs_mount module-level state — initial values

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `beeaef974ab08ab103621d1f8f71a7b493f11d1f9b14be4a225820f9c6c2728b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `beeaef974ab08ab103621d1f8f71a7b493f11d1f9b14be4a225820f9c6c2728b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `beeaef974ab08ab103621d1f8f71a7b493f11d1f9b14be4a225820f9c6c2728b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/kernel/boot_fs_mount_spec.spl
mirror: doc/06_spec/03_system/os/kernel/boot_fs_mount_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/kernel/boot_fs_mount_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/kernel/boot_fs_mount_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/kernel/boot_fs_mount_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/kernel/boot_fs_mount_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new adapter is not ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/kernel/boot_fs_mount_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new adapter has zero sector_buf_addr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/kernel/boot_fs_mount_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'static new produces same zero state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
