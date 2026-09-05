# Simpleos Tool Inventory V1 Specification

> Tests covering SimpleOS truthful primary-tool inventory v1 focused.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Tool Inventory V1 Specification

## Scenarios

### SimpleOS truthful primary-tool inventory v1 focused

#### validates a fully bound Supported entry but requires the evidence owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates a fully bound Supported entry but requires the evidence owner
   - Expected: simpleos_tool_inventory_v1_validate(valid_entry()) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("validates a fully bound Supported entry but requires the evidence owner")
expect(simpleos_tool_inventory_v1_validate(valid_entry())).to_equal(Ok(()))
expect(simpleos_tool_inventory_v1_can_advertise(valid_entry())).to_be(false)
```

</details>

#### rejects uppercase or malformed artifact digests

- rejects uppercase or malformed artifact digests
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.InvalidArtifactDigest)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects uppercase or malformed artifact digests")
var entry = valid_entry()
entry.artifact_digest = "0123456789ABCDEF0123456789abcdef0123456789abcdef0123456789abcdef"
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.InvalidArtifactDigest))
```

</details>

#### rejects non-canonical artifact paths and control characters

- rejects non-canonical artifact paths and control characters
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.InvalidArtifactPath)`
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.InvalidScalar)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects non-canonical artifact paths and control characters")
var entry = valid_entry()
entry.artifact_path = "/sys/apps/../bin/simple"
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.InvalidArtifactPath))
entry = valid_entry()
entry.help_contract = "help-v1\nforged-row"
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.InvalidScalar))
```

</details>

#### rejects Supported without target, filesystem, operation, error, and evidence bindings

- rejects Supported without target, filesystem, operation, error, and evidence bindings
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.MissingTarget)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects Supported without target, filesystem, operation, error, and evidence bindings")
var entry = valid_entry()
entry.target_triples = []
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.MissingTarget))
```

</details>

#### rejects duplicate capabilities, targets, filesystems, and receipts

- rejects duplicate capabilities, targets, filesystems, and receipts
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.DuplicateCapability)`
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.DuplicateTarget)`
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.DuplicateFilesystem)`
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.DuplicateEvidenceReceipt)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects duplicate capabilities, targets, filesystems, and receipts")
var entry = valid_entry()
entry.capabilities = ["compile", "compile"]
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.DuplicateCapability))
entry.capabilities = ["compile"]
entry.target_triples = [SIMPLEOS_TARGET_V1_X86_64_TRIPLE, SIMPLEOS_TARGET_V1_X86_64_TRIPLE, SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE]
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.DuplicateTarget))
entry.target_triples = [SIMPLEOS_TARGET_V1_X86_64_TRIPLE, SIMPLEOS_TARGET_V1_AARCH64_TRIPLE, SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE]
entry.filesystems = ["FAT32", "FAT32", "NVFS"]
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.DuplicateFilesystem))
entry.filesystems = ["FAT32", "DBFS", "NVFS"]
entry.evidence_receipt_ids = ["receipt-req011-001", "receipt-req011-001"]
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.DuplicateEvidenceReceipt))
```

</details>

#### requires a blocker for non-supported states and rejects fabricated success IDs

- requires a blocker for non-supported states and rejects fabricated success IDs
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.MissingBlocker)`
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Err(SimpleOsToolInventoryError.FabricatedSuccess)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("requires a blocker for non-supported states and rejects fabricated success IDs")
var entry = valid_entry()
entry.status = SimpleOsToolStatus.Blocked
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.MissingBlocker))
entry.blocker = "ring3 userland unavailable"
entry.operation_behavior_id = "success"
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Err(SimpleOsToolInventoryError.FabricatedSuccess))
```

</details>

#### allows blocked inventory without fabricated artifact or evidence identity

- allows blocked inventory without fabricated artifact or evidence identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("allows blocked inventory without fabricated artifact or evidence identity")
var entry = valid_entry()
entry.status = SimpleOsToolStatus.Blocked
entry.artifact_path = ""
entry.artifact_digest = ""
entry.evidence_receipt_ids = []
entry.blocker = "ring3 userland unavailable"
expect(simpleos_tool_inventory_v1_can_advertise(entry)).to_be(true)
```

</details>

#### allows a blocked canonical artifact path without fabricating its digest

- allows a blocked canonical artifact path without fabricating its digest
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("allows a blocked canonical artifact path without fabricating its digest")
var entry = valid_entry()
entry.status = SimpleOsToolStatus.Blocked
entry.artifact_digest = ""
entry.evidence_receipt_ids = []
entry.blocker = "target artifact has not been admitted"
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Ok(()))
expect(simpleos_tool_inventory_v1_can_advertise(entry)).to_be(true)
```

</details>

#### keeps partial claims behind evidence admission while publishing unavailable gaps

- keeps partial claims behind evidence admission while publishing unavailable gaps
   - Expected: simpleos_tool_inventory_v1_validate(entry) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("keeps partial claims behind evidence admission while publishing unavailable gaps")
var entry = valid_entry()
entry.status = SimpleOsToolStatus.Partial
entry.blocker = "only one target has execution evidence"
expect(simpleos_tool_inventory_v1_validate(entry)).to_equal(Ok(()))
expect(simpleos_tool_inventory_v1_can_advertise(entry)).to_be(false)
entry.status = SimpleOsToolStatus.Unavailable
entry.artifact_path = ""
entry.artifact_digest = ""
entry.evidence_receipt_ids = []
expect(simpleos_tool_inventory_v1_can_advertise(entry)).to_be(true)
```

</details>

#### rejects a target outside the canonical SimpleOS target contract

- rejects a target outside the canonical SimpleOS target contract
   - Expected: result equals `Err(SimpleOsToolInventoryError.InvalidTarget)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects a target outside the canonical SimpleOS target contract")
var entry = valid_entry()
entry.status = SimpleOsToolStatus.Blocked
entry.blocker = "target port unavailable"
entry.target_triples = ["mips64-unknown-simpleos"]
val result = simpleos_tool_inventory_v1_validate(entry)
expect(result).to_equal(Err(SimpleOsToolInventoryError.InvalidTarget))
```

</details>

#### keeps the primary profile closed while exposing exact implemented owners as blocked

- keeps the primary profile closed while exposing exact implemented owners as blocked
   - Expected: rows.len() equals `8`
   - Expected: rows[i].canonical_name equals `names[i]`
   - Expected: rows[i].capabilities[0] equals `categories[i]`
   - Expected: rows[i].target_triples.len() equals `3`
   - Expected: rows[i].filesystems equals `["FAT32", "DBFS", "NVFS"]`
   - Expected: rows[i].status equals `SimpleOsToolStatus.Blocked`
   - Expected: rows[i].source_owner equals `os.tools.shell.checksum.checksum_tool`
   - Expected: rows[i].artifact_path equals `/usr/bin/{rows[i].canonical_name}`
   - Expected: rows[i].artifact_digest equals ``
   - Expected: rows[i].capabilities equals `["checksums", rows[i].canonical_name]`
   - Expected: rows[i].blocker equals `simpleos-primary-checksum-target-execution-evidence-unavailable`
   - Expected: rows[i].status equals `SimpleOsToolStatus.Blocked`
   - Expected: rows[i].source_owner equals `os.tools.shell.grep.grep_tool`
   - Expected: rows[i].artifact_path equals `/usr/bin/grep`
   - Expected: rows[i].artifact_digest equals ``
   - Expected: rows[i].capabilities equals `["text-processing", "grep"]`
   - Expected: rows[i].blocker equals `simpleos-primary-text-target-execution-evidence-unavailable`
   - Expected: rows[i].status equals `SimpleOsToolStatus.Blocked`
   - Expected: rows[i].source_owner equals `os.tools.proc.ps_tool`
   - Expected: rows[i].artifact_path equals `/usr/bin/ps`
   - Expected: rows[i].artifact_digest equals ``
   - Expected: rows[i].capabilities equals `["process-monitoring", "ps"]`
   - Expected: rows[i].blocker equals `simpleos-primary-process-target-artifact-loader-unavailable`
   - Expected: rows[i].status equals `SimpleOsToolStatus.Blocked`
   - Expected: rows[i].source_owner equals `os.tools.primary_userland_host`
   - Expected: rows[i].artifact_path equals ``
   - Expected: rows[i].capabilities[1] equals `bounded-read-only-inspection`
   - Expected: rows[i].blocker equals `mutation and external I/O require a host capability provider`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("keeps the primary profile closed while exposing exact implemented owners as blocked")
val rows = simpleos_primary_tool_manifest_v1()
expect(rows.len()).to_equal(8)
val names = [
    "admin", "archive", "network", "sha256sum", "md5sum",
    "grep", "ps", "package"
]
val categories = ["administration", "archive-compression", "networking", "checksums", "checksums", "text-processing", "process-monitoring", "package-management"]
var i = 0
while i < rows.len():
    expect(rows[i].canonical_name).to_equal(names[i])
    expect(rows[i].capabilities[0]).to_equal(categories[i])
    expect(simpleos_tool_inventory_v1_can_advertise(rows[i])).to_be(true)
    expect(rows[i].target_triples.len()).to_equal(3)
    expect(rows[i].filesystems).to_equal(["FAT32", "DBFS", "NVFS"])
    if rows[i].canonical_name == "sha256sum" or rows[i].canonical_name == "md5sum":
        expect(rows[i].status).to_equal(SimpleOsToolStatus.Blocked)
        expect(rows[i].source_owner).to_equal("os.tools.shell.checksum.checksum_tool")
        expect(rows[i].artifact_path).to_equal("/usr/bin/{rows[i].canonical_name}")
        expect(rows[i].artifact_digest).to_equal("")
        expect(rows[i].capabilities).to_equal(["checksums", rows[i].canonical_name])
        expect(rows[i].blocker).to_equal("simpleos-primary-checksum-target-execution-evidence-unavailable")
    elif rows[i].canonical_name == "grep":
        expect(rows[i].status).to_equal(SimpleOsToolStatus.Blocked)
        expect(rows[i].source_owner).to_equal("os.tools.shell.grep.grep_tool")
        expect(rows[i].artifact_path).to_equal("/usr/bin/grep")
        expect(rows[i].artifact_digest).to_equal("")
        expect(rows[i].capabilities).to_equal(["text-processing", "grep"])
        expect(rows[i].blocker).to_equal("simpleos-primary-text-target-execution-evidence-unavailable")
    elif rows[i].canonical_name == "ps":
        expect(rows[i].status).to_equal(SimpleOsToolStatus.Blocked)
        expect(rows[i].source_owner).to_equal("os.tools.proc.ps_tool")
        expect(rows[i].artifact_path).to_equal("/usr/bin/ps")
        expect(rows[i].artifact_digest).to_equal("")
        expect(rows[i].capabilities).to_equal(["process-monitoring", "ps"])
        expect(rows[i].blocker).to_equal("simpleos-primary-process-target-artifact-loader-unavailable")
    else:
        expect(rows[i].status).to_equal(SimpleOsToolStatus.Blocked)
        expect(rows[i].source_owner).to_equal("os.tools.primary_userland_host")
        expect(rows[i].artifact_path).to_equal("")
        expect(rows[i].capabilities[1]).to_equal("bounded-read-only-inspection")
        expect(rows[i].blocker).to_equal("mutation and external I/O require a host capability provider")
    i = i + 1
expect(simpleos_primary_tool_manifest_v1_is_closed("admin")).to_be(true)
expect(simpleos_primary_tool_manifest_v1_is_closed("sha256sum")).to_be(true)
expect(simpleos_primary_tool_manifest_v1_is_closed("md5sum")).to_be(true)
expect(simpleos_primary_tool_manifest_v1_is_closed("grep")).to_be(true)
expect(simpleos_primary_tool_manifest_v1_is_closed("ps")).to_be(true)
expect(simpleos_primary_tool_manifest_v1_is_closed("checksum")).to_be(false)
expect(simpleos_primary_tool_manifest_v1_is_closed("unknown-tool")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/simpleos_tool_inventory_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS truthful primary-tool inventory v1 focused.
- SimpleOS truthful primary-tool inventory v1 focused

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-011`
- `REQ-SSPEC-COMMON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea74da302380053db42822a1fb33923d3ad060df5d8532ba0a62adb80e9d3263`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea74da302380053db42822a1fb33923d3ad060df5d8532ba0a62adb80e9d3263`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea74da302380053db42822a1fb33923d3ad060df5d8532ba0a62adb80e9d3263`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/common/simpleos_tool_inventory_v1_spec.spl
mirror: doc/06_spec/01_unit/common/simpleos_tool_inventory_v1_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/common/simpleos_tool_inventory_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/simpleos_tool_inventory_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/simpleos_tool_inventory_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/common/simpleos_tool_inventory_v1_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/common/simpleos_tool_inventory_v1_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates a fully bound Supported entry but requires the evidence owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/simpleos_tool_inventory_v1_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects uppercase or malformed artifact digests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/simpleos_tool_inventory_v1_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-canonical artifact paths and control characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
