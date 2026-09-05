# qemu_systest_contract_spec

> QEMU Systest Contract — Pure Classifier Unit Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# qemu_systest_contract_spec

QEMU Systest Contract — Pure Classifier Unit Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC1 |
| Category | OS system test infrastructure |
| Status | Active |
| Source | `test/01_unit/os/qemu_systest_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU Systest Contract — Pure Classifier Unit Tests.

Verifies classify_serial logic with no QEMU needed.
Tests all four classification outcomes:
  pass, boot-fail:fallback, boot-fail:<marker>, missing-media is not tested
  here (that requires file system — tested in system specs).

## Scenarios

### classify_serial — pass

#### returns pass when all riscv64 markers present and no fallback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns pass when all riscv64 markers present and no fallback
   - Expected: result equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pass when all riscv64 markers present and no fallback")
val markers = riscv64_markers()
val result = classify_serial(_clean_serial(), markers)
expect(result).to_equal(SYSTEST_PASS)
```

</details>

#### returns pass when all x86_32 markers present and no fallback

- returns pass when all x86_32 markers present and no fallback
   - Expected: result equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pass when all x86_32 markers present and no fallback")
val markers = x86_32_markers()
val result = classify_serial(_x86_32_clean_serial(), markers)
expect(result).to_equal(SYSTEST_PASS)
```

</details>

#### rejects the legacy same-CPL x86_32 initrd probe as fs-exec evidence

- rejects the legacy same-CPL x86_32 initrd probe as fs-exec evidence
   - Expected: result equals `boot-fail:SimpleOS x86_32 boot OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the legacy same-CPL x86_32 initrd probe as fs-exec evidence")
val markers = x86_32_markers()
val result = classify_serial(_x86_32_legacy_probe_serial(), markers)
expect(result).to_equal("boot-fail:SimpleOS x86_32 boot OK")
```

</details>

#### rejects the ARM32 NVFS/SMF probe as filesystem-exec evidence

- rejects the ARM32 NVFS/SMF probe as filesystem-exec evidence
   - Expected: result equals `boot-fail:FS_LS_BEGIN path=/SYS/APPS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the ARM32 NVFS/SMF probe as filesystem-exec evidence")
val markers = arm32_markers()
val result = classify_serial(_arm32_nvfs_smf_probe_serial(), markers)
expect(result).to_equal("boot-fail:FS_LS_BEGIN path=/SYS/APPS")
```

</details>

#### returns pass for minimal one-marker list when marker present

- returns pass for minimal one-marker list when marker present
   - Expected: result equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pass for minimal one-marker list when marker present")
val markers = ["ELF_LOAD_OK"]
val result = classify_serial("ELF_LOAD_OK\nTEST PASSED\n", markers)
expect(result).to_equal(SYSTEST_PASS)
```

</details>

### classify_serial — fallback

#### returns boot-fail:fallback when resident-fallback:active pattern present

- returns boot-fail:fallback when resident-fallback:active pattern present
   - Expected: result equals `SYSTEST_BOOT_FAIL_FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boot-fail:fallback when resident-fallback:active pattern present")
val markers = riscv64_markers()
val result = classify_serial(_fallback_serial_resident_active(), markers)
expect(result).to_equal(SYSTEST_BOOT_FAIL_FALLBACK)
```

</details>

#### returns boot-fail:fallback when launcher fallback=resident-manifest present

- returns boot-fail:fallback when launcher fallback=resident-manifest present
   - Expected: result equals `SYSTEST_BOOT_FAIL_FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boot-fail:fallback when launcher fallback=resident-manifest present")
val markers = riscv64_markers()
val result = classify_serial(_fallback_serial_launcher(), markers)
expect(result).to_equal(SYSTEST_BOOT_FAIL_FALLBACK)
```

</details>

#### fallback check precedes marker check

- fallback check precedes marker check
   - Expected: result equals `SYSTEST_BOOT_FAIL_FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fallback check precedes marker check")
# serial has fallback pattern but also missing markers
val markers = riscv64_markers()
val serial = "[desktop-e2e] resident-fallback:active\nELF_LOAD_OK\n"
val result = classify_serial(serial, markers)
expect(result).to_equal(SYSTEST_BOOT_FAIL_FALLBACK)
```

</details>

### classify_serial — missing marker

#### returns boot-fail:<marker> for first missing riscv64 marker

- returns boot-fail:<marker> for first missing riscv64 marker
   - Expected: result equals `boot-fail:NATIVE_GUI_PROCESS_RENDER_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boot-fail:<marker> for first missing riscv64 marker")
val markers = riscv64_markers()
val result = classify_serial(_missing_marker_serial(), markers)
expect(result).to_equal("boot-fail:NATIVE_GUI_PROCESS_RENDER_OK")
```

</details>

#### returns boot-fail:<marker> for first missing x86_32 marker

- returns boot-fail:<marker> for first missing x86_32 marker
   - Expected: result equals `boot-fail:FS_LS_BEGIN path=/SYS/APPS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boot-fail:<marker> for first missing x86_32 marker")
val markers = x86_32_markers()
val result = classify_serial("SimpleOS x86_32 boot OK\n", markers)
expect(result).to_equal("boot-fail:FS_LS_BEGIN path=/SYS/APPS")
```

</details>

#### returns boot-fail:<marker> when no markers present

- returns boot-fail:<marker> when no markers present
   - Expected: result equals `boot-fail:MARKER_A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boot-fail:<marker> when no markers present")
val markers = ["MARKER_A", "MARKER_B"]
val result = classify_serial("", markers)
expect(result).to_equal("boot-fail:MARKER_A")
```

</details>

#### returns boot-fail:<marker> for empty serial with riscv64 markers

- returns boot-fail:<marker> for empty serial with riscv64 markers
   - Expected: result equals `boot-fail:ELF_LOAD_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns boot-fail:<marker> for empty serial with riscv64 markers")
val markers = riscv64_markers()
val result = classify_serial("", markers)
expect(result).to_equal("boot-fail:ELF_LOAD_OK")
```

</details>

### classify_serial — edge cases

#### empty marker list with clean serial returns pass

- empty marker list with clean serial returns pass
   - Expected: result equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty marker list with clean serial returns pass")
val markers: [text] = []
val result = classify_serial(_clean_serial(), markers)
expect(result).to_equal(SYSTEST_PASS)
```

</details>

#### empty marker list with fallback serial returns boot-fail:fallback

- empty marker list with fallback serial returns boot-fail:fallback
   - Expected: result equals `SYSTEST_BOOT_FAIL_FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty marker list with fallback serial returns boot-fail:fallback")
val markers: [text] = []
val result = classify_serial(_fallback_serial_resident_active(), markers)
expect(result).to_equal(SYSTEST_BOOT_FAIL_FALLBACK)
```

</details>

#### partial marker match returns fail for first missing

- partial marker match returns fail for first missing
   - Expected: result equals `boot-fail:C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("partial marker match returns fail for first missing")
val markers = ["A", "B", "C"]
val result = classify_serial("A\nB\n", markers)
expect(result).to_equal("boot-fail:C")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `40db96aadf9ae17a25446b6f18d16c3e82f97ca602f9e172dac1624af4b3fd9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40db96aadf9ae17a25446b6f18d16c3e82f97ca602f9e172dac1624af4b3fd9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40db96aadf9ae17a25446b6f18d16c3e82f97ca602f9e172dac1624af4b3fd9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/qemu_systest_contract_spec.spl
mirror: doc/06_spec/01_unit/os/qemu_systest_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/qemu_systest_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/qemu_systest_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/qemu_systest_contract_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns pass when all riscv64 markers present and no fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/qemu_systest_contract_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns pass when all x86_32 markers present and no fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/qemu_systest_contract_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the legacy same-CPL x86_32 initrd probe as fs-exec evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
