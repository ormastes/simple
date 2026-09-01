# Image Package Payload Policy Specification

> Tests covering Installer image package payload policy v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Image Package Payload Policy Specification

## Scenarios

### Installer image package payload policy v1

#### blocks executable placeholders across every executable package root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks executable placeholders across every executable package root
   - Expected: decision.action equals `block-executable-placeholder`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks executable placeholders across every executable package root")
val paths = [
    "/bin/shell", "/sbin/bootctl", "/usr/bin/clang",
    "/usr/sbin/pkg", "/sys/apps/editor",
]
for path in paths:
    val decision = image_package_payload_decision_v1(
        "simpleos-tools", path, [], Architecture.X86_64)
    expect(decision.action).to_equal("block-executable-placeholder")
    expect(decision.write_payload).to_be(false)
    expect(decision.manifest_deployed).to_be(false)
    expect(decision.inventory_row).to_contain("path = \"{path}\"")
    expect(decision.inventory_row).to_contain("reason = \"package-placeholder-rejected\"")
```

</details>

#### emits the exact essential-toolchain blocked inventory row

- emits the exact essential-toolchain blocked inventory row


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the exact essential-toolchain blocked inventory row")
val decision = image_package_payload_decision_v1(
    "simpleos-apps", "/sys/apps/simple_loader", [], Architecture.X86_64)
expect(decision.essential).to_be(true)
expect(decision.inventory_row).to_equal(
    "[blocked_package_payload]\npackage = \"simpleos-apps\"\npath = \"/sys/apps/simple_loader\"\nreason = \"package-placeholder-rejected\"\nessential = true\n\n")
```

</details>

#### admits executable deployment only after native bytes were validated

- admits executable deployment only after native bytes were validated
   - Expected: admitted.action equals `stage-validated-native`
   - Expected: admitted.inventory_row equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits executable deployment only after native bytes were validated")
val denied = image_package_payload_decision_v1(
    "simpleos-tools", "/usr/bin/clang", [], Architecture.X86_64)
val admitted = image_package_payload_decision_v1(
    "simpleos-tools", "/usr/bin/clang", _elf64_x86_64(), Architecture.X86_64)
expect(denied.manifest_deployed).to_be(false)
expect(admitted.action).to_equal("stage-validated-native")
expect(admitted.write_payload).to_be(true)
expect(admitted.manifest_deployed).to_be(true)
expect(admitted.inventory_row).to_equal("")
```

</details>

#### admits only matching target-native ELF bytes

- admits only matching target-native ELF bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits only matching target-native ELF bytes")
var elf = _elf64_x86_64()
expect(image_native_executable_payload_admitted_v1(
    elf, Architecture.X86_64)).to_be(true)
expect(image_native_executable_payload_admitted_v1(
    elf, Architecture.Arm64)).to_be(false)
elf[0] = 0u8
expect(image_native_executable_payload_admitted_v1(
    elf, Architecture.X86_64)).to_be(false)
```

</details>

#### rejects a header-only ELF and an entry outside file-backed PT_LOAD bytes

- rejects a header-only ELF and an entry outside file-backed PT_LOAD bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a header-only ELF and an entry outside file-backed PT_LOAD bytes")
var header_only = _elf64_x86_64().slice(0, 64)
expect(image_native_executable_payload_admitted_v1(
    header_only, Architecture.X86_64)).to_be(false)
var bss_entry = _elf64_x86_64()
bss_entry = _put_u64_le(bss_entry, 96, 0)
expect(image_native_executable_payload_admitted_v1(
    bss_entry, Architecture.X86_64)).to_be(false)
```

</details>

#### admits canonical SMF only when its embedded ELF is a real executable

- admits canonical SMF only when its embedded ELF is a real executable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits canonical SMF only when its embedded ELF is a real executable")
val admitted = _smf_x86_64(_elf64_x86_64())
val header_only = _smf_x86_64(_elf64_x86_64().slice(0, 64))
expect(image_native_executable_payload_admitted_v1(
    admitted, Architecture.X86_64)).to_be(true)
expect(image_native_executable_payload_admitted_v1(
    admitted, Architecture.Arm64)).to_be(false)
expect(image_native_executable_payload_admitted_v1(
    header_only, Architecture.X86_64)).to_be(false)
```

</details>

#### keeps metadata payloads deployable without executable claims

- keeps metadata payloads deployable without executable claims
   - Expected: decision.action equals `write-installer-owned-metadata`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps metadata payloads deployable without executable claims")
val decision = image_package_payload_decision_v1(
    "simpleos-tools", "/SYS/CLANGMAN.TXT", [], Architecture.X86_64)
val payload = image_package_metadata_payload_v1(
    "simpleos-tools", "/SYS/CLANGMAN.TXT", PkgArch.X86_64)
expect(decision.action).to_equal("write-installer-owned-metadata")
expect(decision.manifest_deployed).to_be(true)
expect(payload).to_contain("status=standalone-required")
```

</details>

#### builds an honest mixed inventory without deployed executable placeholders

- builds an honest mixed inventory without deployed executable placeholders
   - Expected: deployed equals `["/SYS/TOOLSET.SDN"]`
   - Expected: blocked equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds an honest mixed inventory without deployed executable placeholders")
val declared = [
    "/usr/bin/terminal", "/usr/lib/libwm.a",
    "/SYS/TOOLSET.SDN", "/sys/apps/simple_compiler",
]
var deployed: [text] = []
var blocked: [text] = []
for path in declared:
    val decision = image_package_payload_decision_v1(
        "simpleos-image", path, [], Architecture.X86_64)
    if decision.manifest_deployed:
        deployed.push(path)
    else:
        blocked.push(path)
expect(deployed).to_equal(["/SYS/TOOLSET.SDN"])
expect(blocked).to_equal([
    "/usr/bin/terminal", "/usr/lib/libwm.a", "/sys/apps/simple_compiler"])
```

</details>

#### blocks every generic non-executable file when package bytes are unavailable

- blocks every generic non-executable file when package bytes are unavailable
   - Expected: decision.action equals `block-unavailable-package-bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks every generic non-executable file when package bytes are unavailable")
val paths = [
    "/usr/lib/libwm.a", "/usr/lib64/libnative.so",
    "/etc/unowned.conf", "/usr/share/data.bin",
    "/usr/share/simpleos/toolchain/clang/hello.c",
]
for path in paths:
    val decision = image_package_payload_decision_v1(
        "simpleos-image", path, [], Architecture.X86_64)
    expect(decision.action).to_equal("block-unavailable-package-bytes")
    expect(decision.write_payload).to_be(false)
    expect(decision.manifest_deployed).to_be(false)
    expect(decision.inventory_row).to_contain(
        "reason = \"package-bytes-unavailable\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/image_package_payload_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Installer image package payload policy v1.
- Installer image package payload policy v1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `406970001e0c7f38aa69134773fa12a4c4fb59a99c3dd250278f59c23b56adc7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `406970001e0c7f38aa69134773fa12a4c4fb59a99c3dd250278f59c23b56adc7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `406970001e0c7f38aa69134773fa12a4c4fb59a99c3dd250278f59c23b56adc7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/installer/image_package_payload_policy_spec.spl
mirror: doc/06_spec/01_unit/os/installer/image_package_payload_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/installer/image_package_payload_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/installer/image_package_payload_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/installer/image_package_payload_policy_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks executable placeholders across every executable package root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_package_payload_policy_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the exact essential-toolchain blocked inventory row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_package_payload_policy_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits executable deployment only after native bytes were validated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
