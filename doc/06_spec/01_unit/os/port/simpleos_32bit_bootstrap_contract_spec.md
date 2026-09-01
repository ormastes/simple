# Simpleos 32bit Bootstrap Contract Specification

> Tests covering SimpleOS 32-bit bootstrap phase 1/2 evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos 32bit Bootstrap Contract Specification

## Scenarios

### SimpleOS 32-bit bootstrap phase 1/2 evidence

#### accepts bound host phases plus real per-guest filesystem hello evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts bound host phases plus real per-guest filesystem hello evidence
   - Expected: SHA1.len() equals `64`
   - Expected: host_evidence().host_triple equals `x86_64-unknown-linux-gnu`
   - Expected: host_evidence().stage2_parent_sha256 equals `host_evidence().stage1_sha256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts bound host phases plus real per-guest filesystem hello evidence")
expect(SHA1.len()).to_equal(64)
expect(host_evidence().host_triple).to_equal("x86_64-unknown-linux-gnu")
expect(host_evidence().stage2_parent_sha256).to_equal(host_evidence().stage1_sha256)
expect(host_evidence().stage2_sha256 == host_evidence().stage1_sha256).to_be(false)
expect(bootstrap_host_phase12_evidence_v1_valid(host_evidence())).to_be(true)
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest_evidence(SimpleOs32BitGuest.Arm32))).to_be(true)
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest_evidence(SimpleOs32BitGuest.Riscv32))).to_be(true)
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest_evidence(SimpleOs32BitGuest.X86_32))).to_be(true)
```

</details>

#### rejects a guest artifact not built by the admitted Stage 2 compiler

- rejects a guest artifact not built by the admitted Stage 2 compiler


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a guest artifact not built by the admitted Stage 2 compiler")
val guest = guest_evidence(SimpleOs32BitGuest.Riscv32)
guest.compiler_sha256 = SHA1
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest)).to_be(false)
```

</details>

#### rejects host evidence with stub fallback or forged stage lineage

- rejects host evidence with stub fallback or forged stage lineage


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects host evidence with stub fallback or forged stage lineage")
val fallback = host_evidence()
fallback.stub_fallback_disabled = false
expect(bootstrap_host_phase12_evidence_v1_valid(fallback)).to_be(false)
val forged = host_evidence()
forged.stage2_parent_sha256 = SHA4
expect(bootstrap_host_phase12_evidence_v1_valid(forged)).to_be(false)
```

</details>

#### rejects wrong target, qemu, filesystem path, marker, or exit status

- rejects wrong target, qemu, filesystem path, marker, or exit status


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects wrong target, qemu, filesystem path, marker, or exit status")
val guest = guest_evidence(SimpleOs32BitGuest.X86_32)
guest.qemu_system = "qemu-system-i386"
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest)).to_be(false)
guest.qemu_system = "qemu-system-x86_64"
guest.filesystem_path = "/metadata-only"
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest)).to_be(false)
guest.filesystem_path = "/FSEXEC.ELF"
guest.serial_stdout = "SIMPLEOS_FS_EXEC_OK arch=x86_32"
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest)).to_be(false)
guest.serial_stdout = "SIMPLEOS_FS_EXEC_OK arch=x86_32 nonce=abc"
guest.exit_code = 1
expect(simpleos_32bit_cross_phase12_hello_v1_valid(host_evidence(), guest)).to_be(false)
```

</details>

#### never promotes cross-build evidence to target-native phase 1/2 proof

- never promotes cross-build evidence to target-native phase 1/2 proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("never promotes cross-build evidence to target-native phase 1/2 proof")
expect(simpleos_32bit_target_native_phase12_v1_valid(host_evidence(), guest_evidence(SimpleOs32BitGuest.Arm32))).to_be(false)
expect(simpleos_32bit_target_native_phase12_v1_valid(host_evidence(), guest_evidence(SimpleOs32BitGuest.Riscv32))).to_be(false)
expect(simpleos_32bit_target_native_phase12_v1_valid(host_evidence(), guest_evidence(SimpleOs32BitGuest.X86_32))).to_be(false)
```

</details>

#### publishes one data-driven target ABI linker sysroot and tool-manifest profile per guest

- publishes one data-driven target ABI linker sysroot and tool-manifest profile per guest
   - Expected: arm.target_triple equals `armv7-unknown-simpleos`
   - Expected: rv.abi equals `ilp32`
   - Expected: rv.target_triple equals `riscv32imac-unknown-simpleos`
   - Expected: x86.target_triple equals `i686-unknown-simpleos`
   - Expected: arm.linker_emulation equals `armelf_linux_eabi`
   - Expected: x86.linker_emulation equals `elf_i386`
   - Expected: x86.qemu_system equals `qemu-system-i386`
   - Expected: arm.sysroot_manifest equals `rv.sysroot_manifest`
   - Expected: rv.tool_manifest equals `x86.tool_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("publishes one data-driven target ABI linker sysroot and tool-manifest profile per guest")
val arm = simpleos_32bit_target_profile_v1(SimpleOs32BitGuest.Arm32)
val rv = simpleos_32bit_target_profile_v1(SimpleOs32BitGuest.Riscv32)
val x86 = simpleos_32bit_target_profile_v1(SimpleOs32BitGuest.X86_32)
expect(arm.target_triple).to_equal("armv7-unknown-simpleos")
expect(rv.abi).to_equal("ilp32")
expect(rv.target_triple).to_equal("riscv32imac-unknown-simpleos")
expect(x86.target_triple).to_equal("i686-unknown-simpleos")
expect(arm.linker_emulation).to_equal("armelf_linux_eabi")
expect(x86.linker_emulation).to_equal("elf_i386")
expect(x86.qemu_system).to_equal("qemu-system-i386")
expect(arm.sysroot_manifest).to_equal(rv.sysroot_manifest)
expect(rv.tool_manifest).to_equal(x86.tool_manifest)
```

</details>

#### derives every 32-bit target identity and ABI from the canonical SimpleOS catalog

- derives every 32-bit target identity and ABI from the canonical SimpleOS catalog
   - Expected: arm.abi equals `eabihf`
   - Expected: rv.abi equals `ilp32`
   - Expected: x86.abi equals `cdecl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("derives every 32-bit target identity and ABI from the canonical SimpleOS catalog")
expect(simpleos_32bit_target_catalog_v1_complete()).to_be(true)
val arm = simpleos_32bit_target_profile_v1(SimpleOs32BitGuest.Arm32)
val rv = simpleos_32bit_target_profile_v1(SimpleOs32BitGuest.Riscv32)
val x86 = simpleos_32bit_target_profile_v1(SimpleOs32BitGuest.X86_32)
expect(arm.abi).to_equal("eabihf")
expect(rv.abi).to_equal("ilp32")
expect(x86.abi).to_equal("cdecl")
```

</details>

#### accepts complete phase 1 and phase 2 receipts for all three targets

- accepts complete phase 1 and phase 2 receipts for all three targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts complete phase 1 and phase 2 receipts for all three targets")
expect(simpleos_32bit_bootstrap_receipt_v2_valid(receipt_v2(SimpleOs32BitGuest.Arm32))).to_be(true)
expect(simpleos_32bit_bootstrap_receipt_v2_valid(receipt_v2(SimpleOs32BitGuest.Riscv32))).to_be(true)
expect(simpleos_32bit_bootstrap_receipt_v2_valid(receipt_v2(SimpleOs32BitGuest.X86_32))).to_be(true)
```

</details>

#### fails closed on incomplete phases manifests target metadata or QEMU transcript

- fails closed on incomplete phases manifests target metadata or QEMU transcript


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed on incomplete phases manifests target metadata or QEMU transcript")
val incomplete = receipt_v2(SimpleOs32BitGuest.Riscv32)
incomplete.phase2_status = "blocked"
expect(simpleos_32bit_bootstrap_receipt_v2_valid(incomplete)).to_be(false)
val no_tools = receipt_v2(SimpleOs32BitGuest.Riscv32)
no_tools.tool_manifest_sha256 = ""
expect(simpleos_32bit_bootstrap_receipt_v2_valid(no_tools)).to_be(false)
val wrong_abi = receipt_v2(SimpleOs32BitGuest.Riscv32)
wrong_abi.abi = "lp64"
expect(simpleos_32bit_bootstrap_receipt_v2_valid(wrong_abi)).to_be(false)
val fabricated = receipt_v2(SimpleOs32BitGuest.Riscv32)
fabricated.serial_stdout = "TEST PASSED nonce=" + fabricated.nonce
expect(simpleos_32bit_bootstrap_receipt_v2_valid(fabricated)).to_be(false)
```

</details>

#### rejects malformed digests missing authority and replayed receipt identity or nonce

- rejects malformed digests missing authority and replayed receipt identity or nonce


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects malformed digests missing authority and replayed receipt identity or nonce")
val malformed = receipt_v2(SimpleOs32BitGuest.Arm32)
malformed.phase1_sha256 = "GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG"
expect(simpleos_32bit_bootstrap_receipt_v2_valid(malformed)).to_be(false)
val no_authority = receipt_v2(SimpleOs32BitGuest.Arm32)
no_authority.key_id = ""
expect(simpleos_32bit_bootstrap_receipt_v2_valid(no_authority)).to_be(false)
val receipt = receipt_v2(SimpleOs32BitGuest.Arm32)
expect(simpleos_32bit_bootstrap_receipt_v2_authorized(receipt,
    "replayed-receipt", receipt.nonce, receipt.key_id, [for _ in 0..32: 1])).to_be(false)
expect(simpleos_32bit_bootstrap_receipt_v2_authorized(receipt,
    receipt.receipt_id, "replayed-nonce-0000", receipt.key_id, [for _ in 0..32: 1])).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS 32-bit bootstrap phase 1/2 evidence.
- SimpleOS 32-bit bootstrap phase 1/2 evidence

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e64314cba6d1b936abadf800769492b41af0c220431f27fe95e3e9b0ec3ec6d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e64314cba6d1b936abadf800769492b41af0c220431f27fe95e3e9b0ec3ec6d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e64314cba6d1b936abadf800769492b41af0c220431f27fe95e3e9b0ec3ec6d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl
mirror: doc/06_spec/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes one data-driven target ABI linker sysroot and tool-manifest profile per guest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives every 32-bit target identity and ABI from the canonical SimpleOS catalog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts complete phase 1 and phase 2 receipts for all three targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
