# @manual: primary

> Purpose: Prove that smf_dyload gate (H8).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that smf_dyload gate (H8).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/smf_dyload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that smf_dyload gate (H8).
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-KERNEL-001
doc/01_research/local/REQ-OS-KERNEL-001.md
doc/03_plan/sys_test/REQ-OS-KERNEL-001.md
doc/04_architecture/REQ-OS-KERNEL-001.md
doc/05_design/REQ-OS-KERNEL-001.md

## Scenarios

### smf_dyload gate (H8)

#### dynloads a role-2 x86_64 SMF library and resolves exported symbols by name

- Verify: dynloads a role-2 x86_64 SMF library and resolves exported symbols by name
   - Expected: loader_dynsym(handle, "smf_hello") equals `0xBEEF`
   - Expected: loader_dynsym(handle, "smf_add") equals `0xF00D`
   - Expected: loader_dynsym(handle, "_start") equals `0x400000`
   - Expected: loader_dynsym(handle, "main") equals `0x400000`
   - Expected: loader_dynsym(handle, "smf_missing") equals `-2`
   - Expected: loader_dynclose(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: dynloads a role-2 x86_64 SMF library and resolves exported symbols by name")
"""A matching role-2/x86_64/simpleos-ABI envelope registers through the
arch-validated loader API and both exported functions resolve via
loader_dynsym, alongside the entry-symbol fast path."""
dylib_registry_reset_for_test()
val env = make_smf_lib_envelope(2, 1, 1)
val handle = loader_dynopen_smf_library_bytes_for_arch("/lib/h8_hot.smf", env, Architecture.X86_64)
expect(handle).to_be_greater_than(0)
# exported symbols via .dynsym slow path
expect(loader_dynsym(handle, "smf_hello")).to_equal(0xBEEF)
expect(loader_dynsym(handle, "smf_add")).to_equal(0xF00D)
# entry-symbol fast path
expect(loader_dynsym(handle, "_start")).to_equal(0x400000)
expect(loader_dynsym(handle, "main")).to_equal(0x400000)
# missing symbol → -ENOENT
expect(loader_dynsym(handle, "smf_missing")).to_equal(-2)
expect(loader_dynclose(handle)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### accepts arch-matching and arch-unspecified envelopes

- Verify: accepts arch-matching and arch-unspecified envelopes
   - Expected: loader_dynsym(arm_handle, "smf_hello") equals `0xBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: accepts arch-matching and arch-unspecified envelopes")
dylib_registry_reset_for_test()
# arm64 envelope on an arm64 target
val arm_env = make_smf_lib_envelope(2, 3, 1)
val arm_handle = loader_dynopen_smf_library_bytes_for_arch("/lib/h8_arm64.smf", arm_env, Architecture.Arm64)
expect(arm_handle).to_be_greater_than(0)
expect(loader_dynsym(arm_handle, "smf_hello")).to_equal(0xBEEF)
# arch/abi = 0 (unspecified) is accepted for any target
val any_env = make_smf_lib_envelope(2, 0, 0)
val any_handle = loader_dynopen_smf_library_bytes_for_arch("/lib/h8_anyarch.smf", any_env, Architecture.X86_64)
expect(any_handle).to_be_greater_than(0)
```

</details>

#### fails closed for wrong-arch, wrong-role, and wrong-ABI envelopes

- Verify: fails closed for wrong-arch, wrong-role, and wrong-ABI envelopes
   - Expected: loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", wrong_arch, Architecture.X86_64) equals `-8`
   - Expected: loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", wrong_role, Architecture.X86_64) equals `-8`
   - Expected: loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", wrong_abi, Architecture.X86_64) equals `-8`
   - Expected: loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", empty, Architecture.X86_64) equals `-2`
   - Expected: loader_dynopen_smf_library_bytes_for_arch("", make_smf_lib_envelope(2, 1, 1), Architecture.X86_64) equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: fails closed for wrong-arch, wrong-role, and wrong-ABI envelopes")
"""Mismatched metadata must never register a handle: each rejection
returns -ENOEXEC (-8) before the registry is touched."""
dylib_registry_reset_for_test()
# arm64-tagged library on an x86_64 target
val wrong_arch = make_smf_lib_envelope(2, 3, 1)
expect(loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", wrong_arch, Architecture.X86_64)).to_equal(-8)
# executable role (1) through the library gate
val wrong_role = make_smf_lib_envelope(1, 1, 1)
expect(loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", wrong_role, Architecture.X86_64)).to_equal(-8)
# unknown ABI (2)
val wrong_abi = make_smf_lib_envelope(2, 1, 2)
expect(loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", wrong_abi, Architecture.X86_64)).to_equal(-8)
# empty bytes / empty path
val empty: [u8] = []
expect(loader_dynopen_smf_library_bytes_for_arch("/lib/h8_bad.smf", empty, Architecture.X86_64)).to_equal(-2)
expect(loader_dynopen_smf_library_bytes_for_arch("", make_smf_lib_envelope(2, 1, 1), Architecture.X86_64)).to_equal(-22)
```

</details>

#### dynloads a real on-disk .smf file via loader_dynopen_path

- Verify: dynloads a real on-disk .smf file via loader_dynopen_path
   - Expected: rt_file_write_bytes(path, env) is true
   - Expected: loader_dynsym(handle, "smf_hello") equals `0xBEEF`
   - Expected: loader_dynsym(handle, "smf_add") equals `0xF00D`
   - Expected: loader_dynclose(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: dynloads a real on-disk .smf file via loader_dynopen_path")
"""The file leg of the pipeline: envelope bytes written to disk are
read back through rt_file_read_bytes and register end-to-end."""
dylib_registry_reset_for_test()
val path = "/tmp/h8_smf_dyload_gate.smf"
val env = make_smf_lib_envelope(2, 1, 1)
expect(rt_file_write_bytes(path, env)).to_equal(true)
val handle = loader_dynopen_path(path)
expect(handle).to_be_greater_than(0)
expect(loader_dynsym(handle, "smf_hello")).to_equal(0xBEEF)
expect(loader_dynsym(handle, "smf_add")).to_equal(0xF00D)
expect(loader_dynclose(handle)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### keeps unmapped SMF symbols non-process-callable (execution is boot-gated)

- Verify: keeps unmapped SMF symbols non-process-callable (execution is boot-gated)
   - Expected: loader_dynsym(handle, "smf_hello") equals `0xBEEF`
   - Expected: loader_dynsym_is_process_callable(handle, "smf_hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: keeps unmapped SMF symbols non-process-callable (execution is boot-gated)")
"""Resolving a symbol from registry bytes is not the same as being able
to call it: until the library is mapped PF_X into a live process VM
space in-guest, the loader must report non-callable. Actually invoking
the loaded code is the boot-gated half of this gate."""
dylib_registry_reset_for_test()
val env = make_smf_lib_envelope(2, 1, 1)
val handle = loader_dynopen_smf_library_bytes_for_arch("/lib/h8_hot.smf", env, Architecture.X86_64)
expect(handle).to_be_greater_than(0)
expect(loader_dynsym(handle, "smf_hello")).to_equal(0xBEEF)
expect(loader_dynsym_is_process_callable(handle, "smf_hello")).to_equal(false)
```

</details>

#### documents the writer/kernel trailer skew: toolchain output cannot pass the role-2 library gate

- Verify: documents the writer/kernel trailer skew: toolchain output cannot pass the role-2 library gate
   - Expected: loader_dynsym(handle, "smf_hello") equals `0xBEEF`
   - Expected: loader_dynopen_smf_library_bytes_for_arch("/lib/h8_writer2.smf", writer_env, Architecture.X86_64) equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Verify: documents the writer/kernel trailer skew: toolchain output cannot pass the role-2 library gate")
"""The compiler's SMF v1.1 writer stores module_hash at trailer bytes
60-67 where the kernel reads role/arch/abi, so every written envelope
arrives role=0: tolerated as an executable envelope, fail-closed as a
role-2 library. This pins the current skew until a writer learns to
emit kernel role/arch/ABI bytes."""
dylib_registry_reset_for_test()
val writer_env = make_writer_layout_envelope()
# executable-envelope tolerance: role=0 registers via the generic path
val handle = loader_dynopen_bytes("/lib/h8_writer.smf", writer_env)
expect(handle).to_be_greater_than(0)
expect(loader_dynsym(handle, "smf_hello")).to_equal(0xBEEF)
# strict role-2 library gate fails closed on writer-default metadata
expect(loader_dynopen_smf_library_bytes_for_arch("/lib/h8_writer2.smf", writer_env, Architecture.X86_64)).to_equal(-8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-KERNEL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f30882142e14a692de77fa1861f84f840a3f96e0184ead6d96a4dbee10f5509`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f30882142e14a692de77fa1861f84f840a3f96e0184ead6d96a4dbee10f5509`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f30882142e14a692de77fa1861f84f840a3f96e0184ead6d96a4dbee10f5509`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/loader/smf_dyload_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/smf_dyload_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/loader/smf_dyload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/smf_dyload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/smf_dyload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/smf_dyload_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/kernel/loader/smf_dyload_spec.spl:242:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dynloads a role-2 x86_64 SMF library and resolves exported symbols by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/smf_dyload_spec.spl:262:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts arch-matching and arch-unspecified envelopes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/smf_dyload_spec.spl:276:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for wrong-arch, wrong-role, and wrong-ABI envelopes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
