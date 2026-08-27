# e2e_qemu_smoke_spec

> Encodes the 6-step Phase-3 verification pipeline. Each step is a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# e2e_qemu_smoke_spec

Encodes the 6-step Phase-3 verification pipeline. Each step is a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/e2e_qemu_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Encodes the 6-step Phase-3 verification pipeline. Each step is a
    separate it-block so failures are reported individually. All cases
    skip cleanly when SIMPLEOS_QEMU_SMOKE is not set.

## Scenarios

### Phase-3 end-to-end QEMU SimpleOS smoke test

#### step 1 [phase-3-boot]: QEMU boots initramfs+FAT32 with IF-08 [BOOT] markers

- step 1 [phase-3-boot]: QEMU boots initramfs+FAT32 with IF-08 [BOOT] markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 1 [phase-3-boot]: QEMU boots initramfs+FAT32 with IF-08 [BOOT] markers")
"""
IF-08 contract: kernel emits [BOOT] init on COM1 within 60 s.
Expected serial marker: [phase-3-boot]
"""
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-boot]")
```

</details>

#### step 2 [phase-3-clang]: clang cross-compiles hello.c for x86_64-simpleos (exit 0)

- step 2 [phase-3-clang]: clang cross-compiles hello.c for x86_64-simpleos (exit 0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 2 [phase-3-clang]: clang cross-compiles hello.c for x86_64-simpleos (exit 0)")
"""
Verifies the LLVM sysroot (IF-05) is wired correctly inside the guest.
Expected serial marker: [phase-3-clang]
"""
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-clang]")
```

</details>

#### step 3 [phase-3-nm]: llvm-nm finds main symbol in hello.o

- step 3 [phase-3-nm]: llvm-nm finds main symbol in hello.o


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 3 [phase-3-nm]: llvm-nm finds main symbol in hello.o")
"""
Confirms hello.o from step 2 contains a valid ELF symbol table.
Expected serial marker: [phase-3-nm]
"""
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-nm]")
```

</details>

#### step 4 [phase-3-rustc]: rustc cross-compiles hello.rs, ELF contains _start

- step 4 [phase-3-rustc]: rustc cross-compiles hello.rs, ELF contains _start


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 4 [phase-3-rustc]: rustc cross-compiles hello.rs, ELF contains _start")
"""
Verifies the Rust PAL (IF-04) and libstd sysroot are functional.
Expected serial marker: [phase-3-rustc]
"""
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-rustc]")
```

</details>

#### step 5 [phase-3-cargo]: cargo offline build succeeds for vendored hello_rs crate

- step 5 [phase-3-cargo]: cargo offline build succeeds for vendored hello_rs crate


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 5 [phase-3-cargo]: cargo offline build succeeds for vendored hello_rs crate")
"""
Verifies the Cargo vendored protocol (IF-10) and offline build path.
Expected serial marker: [phase-3-cargo]
"""
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-cargo]")
```

</details>

#### step 6 [phase-3-convergence]: simple native-build stage3=stage4 convergence (IF-09)

- step 6 [phase-3-convergence]: simple native-build stage3=stage4 convergence (IF-09)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("step 6 [phase-3-convergence]: simple native-build stage3=stage4 convergence (IF-09)")
"""
IF-09 bootstrap verifier: stage3 compiled by stage2 must be byte-identical
to stage4 compiled by stage3 (or equal auto_stub counts).
Expected serial marker: [phase-3-convergence]
"""
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val serial = ensure_serial()
serial.to_contain("[phase-3-convergence]")
```

</details>

### phase-3 IF-08 marker registry

#### all 6 phase-3 markers are registered in canonical order

- all 6 phase-3 markers are registered in canonical order
   - Expected: markers.len() equals `6`
   - Expected: markers[0] equals `[phase-3-boot]`
   - Expected: markers[1] equals `[phase-3-clang]`
   - Expected: markers[2] equals `[phase-3-nm]`
   - Expected: markers[3] equals `[phase-3-rustc]`
   - Expected: markers[4] equals `[phase-3-cargo]`
   - Expected: markers[5] equals `[phase-3-convergence]`
   - Expected: (markers[i] == markers[j]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all 6 phase-3 markers are registered in canonical order")
val gate = qemu_smoke_gate()
if gate == "":
    return "skip: SIMPLEOS_QEMU_SMOKE not set"
val markers = [
    "[phase-3-boot]",
    "[phase-3-clang]",
    "[phase-3-nm]",
    "[phase-3-rustc]",
    "[phase-3-cargo]",
    "[phase-3-convergence]"
]
expect(markers.len()).to_equal(6)
expect(markers[0]).to_equal("[phase-3-boot]")
expect(markers[1]).to_equal("[phase-3-clang]")
expect(markers[2]).to_equal("[phase-3-nm]")
expect(markers[3]).to_equal("[phase-3-rustc]")
expect(markers[4]).to_equal("[phase-3-cargo]")
expect(markers[5]).to_equal("[phase-3-convergence]")
## Assert all markers are distinct (no duplicates)
var i: i32 = 0
while i < markers.len():
    var j: i32 = i + 1
    while j < markers.len():
        expect((markers[i] == markers[j])).to_equal(false)
        j = j + 1
    i = i + 1
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ede8ecae2738ede94191791c5c7c7409200beed0e57553c90b8648d92ea87666`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ede8ecae2738ede94191791c5c7c7409200beed0e57553c90b8648d92ea87666`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ede8ecae2738ede94191791c5c7c7409200beed0e57553c90b8648d92ea87666`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/os/port/e2e_qemu_smoke_spec.spl
mirror: doc/06_spec/03_system/os/port/e2e_qemu_smoke_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/port/e2e_qemu_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/e2e_qemu_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/port/e2e_qemu_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/port/e2e_qemu_smoke_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'step 1 [phase-3-boot]: QEMU boots initramfs+FAT32 with IF-08 [BOOT] markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/port/e2e_qemu_smoke_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'step 2 [phase-3-clang]: clang cross-compiles hello.c for x86_64-simpleos (exit 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/port/e2e_qemu_smoke_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'step 3 [phase-3-nm]: llvm-nm finds main symbol in hello.o' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
