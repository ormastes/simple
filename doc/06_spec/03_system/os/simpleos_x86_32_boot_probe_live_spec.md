# Simpleos X86 32 Boot Probe Live Specification

> Tests covering SimpleOS x86_32 boot-probe live QEMU lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos X86 32 Boot Probe Live Specification

## Scenarios

### SimpleOS x86_32 boot-probe live QEMU lane

#### boots the x86_32 browser probe to spl_start

- boots the x86_32 browser probe to spl_start
   - Expected: _enabled() is false
   - Expected: _qemu_available() is false
   - Expected: _build_prerequisite_missing(build[1]) is true
   - Expected: serial contains `PROBE_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the x86_32 browser probe to spl_start")
"""When enabled, QEMU serial output must show the x86_32 probe marker."""
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_browser_probe.elf"
    val build = _build_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(PROBE_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] qemu exit={result[1]}"
            print serial
        expect(serial.contains(PROBE_MARKER)).to_equal(true)
```

</details>

#### routes a live int 0x80 trap through the i386 IDT gate

- routes a live int 0x80 trap through the i386 IDT gate
   - Expected: _enabled() is false
   - Expected: _qemu_available() is false
   - Expected: _build_prerequisite_missing(build[1]) is true
   - Expected: serial contains `INT80_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes a live int 0x80 trap through the i386 IDT gate")
"""When enabled, QEMU serial output must show the int80 probe marker."""
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_int80_probe.elf"
    val build = _build_int80_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(INT80_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] int80 qemu exit={result[1]}"
            print serial
        expect(serial.contains(INT80_MARKER)).to_equal(true)
```

</details>

#### routes live int 0x80 through the installed Simple syscall runtime

- routes live int 0x80 through the installed Simple syscall runtime
   - Expected: _enabled() is false
   - Expected: _qemu_available() is false
   - Expected: _build_prerequisite_missing(build[1]) is true
   - Expected: serial contains `INT80_SYSCALL_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes live int 0x80 through the installed Simple syscall runtime")
"""When enabled, the real x86_32 syscall runtime must handle brk."""
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_int80_syscall_probe.elf"
    val build = _build_int80_syscall_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(INT80_SYSCALL_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] int80 syscall qemu exit={result[1]}"
            print serial
        expect(serial.contains(INT80_SYSCALL_MARKER)).to_equal(true)
```

</details>

#### routes live x86_32 process and shell smoke through the installed runtime

- routes live x86_32 process and shell smoke through the installed runtime
   - Expected: _enabled() is false
   - Expected: _qemu_available() is false
   - Expected: _build_prerequisite_missing(build[1]) is true
   - Expected: serial contains `PROCESS_CREATE_MARKER`
   - Expected: serial contains `PROCESS_BRK_MARKER`
   - Expected: serial contains `PROCESS_REBOOT_MARKER`
   - Expected: serial contains `PROCESS_DIAGNOSTICS_MARKER`
   - Expected: serial contains `SHELL_SMOKE_MARKER`
   - Expected: serial contains `PROCESS_SHELL_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes live x86_32 process and shell smoke through the installed runtime")
"""When enabled, i386 process, brk, reboot, diagnostics, and shell markers must pass."""
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_int80_process_shell_probe.elf"
    val build = _build_int80_process_shell_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(PROCESS_SHELL_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] int80 process shell qemu exit={result[1]}"
            print serial
        expect(serial.contains(PROCESS_CREATE_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_BRK_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_REBOOT_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_DIAGNOSTICS_MARKER)).to_equal(true)
        expect(serial.contains(SHELL_SMOKE_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_SHELL_MARKER)).to_equal(true)
```

</details>

#### executes x86_32 filesystem-backed app payloads from a FAT32 initrd image

- executes x86_32 filesystem-backed app payloads from a FAT32 initrd image
   - Expected: _enabled() is false
   - Expected: _qemu_available() is false
   - Expected: false is true
   - Expected: _build_prerequisite_missing(build[1]) is true
   - Expected: serial contains `FS_INITRD_MARKER`
   - Expected: serial contains `FS_HELLO_MARKER`
   - Expected: serial contains `FS_BROWSER_MARKER`
   - Expected: serial contains `FS_ARCH_MARKER`
   - Expected: serial contains `FS_EXEC_MARKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes x86_32 filesystem-backed app payloads from a FAT32 initrd image")
"""When enabled, the i386 lane must find staged app payloads in a live QEMU filesystem image."""
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_initrd_fs_exec_probe.elf"
    val image_path = "build/os/simpleos_x86_32_fs_exec.img"
    val image = _ensure_x86_32_fs_exec_image(image_path)
    val build = _build_initrd_fs_exec_probe(output_path)
    if not image[0]:
        expect(false).to_equal(true)
    elif not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe_with_initrd(output_path, image_path)
        val serial = result[0]
        if not serial.contains(FS_EXEC_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] initrd fs-exec qemu exit={result[1]}"
            print serial
        expect(serial.contains(FS_INITRD_MARKER)).to_equal(true)
        expect(serial.contains(FS_HELLO_MARKER)).to_equal(true)
        expect(serial.contains(FS_BROWSER_MARKER)).to_equal(true)
        expect(serial.contains(FS_ARCH_MARKER)).to_equal(true)
        expect(serial.contains(FS_EXEC_MARKER)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_x86_32_boot_probe_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS x86_32 boot-probe live QEMU lane.
- SimpleOS x86_32 boot-probe live QEMU lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `3d75886b4ad90205e25fe9c5145600c5060833b6e0f7575c13fffc209b036050`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d75886b4ad90205e25fe9c5145600c5060833b6e0f7575c13fffc209b036050`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d75886b4ad90205e25fe9c5145600c5060833b6e0f7575c13fffc209b036050`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/simpleos_x86_32_boot_probe_live_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_x86_32_boot_probe_live_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_x86_32_boot_probe_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_x86_32_boot_probe_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_x86_32_boot_probe_live_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the x86_32 browser probe to spl_start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_x86_32_boot_probe_live_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a live int 0x80 trap through the i386 IDT gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_x86_32_boot_probe_live_spec.spl:189:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes live int 0x80 through the installed Simple syscall runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
