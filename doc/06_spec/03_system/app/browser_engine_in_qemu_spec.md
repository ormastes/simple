# Browser Engine In Qemu Specification

> Tests covering Browser engine in QEMU baremetal ELF execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Engine In Qemu Specification

## Scenarios

### Browser engine in QEMU baremetal ELF execution

#### boots the browser probe ELF

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- boots the browser probe ELF
   - Expected: artifact_exists(output_path) is true
   - Expected: output contains `[probe] browser spl_start`
   - Expected: output does not contain `FAULT @`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the browser probe ELF")
val output_path = "build/os/simpleos_browser_probe_32.elf"
expect(_build_target(
    "examples/09_embedded/simple_os/arch/x86_64/browser_probe_entry.spl",
    output_path,
    false
)).to_equal(true)
expect(artifact_exists(output_path)).to_equal(true)

val output = _run_qemu(output_path, "384M", "", "5s")
expect(output.contains("[probe] browser spl_start")).to_equal(true)
expect(output.contains("FAULT @")).to_equal(false)
```

</details>

#### boots the desktop probe ELF

- boots the desktop probe ELF
   - Expected: artifact_exists(output_path) is true
   - Expected: output contains `[probe] desktop spl_start`
   - Expected: output does not contain `FAULT @`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the desktop probe ELF")
val output_path = "build/os/simpleos_desktop_probe_32.elf"
expect(_build_target(
    "examples/09_embedded/simple_os/arch/x86_64/desktop_probe_entry.spl",
    output_path,
    true
)).to_equal(true)
expect(artifact_exists(output_path)).to_equal(true)

val output = _run_qemu(output_path, "384M", "", "5s")
expect(output.contains("[probe] desktop spl_start")).to_equal(true)
expect(output.contains("FAULT @")).to_equal(false)
```

</details>

#### builds and boots the browser software smoke ELF

- builds and boots the browser software smoke ELF
   - Expected: artifact_exists(output_path) is true
   - Expected: output contains `[browser-soft] start`
   - Expected: output contains `[PASS] browser_soft_entry`
   - Expected: output contains `TEST PASSED`
   - Expected: output does not contain `[FAIL]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds and boots the browser software smoke ELF")
val output_path = "build/os/simpleos_browser_soft_32.elf"
expect(_build_target(
    "examples/09_embedded/simple_os/arch/x86_64/browser_soft_entry.spl",
    output_path,
    false
)).to_equal(true)
expect(artifact_exists(output_path)).to_equal(true)

val output = _run_qemu(output_path, "384M", "-vga std", "15s")
expect(output.contains("[browser-soft] start")).to_equal(true)
expect(output.contains("[PASS] browser_soft_entry")).to_equal(true)
expect(output.contains("TEST PASSED")).to_equal(true)
expect(output.contains("[FAIL]")).to_equal(false)
```

</details>

#### runs the lean desktop wrapper through launcher and wm markers

- runs the lean desktop wrapper through launcher and wm markers
   - Expected: artifact_exists(output_path) is true
   - Expected: output contains `[desktop-e2e] launcher:ready`
   - Expected: output contains `[desktop-e2e] spl_start`
   - Expected: output contains `[desktop-e2e] launcher:ready`
   - Expected: output contains `[desktop-e2e] shortcut:ok`
   - Expected: output contains `[desktop-e2e] wm:ok`
   - Expected: output contains `[desktop-e2e] resident fallback done`
   - Expected: output contains `[desktop-e2e] remote-grouping:ok`
   - Expected: output contains `TEST PASSED`
   - Expected: output does not contain `TEST FAILED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the lean desktop wrapper through launcher and wm markers")
val output_path = "build/os/simpleos_desktop_e2e_32.elf"
expect(_build_target(
    "examples/09_embedded/simple_os/arch/x86_64/desktop_e2e_entry.spl",
    output_path,
    true
)).to_equal(true)
expect(artifact_exists(output_path)).to_equal(true)

val output = _run_qemu(output_path, "512M", "-vga std", "15s")
if output.contains("[vfs] mount_failed") and output.contains("[desktop-e2e] shortcut:fail"):
    print "SKIP: desktop launcher E2E requires a mounted app disk image"
    expect(output.contains("[desktop-e2e] launcher:ready")).to_equal(true)
else:
    expect(output.contains("[desktop-e2e] spl_start")).to_equal(true)
    expect(output.contains("[desktop-e2e] launcher:ready")).to_equal(true)
    expect(output.contains("[desktop-e2e] shortcut:ok")).to_equal(true)
    expect(output.contains("[desktop-e2e] wm:ok")).to_equal(true)
    expect(output.contains("[desktop-e2e] resident fallback done")).to_equal(true)
    expect(output.contains("[desktop-e2e] remote-grouping:ok")).to_equal(true)
    expect(output.contains("TEST PASSED")).to_equal(true)
    expect(output.contains("TEST FAILED")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser_engine_in_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser engine in QEMU baremetal ELF execution.
- Browser engine in QEMU baremetal ELF execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `c0c2715fc859626b2ac21f21a2182d003fa88f9185b435dc0a9c8a9c4447e971`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0c2715fc859626b2ac21f21a2182d003fa88f9185b435dc0a9c8a9c4447e971`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0c2715fc859626b2ac21f21a2182d003fa88f9185b435dc0a9c8a9c4447e971`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/browser_engine_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/browser_engine_in_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser_engine_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser_engine_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser_engine_in_qemu_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the browser probe ELF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser_engine_in_qemu_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the desktop probe ELF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser_engine_in_qemu_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds and boots the browser software smoke ELF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
