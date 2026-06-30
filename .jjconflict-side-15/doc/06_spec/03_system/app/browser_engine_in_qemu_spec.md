# Browser Engine In Qemu Specification

> <details>

<!-- sdn-diagram:id=browser_engine_in_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_engine_in_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_engine_in_qemu_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_engine_in_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Engine In Qemu Specification

## Scenarios

### Browser engine in QEMU baremetal ELF execution

#### boots the browser probe ELF

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
