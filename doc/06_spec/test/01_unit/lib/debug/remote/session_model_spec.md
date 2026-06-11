# Session Model Specification

> 1. Ok

<!-- sdn-diagram:id=session_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_model_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Model Specification

## Scenarios

### remote debug session model

#### selects Intel jtagd for Intel hardware sessions

1. Ok
   - Expected: selected.backend_id equals `intel_jtagd`
   - Expected: selected.capabilities.supports("persistent_session") is true
2. Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = debug_target_descriptor("intel_jtagd", "", "riscv32", "hw", "intel", "", "")
val backend = debug_select_backend(target)
match backend:
    Ok(selected):
        expect(selected.backend_id).to_equal("intel_jtagd")
        expect(selected.capabilities.supports("persistent_session")).to_equal(true)
    Err(_):
        fail("debug_select_backend rejected Intel jtagd hardware session")
```

</details>

#### builds remote_bitbang bootstrap plan for RTL sessions

1. var hints = DebugConnectionHints empty
2. Ok
   - Expected: resolved.backend_id equals `openocd_remote_bitbang`
3. Err
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = debug_target_descriptor("rtl_sim", "openocd_remote_bitbang", "riscv32", "rtl_sim", "", "", "")
var hints = DebugConnectionHints.empty()
hints.bitbang_host = "127.0.0.1"
hints.bitbang_port = 4567
val plan = debug_bootstrap_plan(target, hints, "build/rtl.elf")
match plan:
    Ok(resolved):
        expect(resolved.backend_id).to_equal("openocd_remote_bitbang")
        expect(resolved.launch_command).to_contain("remote_bitbang")
        expect(resolved.generated_config).to_contain("remote_bitbang port 4567")
    Err(_):
        fail("debug_bootstrap_plan rejected remote_bitbang RTL session")
```

</details>

#### keeps QEMU as gdb remote validation lane

1. Ok
   - Expected: selected.backend_id equals `gdb_remote`
   - Expected: selected.exec_mode.to_string() equals `qemu_stub`
2. Err
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = debug_target_descriptor("remote", "", "riscv32", "", "", "", "")
val backend = debug_select_backend(target)
match backend:
    Ok(selected):
        expect(selected.backend_id).to_equal("gdb_remote")
        expect(selected.exec_mode.to_string()).to_equal("qemu_stub")
    Err(_):
        fail("debug_select_backend rejected QEMU gdb remote validation lane")
```

</details>

#### publishes future extension registry hooks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = debug_extension_registry_entries()
expect(entries.len()).to_be_greater_than(5)
expect(entries).to_contain("transport:swd")
expect(entries).to_contain("transport:xvc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/remote/session_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- remote debug session model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
