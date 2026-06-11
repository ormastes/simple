# Wine Substrate Specification

> <details>

<!-- sdn-diagram:id=wine_substrate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_substrate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_substrate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_substrate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Substrate Specification

## Scenarios

### Wine substrate readiness gates

### capability state

#### reports completed research without claiming platform readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_substrate_capability_state("research")).to_equal("verified")
expect(wine_substrate_capability_state("exec_env")).to_equal("partial")
expect(wine_substrate_capability_state("pe_loader")).to_equal("partial")
expect(wine_substrate_capability_state("pthread")).to_equal("partial")
expect(wine_substrate_capability_state("dynload")).to_equal("partial")
expect(wine_substrate_capability_state("registry")).to_equal("partial")
expect(wine_substrate_capability_state("user32")).to_equal("partial")
expect(wine_substrate_capability_state("gdi32")).to_equal("partial")
expect(wine_substrate_capability_state("kernel32_core")).to_equal("partial")
expect(wine_substrate_capability_state("audio")).to_equal("missing")
```

</details>

#### does not verify unfinished rows just because evidence text exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_substrate_verify_capability("pthread", "doc/some-evidence.md")
expect(state).to_equal("partial")
```

</details>

#### derives verified capability rows from explicit gate evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified pthread=verified dynload=verified registry=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_capability_state_from_gates("pthread", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("fs_semantics", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("user32", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("gdi32", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("kernel32_core", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("registry", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("audio", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("fonts", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("input", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("audio", "host=verified")).to_equal("missing")
expect(wine_substrate_capability_state_from_gates("hello_exe", gates)).to_equal("verified")
val posix = wine_substrate_capability_row("posix_fd", gates)
expect(posix.state).to_equal("verified")
expect(posix.evidence_command).to_contain("wine_kernel32_file_io_spec")
val row = wine_substrate_capability_row("nt_bridge", gates)
expect(row.state).to_equal("verified")
expect(row.implementation_path).to_equal("src/lib/common/wine_nt_bridge.spl")
expect(row.evidence_command).to_equal("bin/simple test test/unit/lib/common/wine_nt_bridge_spec.spl --mode=interpreter --clean")
val exec_env = wine_substrate_capability_row("exec_env", gates)
expect(exec_env.state).to_equal("verified")
expect(exec_env.evidence_command).to_equal("bin/simple test test/unit/lib/common/wine_simpleos_exec_env_gate_spec.spl --mode=interpreter --clean")
val pe_loader = wine_substrate_capability_row("pe_loader", gates)
expect(pe_loader.state).to_equal("verified")
expect(pe_loader.evidence_command).to_contain("wine_pe_loader_runtime_spec")
val user32 = wine_substrate_capability_row("user32", gates)
expect(user32.state).to_equal("verified")
expect(user32.evidence_command).to_contain("wine_user32_window_spec")
val gdi32 = wine_substrate_capability_row("gdi32", gates)
expect(gdi32.state).to_equal("verified")
expect(gdi32.evidence_command).to_contain("wine_gdi32_drawing_spec")
val kernel32_core = wine_substrate_capability_row("kernel32_core", gates)
expect(kernel32_core.state).to_equal("verified")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_virtual_memory_spec")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_interlocked_spec")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_process_env_spec")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_file_metadata_spec")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_file_management_spec")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_module_loader_spec")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_process_identity_spec")
val dynload = wine_substrate_capability_row("dynload", gates)
expect(dynload.state).to_equal("verified")
expect(dynload.evidence_command).to_contain("wine_ntdll_loader_spec")
val pthread = wine_substrate_capability_row("pthread", gates)
expect(pthread.state).to_equal("verified")
expect(pthread.evidence_command).to_contain("wine_nt_thread_wait_spec")
val ipc = wine_substrate_capability_row("ipc_wait", gates)
expect(ipc.state).to_equal("verified")
expect(ipc.evidence_command).to_contain("wine_advapi32_service_spec")
val registry = wine_substrate_capability_row("registry", gates)
expect(registry.state).to_equal("verified")
expect(registry.implementation_path).to_equal("src/lib/common/wine_advapi32_registry.spl")
expect(registry.evidence_command).to_contain("wine_ntdll_registry_spec")
val audio = wine_substrate_capability_row("audio", gates)
expect(audio.state).to_equal("verified")
expect(audio.evidence_command).to_equal("bin/simple test test/unit/lib/common/wine_service_adapter_spec.spl --mode=interpreter --clean")
```

</details>

<details>
<summary>Advanced: lists explicit matrix rows for modeled Wine preconditions</summary>

#### lists explicit matrix rows for modeled Wine preconditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = wine_substrate_capability_matrix("process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified pthread=verified dynload=verified registry=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified")
expect(matrix.len()).to_equal(21)
expect(matrix[0].capability).to_equal("process")
expect(matrix[1].capability).to_equal("exec_env")
expect(matrix[5].capability).to_equal("user32")
expect(matrix[6].capability).to_equal("gdi32")
expect(matrix[7].capability).to_equal("kernel32_core")
expect(matrix[9].capability).to_equal("fs_semantics")
expect(matrix[10].capability).to_equal("ipc_wait")
expect(matrix[11].capability).to_equal("registry")
expect(matrix[15].capability).to_equal("fonts")
expect(matrix[19].capability).to_equal("nt_bridge")
expect(matrix[20].state).to_equal("verified")
```

</details>


</details>

### process evidence

#### rejects resident fallback markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_substrate_check_process_evidence("[desktop-e2e] process-backed:resident")
expect(result).to_equal("resident-fallback")
```

</details>

#### requires all baseline process-backed app markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3\n" +
    "[desktop-e2e] process-backed:ok app=terminal pid=4\n" +
    "[desktop-e2e] process-backed:ok app=file_manager pid=5"
expect(wine_substrate_check_process_evidence(log)).to_equal("process-backed")
```

</details>

#### rejects partial process-backed evidence without terminal and file manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3"
expect(wine_substrate_check_process_evidence(log)).to_equal("insufficient-evidence")
```

</details>

### VM and renderer gates

#### reports full-OS executable environment gaps before Wine readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val partial = "simpleos-qemu-vm simpleos-full-os-boot simpleos-user-process"
expect(wine_substrate_exec_env_gate(partial)).to_equal("missing-simpleos-vmspace")
val serial_log = "QEMU x86_64 desktop lane\n" +
    "[phase-3-mount] fat32 ok\n" +
    "[vfs] mounted fat32 device=nvme0 volume=simpleos\n" +
    "[fs-exec] spawn:image path=/sys/apps/wine_hello entry=0 segments=1 stub_bytes=128\n" +
    "[desktop-e2e] process-backed:ok app=wine_hello pid=42\n" +
    "[desktop-e2e] wm:ok pid=42 wid=1001\n" +
    "[desktop-e2e] network-smoke:bounded ok packets=1\n" +
    "[desktop-e2e] container-namespace:ok pid fs ipc net capability\n" +
    "[desktop-e2e] container-rootfs:ok rootfs=/containers/wine rootfs_backend=nvfs\n" +
    "TEST PASSED"
expect(wine_substrate_exec_env_gate_from_serial_log(serial_log)).to_equal("ready")
```

</details>

#### reports the first missing VM requirement

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_substrate_vm_gate("reserve commit unmap fixed-map")).to_equal("missing-mprotect")
```

</details>

#### reports renderer backend gaps in X11-class behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "display screen window map-unmap configure surface damage clip expose present input focus cursor"
expect(wine_substrate_renderer_gate(features)).to_equal("missing-atom")
```

</details>

#### reports host substrate gaps for all other Wine features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv spawn fs-paths"
expect(wine_substrate_host_gate(features)).to_equal("missing-fs-attrs")
```

</details>

#### reports PE loader preparation gaps before hello.exe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "mz pe-signature machine-x86_64 pe32plus"
expect(wine_substrate_pe_gate(features)).to_equal("missing-section-bounds")
```

</details>

#### requires nogc async primitives for Wine async readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "nogc-future poll waker io-driver submit-open submit-read"
expect(wine_substrate_async_gate(features)).to_equal("missing-submit-write")
```

</details>

### hello.exe gate

#### blocks hello.exe until substrate gates are verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified")
expect(state).to_equal("blocked")
```

</details>

#### still blocks hello.exe until the modeled NT bridge is verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified")
expect(state).to_equal("blocked")
```

</details>

#### allows hello.exe only after async and NT bridge gates are verified too

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified")
expect(state).to_equal("ready")
```

</details>

### full Wine gate

#### does not treat controlled hello.exe readiness as full Wine readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_hello_exe_gate(hello_gates)).to_equal("ready")
expect(wine_substrate_full_wine_gate(hello_gates)).to_equal("blocked-missing-renderer")
```

</details>

#### requires every tracked Wine substrate row before full Wine readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val missing_registry = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_full_wine_gate(gates)).to_equal("ready")
expect(wine_substrate_full_wine_gate(missing_registry)).to_equal("blocked-missing-registry")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_substrate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine substrate readiness gates
- capability state
- process evidence
- VM and renderer gates
- hello.exe gate
- full Wine gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
