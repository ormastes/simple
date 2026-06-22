# Simpleos Wine Substrate Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_substrate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_substrate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_substrate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_substrate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Substrate Specification

## Scenarios

### SimpleOS Wine Substrate

### REQ-001: capability matrix

#### should classify missing Wine substrate capability rows explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_substrate_capability_state("pthread")
expect(state).to_equal("partial")
expect(wine_substrate_capability_state("audio")).to_equal("missing")
expect(wine_substrate_capability_state("fonts")).to_equal("missing")
expect(wine_substrate_capability_state("input")).to_equal("missing")
expect(wine_substrate_capability_state("registry")).to_equal("partial")
expect(wine_substrate_capability_state("user32")).to_equal("partial")
expect(wine_substrate_capability_state("gdi32")).to_equal("partial")
expect(wine_substrate_capability_state("kernel32_core")).to_equal("partial")
```

</details>

#### should require evidence before a row can be verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_substrate_verify_capability("pthread", "")
expect(state).to_equal("partial")
```

</details>

#### should link verified capability rows to implementation paths and evidence commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gates = "process=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified pthread=verified dynload=verified registry=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val row = wine_substrate_capability_row("nt_bridge", gates)
expect(row.state).to_equal("verified")
expect(row.implementation_path).to_equal("src/lib/common/wine_nt_bridge.spl")
expect(row.evidence_command).to_contain("wine_nt_bridge_spec")
val exec_env = wine_substrate_capability_row("exec_env", gates + " exec_env=verified")
expect(exec_env.state).to_equal("verified")
expect(exec_env.evidence_command).to_contain("wine_simpleos_exec_env_gate_spec")
val registry = wine_substrate_capability_row("registry", gates)
expect(registry.state).to_equal("verified")
expect(registry.evidence_command).to_contain("wine_advapi32_registry_spec")
val user32 = wine_substrate_capability_row("user32", gates)
expect(user32.state).to_equal("verified")
expect(user32.evidence_command).to_contain("wine_user32_window_spec")
val gdi32 = wine_substrate_capability_row("gdi32", gates)
expect(gdi32.state).to_equal("verified")
expect(gdi32.evidence_command).to_contain("wine_gdi32_drawing_spec")
val kernel32_core = wine_substrate_capability_row("kernel32_core", gates)
expect(kernel32_core.state).to_equal("verified")
expect(kernel32_core.evidence_command).to_contain("wine_kernel32_heap_spec")
expect(wine_substrate_capability_state_from_gates("audio", gates)).to_equal("verified")
expect(wine_substrate_capability_state_from_gates("audio", "host=verified")).to_equal("missing")
val matrix = wine_substrate_capability_matrix(gates)
expect(matrix.len()).to_equal(21)
expect(matrix[1].capability).to_equal("exec_env")
expect(matrix[5].capability).to_equal("user32")
expect(matrix[6].capability).to_equal("gdi32")
expect(matrix[7].capability).to_equal("kernel32_core")
expect(matrix[9].capability).to_equal("fs_semantics")
expect(matrix[10].capability).to_equal("ipc_wait")
expect(matrix[11].capability).to_equal("registry")
expect(matrix[15].capability).to_equal("fonts")
expect(matrix[20].capability).to_equal("hello_exe")
```

</details>

### REQ-002: process-backed app baseline

#### should reject resident fallback as complete evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_substrate_check_process_evidence("[desktop-e2e] process-backed:resident")
expect(result).to_equal("resident-fallback")
```

</details>

#### should require Browser Demo, Hello World, Editor, Terminal, and File Manager process markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val partial = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3"
expect(wine_substrate_check_process_evidence(partial)).to_equal("insufficient-evidence")
```

</details>

### REQ-005: VM and container support

#### should require full SimpleOS executable-environment evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
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
    "[desktop-e2e] mdsoc-capsule:ok owner=process-container-wm\n" +
    "[desktop-e2e] mdsoc-public-port:ok facade=exec-env\n" +
    "[desktop-e2e] mdsoc-resident-state-owner:ok ecs=wm,process,container\n" +
    "TEST PASSED"
expect(wine_substrate_exec_env_gate_from_serial_log(serial_log)).to_equal("ready")
```

</details>

#### should require fixed mappings, guard pages, and permission changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_substrate_vm_gate("reserve commit unmap fixed-map")
expect(result).to_equal("missing-mprotect")
```

</details>

### REQ-006: X11-class renderer and WM backend

#### should require window lifecycle, expose, input, and clipboard coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "display screen window map-unmap configure surface damage clip expose present input focus cursor"
val result = wine_substrate_renderer_gate(features)
expect(result).to_equal("missing-atom")
```

</details>

### REQ-003 and REQ-004: host ABI, thread, and dynamic loading

#### should require the remaining Wine host substrate features

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv spawn fs-paths"
val result = wine_substrate_host_gate(features)
expect(result).to_equal("missing-fs-attrs")
```

</details>

### REQ-007: PE/COFF loader preparation

#### should require safe PE validation before execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_substrate_pe_gate("mz pe-signature machine-x86_64 pe32plus")
expect(result).to_equal("missing-section-bounds")
```

</details>

### REQ-009: nogc async substrate

<details>
<summary>Advanced: should require the existing nogc_async_mut completion and event-loop primitives</summary>

#### should require the existing nogc_async_mut completion and event-loop primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "nogc-future poll waker io-driver submit-open submit-read"
val result = wine_substrate_async_gate(features)
expect(result).to_equal("missing-submit-write")
```

</details>


</details>

### REQ-008: non-GUI hello.exe milestone

#### should keep hello.exe blocked until substrate gates are verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate_state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified")
expect(gate_state).to_equal("blocked")
```

</details>

#### should keep hello.exe blocked until the modeled NT bridge is verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate_state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified")
expect(gate_state).to_equal("blocked")
```

</details>

#### should not execute malformed hello.exe bytes even when gates are declared verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
val result = wine_hello_exe_probe(_zero_pe_bytes(0), gates)
expect(result.status).to_equal("rejected")
expect(result.error).to_equal("too-small")
```

</details>

### REQ-010: full Wine readiness boundary

#### should distinguish controlled hello.exe readiness from full Wine readiness

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

#### should require all tracked Wine substrate rows for the full Wine gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_full_wine_gate(gates)).to_equal("ready")
```

</details>

### REQ-011: Wine process-session handoff

#### should keep arbitrary exe sessions blocked until full Wine readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
val arbitrary = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\"), hello_gates)
expect(arbitrary.ok).to_equal(false)
expect(arbitrary.error).to_equal("blocked-missing-renderer")
```

</details>

#### should emit a dry-run handoff for the controlled hello path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), hello_gates)
val handoff = wine_process_launch_handoff(plan, true)
expect(handoff.ok).to_equal(true)
expect(handoff.substrate_readiness).to_equal("controlled-hello-ready")
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

### REQ-012: controlled Wine process-session execution

#### should execute only the verified hello.exe process session

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), hello_gates)
val execution = wine_process_execute_controlled_hello(plan)
expect(execution.ok).to_equal(true)
expect(execution.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(execution.exit_code).to_equal(0)
expect(execution.status).to_equal("executed")
```

</details>

#### should not treat full-Wine planning as arbitrary executable support

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val execution = wine_process_execute_controlled_hello(plan)
expect(execution.ok).to_equal(false)
expect(execution.error).to_equal("unsupported-process-session")
```

</details>

### REQ-013: arbitrary process image validation boundary

#### should validate PE image structure before future arbitrary execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val image = wine_process_validate_full_image(plan, wine_known_hello_exe_fixture_bytes())
expect(image.ok).to_equal(true)
expect(image.machine).to_equal("x86_64")
expect(image.subsystem).to_equal("console")
expect(image.status).to_equal("image-validated")
```

</details>

#### should reject malformed images at the process-session boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val image = wine_process_validate_full_image(plan, _zero_pe_bytes(0))
expect(image.ok).to_equal(false)
expect(image.error).to_equal("too-small")
```

</details>

### REQ-014: arbitrary process import inspection boundary

#### should inspect bounded first-import DLL and symbols before future binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val imports = wine_process_inspect_full_imports(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(imports.ok).to_equal(true)
expect(imports.dll_name).to_equal("KERNEL32.dll")
expect(imports.symbol_count).to_equal(3)
expect(imports.symbols[0]).to_equal("GetStdHandle")
expect(imports.symbols[1]).to_equal("WriteFile")
expect(imports.symbols[2]).to_equal("ExitProcess")
expect(imports.status).to_equal("imports-inspected")
```

</details>

#### should keep import inspection bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val imports = wine_process_inspect_full_imports(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(imports.ok).to_equal(false)
expect(imports.error).to_equal("invalid-symbol-limit")
```

</details>

### REQ-015: bounded process import binding plan

#### should plan supported KERNEL32 import bindings before execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val bindings = wine_process_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(bindings.ok).to_equal(true)
expect(bindings.dll_name).to_equal("kernel32.dll")
expect(bindings.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(bindings.binding_count).to_equal(3)
expect(bindings.status).to_equal("imports-bound")
```

</details>

#### should reject unbounded or incomplete import binding attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val bindings = wine_process_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 1)
expect(bindings.ok).to_equal(false)
expect(bindings.error).to_equal("import-thunk-limit-exceeded")
```

</details>

### REQ-016: guarded process import thunk patch plan

#### should produce import-thunk evidence only after supported binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val patches = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(patches.ok).to_equal(true)
expect(patches.patch_count).to_equal(3)
expect(patches.evidence).to_contain("import-thunks-bound")
expect(patches.evidence).to_contain("import-thunk-table-valid")
expect(patches.evidence).to_contain("import-thunk-symbols-resolved")
expect(patches.evidence).to_contain("import-thunk-bindings-match")
expect(patches.evidence).to_contain("import-thunk-iat-guarded")
expect(patches.status).to_equal("thunk-patch-planned")
```

</details>

#### should reject thunk patch planning when binding is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val patches = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 1)
expect(patches.ok).to_equal(false)
expect(patches.error).to_equal("import-thunk-limit-exceeded")
```

</details>

### REQ-017: process CPU dispatch preflight

#### should require process loader evidence and CPU dispatch evidence before future execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val preflight = wine_process_cpu_dispatch_preflight(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(preflight.ok).to_equal(true)
expect(preflight.evidence).to_contain("import-thunk-bytes-written")
expect(preflight.evidence).to_contain("import-thunk-iat-guarded")
expect(preflight.evidence).to_contain("x86_64-dispatch")
expect(preflight.evidence).to_contain("process-image-mapped")
expect(preflight.evidence).to_contain("os-vma")
expect(preflight.evidence).to_contain("process-vma-write-window")
expect(preflight.evidence).to_contain("process-vma-rx-restored")
expect(preflight.evidence).to_contain("no-host-code-jump")
expect(preflight.status).to_equal("cpu-preflight-ready")
```

</details>

#### should block process CPU dispatch preflight when CPU evidence is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val preflight = wine_process_cpu_dispatch_preflight(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(preflight.ok).to_equal(false)
expect(preflight.error).to_equal("missing-thread-context")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine Substrate
- REQ-001: capability matrix
- REQ-002: process-backed app baseline
- REQ-005: VM and container support
- REQ-006: X11-class renderer and WM backend
- REQ-003 and REQ-004: host ABI, thread, and dynamic loading
- REQ-007: PE/COFF loader preparation
- REQ-009: nogc async substrate
- REQ-008: non-GUI hello.exe milestone
- REQ-010: full Wine readiness boundary
- REQ-011: Wine process-session handoff
- REQ-012: controlled Wine process-session execution
- REQ-013: arbitrary process image validation boundary
- REQ-014: arbitrary process import inspection boundary
- REQ-015: bounded process import binding plan
- REQ-016: guarded process import thunk patch plan
- REQ-017: process CPU dispatch preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
