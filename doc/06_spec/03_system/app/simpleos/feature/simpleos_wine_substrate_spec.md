# Simpleos Wine Substrate Specification

> Tests covering SimpleOS Wine Substrate, REQ-001: capability matrix, REQ-002: process-backed app baseline, REQ-005: VM and container support, REQ-006: X11-class renderer and WM backend, REQ-003 and REQ-004: host ABI, thread, and dynamic loading, REQ-007: PE/COFF loader preparation, REQ-009: nogc async substrate, REQ-008: non-GUI hello.exe milestone, REQ-010: full Wine readiness boundary, REQ-011: Wine process-session handoff, REQ-012: controlled Wine process-session execution, REQ-013: arbitrary process image validation boundary, REQ-014: arbitrary process import inspection boundary, REQ-015: bounded process import binding plan, REQ-016: guarded process import thunk patch plan, REQ-017: process CPU dispatch preflight.

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
#### should require evidence before a row can be verified

- should require evidence before a row can be verified
   - Expected: state equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require evidence before a row can be verified")
val state = wine_substrate_verify_capability("pthread", "")
expect(state).to_equal("partial")
```

</details>

#### should link verified capability rows to implementation paths and evidence commands

- should link verified capability rows to implementation paths and evidence commands
   - Expected: row.state equals `verified`
   - Expected: row.implementation_path equals `src/lib/common/wine_nt_bridge.spl`
   - Expected: exec_env.state equals `verified`
   - Expected: registry.state equals `verified`
   - Expected: user32.state equals `verified`
   - Expected: gdi32.state equals `verified`
   - Expected: kernel32_core.state equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("audio", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("audio", "host=verified") equals `missing`
   - Expected: matrix.len() equals `21`
   - Expected: matrix[1].capability equals `exec_env`
   - Expected: matrix[5].capability equals `user32`
   - Expected: matrix[6].capability equals `gdi32`
   - Expected: matrix[7].capability equals `kernel32_core`
   - Expected: matrix[9].capability equals `fs_semantics`
   - Expected: matrix[10].capability equals `ipc_wait`
   - Expected: matrix[11].capability equals `registry`
   - Expected: matrix[15].capability equals `fonts`
   - Expected: matrix[20].capability equals `hello_exe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should link verified capability rows to implementation paths and evidence commands")
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

- should reject resident fallback as complete evidence
   - Expected: result equals `resident-fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject resident fallback as complete evidence")
val result = wine_substrate_check_process_evidence("[desktop-e2e] process-backed:resident")
expect(result).to_equal("resident-fallback")
```

</details>

#### should require Browser Demo, Hello World, Editor, Terminal, and File Manager process markers

- should require Browser Demo, Hello World, Editor, Terminal, and File Manager process markers
   - Expected: wine_substrate_check_process_evidence(partial) equals `insufficient-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require Browser Demo, Hello World, Editor, Terminal, and File Manager process markers")
val partial = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3"
expect(wine_substrate_check_process_evidence(partial)).to_equal("insufficient-evidence")
```

</details>

### REQ-005: VM and container support

#### should require full SimpleOS executable-environment evidence

- should require full SimpleOS executable-environment evidence
   - Expected: wine_substrate_exec_env_gate(partial) equals `missing-simpleos-vmspace`
   - Expected: wine_substrate_exec_env_gate_from_serial_log(serial_log) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require full SimpleOS executable-environment evidence")
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

- should require fixed mappings, guard pages, and permission changes
   - Expected: result equals `missing-mprotect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require fixed mappings, guard pages, and permission changes")
val result = wine_substrate_vm_gate("reserve commit unmap fixed-map")
expect(result).to_equal("missing-mprotect")
```

</details>

### REQ-006: X11-class renderer and WM backend

#### should require window lifecycle, expose, input, and clipboard coverage

- should require window lifecycle, expose, input, and clipboard coverage
   - Expected: result equals `missing-atom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require window lifecycle, expose, input, and clipboard coverage")
val features = "display screen window map-unmap configure surface damage clip expose present input focus cursor"
val result = wine_substrate_renderer_gate(features)
expect(result).to_equal("missing-atom")
```

</details>

### REQ-003 and REQ-004: host ABI, thread, and dynamic loading

#### should require the remaining Wine host substrate features

- should require the remaining Wine host substrate features
   - Expected: result equals `missing-fs-attrs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the remaining Wine host substrate features")
val features = "fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv spawn fs-paths"
val result = wine_substrate_host_gate(features)
expect(result).to_equal("missing-fs-attrs")
```

</details>

### REQ-007: PE/COFF loader preparation

#### should require safe PE validation before execution

- should require safe PE validation before execution
   - Expected: result equals `missing-section-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require safe PE validation before execution")
val result = wine_substrate_pe_gate("mz pe-signature machine-x86_64 pe32plus")
expect(result).to_equal("missing-section-bounds")
```

</details>

### REQ-009: nogc async substrate

<details>
<summary>Advanced: should require the existing nogc_async_mut completion and event-loop primitives</summary>

#### should require the existing nogc_async_mut completion and event-loop primitives

- should require the existing nogc_async_mut completion and event-loop primitives
   - Expected: result equals `missing-submit-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the existing nogc_async_mut completion and event-loop primitives")
val features = "nogc-future poll waker io-driver submit-open submit-read"
val result = wine_substrate_async_gate(features)
expect(result).to_equal("missing-submit-write")
```

</details>


</details>

### REQ-008: non-GUI hello.exe milestone

#### should keep hello.exe blocked until substrate gates are verified

- should keep hello.exe blocked until substrate gates are verified
   - Expected: gate_state equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep hello.exe blocked until substrate gates are verified")
val gate_state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified")
expect(gate_state).to_equal("blocked")
```

</details>

#### should keep hello.exe blocked until the modeled NT bridge is verified

- should keep hello.exe blocked until the modeled NT bridge is verified
   - Expected: gate_state equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep hello.exe blocked until the modeled NT bridge is verified")
val gate_state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified")
expect(gate_state).to_equal("blocked")
```

</details>

#### should not execute malformed hello.exe bytes even when gates are declared verified

- should not execute malformed hello.exe bytes even when gates are declared verified
   - Expected: result.status equals `rejected`
   - Expected: result.error equals `too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not execute malformed hello.exe bytes even when gates are declared verified")
val gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
val result = wine_hello_exe_probe(_zero_pe_bytes(0), gates)
expect(result.status).to_equal("rejected")
expect(result.error).to_equal("too-small")
```

</details>

### REQ-010: full Wine readiness boundary

#### should distinguish controlled hello.exe readiness from full Wine readiness

- should distinguish controlled hello.exe readiness from full Wine readiness
   - Expected: wine_substrate_hello_exe_gate(hello_gates) equals `ready`
   - Expected: wine_substrate_full_wine_gate(hello_gates) equals `blocked-missing-renderer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should distinguish controlled hello.exe readiness from full Wine readiness")
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_hello_exe_gate(hello_gates)).to_equal("ready")
expect(wine_substrate_full_wine_gate(hello_gates)).to_equal("blocked-missing-renderer")
```

</details>

#### should require all tracked Wine substrate rows for the full Wine gate

- should require all tracked Wine substrate rows for the full Wine gate
   - Expected: wine_substrate_full_wine_gate(gates) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require all tracked Wine substrate rows for the full Wine gate")
val gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_full_wine_gate(gates)).to_equal("ready")
```

</details>

### REQ-011: Wine process-session handoff

#### should keep arbitrary exe sessions blocked until full Wine readiness

- should keep arbitrary exe sessions blocked until full Wine readiness
   - Expected: arbitrary.ok is false
   - Expected: arbitrary.error equals `blocked-missing-renderer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep arbitrary exe sessions blocked until full Wine readiness")
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
val arbitrary = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\"), hello_gates)
expect(arbitrary.ok).to_equal(false)
expect(arbitrary.error).to_equal("blocked-missing-renderer")
```

</details>

#### should emit a dry-run handoff for the controlled hello path

- should emit a dry-run handoff for the controlled hello path
   - Expected: handoff.ok is true
   - Expected: handoff.substrate_readiness equals `controlled-hello-ready`
   - Expected: handoff.status equals `dry-run-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit a dry-run handoff for the controlled hello path")
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

- should execute only the verified hello.exe process session
   - Expected: execution.ok is true
   - Expected: execution.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: execution.exit_code equals `0`
   - Expected: execution.status equals `executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute only the verified hello.exe process session")
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

- should not treat full-Wine planning as arbitrary executable support
   - Expected: execution.ok is false
   - Expected: execution.error equals `unsupported-process-session`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not treat full-Wine planning as arbitrary executable support")
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val execution = wine_process_execute_controlled_hello(plan)
expect(execution.ok).to_equal(false)
expect(execution.error).to_equal("unsupported-process-session")
```

</details>

### REQ-013: arbitrary process image validation boundary

#### should validate PE image structure before future arbitrary execution

- should validate PE image structure before future arbitrary execution
   - Expected: image.ok is true
   - Expected: image.machine equals `x86_64`
   - Expected: image.subsystem equals `console`
   - Expected: image.status equals `image-validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate PE image structure before future arbitrary execution")
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

- should reject malformed images at the process-session boundary
   - Expected: image.ok is false
   - Expected: image.error equals `too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject malformed images at the process-session boundary")
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val image = wine_process_validate_full_image(plan, _zero_pe_bytes(0))
expect(image.ok).to_equal(false)
expect(image.error).to_equal("too-small")
```

</details>

### REQ-014: arbitrary process import inspection boundary

#### should inspect bounded first-import DLL and symbols before future binding

- should inspect bounded first-import DLL and symbols before future binding
   - Expected: imports.ok is true
   - Expected: imports.dll_name equals `KERNEL32.dll`
   - Expected: imports.symbol_count equals `3`
   - Expected: imports.symbols[0] equals `GetStdHandle`
   - Expected: imports.symbols[1] equals `WriteFile`
   - Expected: imports.symbols[2] equals `ExitProcess`
   - Expected: imports.status equals `imports-inspected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should inspect bounded first-import DLL and symbols before future binding")
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

- should keep import inspection bounded
   - Expected: imports.ok is false
   - Expected: imports.error equals `invalid-symbol-limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep import inspection bounded")
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val imports = wine_process_inspect_full_imports(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(imports.ok).to_equal(false)
expect(imports.error).to_equal("invalid-symbol-limit")
```

</details>

### REQ-015: bounded process import binding plan

#### should plan supported KERNEL32 import bindings before execution

- should plan supported KERNEL32 import bindings before execution
   - Expected: bindings.ok is true
   - Expected: bindings.dll_name equals `kernel32.dll`
   - Expected: bindings.call_sequence equals `GetStdHandle WriteFile ExitProcess`
   - Expected: bindings.binding_count equals `3`
   - Expected: bindings.status equals `imports-bound`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should plan supported KERNEL32 import bindings before execution")
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

- should reject unbounded or incomplete import binding attempts
   - Expected: bindings.ok is false
   - Expected: bindings.error equals `import-thunk-limit-exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unbounded or incomplete import binding attempts")
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val bindings = wine_process_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 1)
expect(bindings.ok).to_equal(false)
expect(bindings.error).to_equal("import-thunk-limit-exceeded")
```

</details>

### REQ-016: guarded process import thunk patch plan

#### should produce import-thunk evidence only after supported binding

- should produce import-thunk evidence only after supported binding
   - Expected: patches.ok is true
   - Expected: patches.patch_count equals `3`
   - Expected: patches.status equals `thunk-patch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce import-thunk evidence only after supported binding")
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

- should reject thunk patch planning when binding is rejected
   - Expected: patches.ok is false
   - Expected: patches.error equals `import-thunk-limit-exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject thunk patch planning when binding is rejected")
val full_gates = "process=verified exec_env=verified vm=verified renderer=verified user32=verified gdi32=verified kernel32_core=verified host=verified posix=verified registry=verified pthread=verified dynload=verified audio=verified fonts=verified input=verified pe_loader=verified async=verified nt_bridge=verified"
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), full_gates)
val patches = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 1)
expect(patches.ok).to_equal(false)
expect(patches.error).to_equal("import-thunk-limit-exceeded")
```

</details>

### REQ-017: process CPU dispatch preflight

#### should require process loader evidence and CPU dispatch evidence before future execution

- should require process loader evidence and CPU dispatch evidence before future execution
   - Expected: preflight.ok is true
   - Expected: preflight.status equals `cpu-preflight-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require process loader evidence and CPU dispatch evidence before future execution")
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

- should block process CPU dispatch preflight when CPU evidence is missing
   - Expected: preflight.ok is false
   - Expected: preflight.error equals `missing-thread-context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block process CPU dispatch preflight when CPU evidence is missing")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine Substrate, REQ-001: capability matrix, REQ-002: process-backed app baseline, REQ-005: VM and container support, REQ-006: X11-class renderer and WM backend, REQ-003 and REQ-004: host ABI, thread, and dynamic loading, REQ-007: PE/COFF loader preparation, REQ-009: nogc async substrate, REQ-008: non-GUI hello.exe milestone, REQ-010: full Wine readiness boundary, REQ-011: Wine process-session handoff, REQ-012: controlled Wine process-session execution, REQ-013: arbitrary process image validation boundary, REQ-014: arbitrary process import inspection boundary, REQ-015: bounded process import binding plan, REQ-016: guarded process import thunk patch plan, REQ-017: process CPU dispatch preflight.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-005`
- `REQ-006`
- `REQ-003`
- `REQ-004`
- `REQ-007`
- `REQ-009`
- `REQ-008`
- `REQ-010`
- `REQ-011`
- `REQ-012`
- `REQ-013`
- `REQ-014`
- `REQ-015`
- `REQ-016`
- `REQ-017`
- `REQ-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7087c18673457308e9fd87fecc31b0718f06f5bfa21ab588e0c132f530c8c179`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7087c18673457308e9fd87fecc31b0718f06f5bfa21ab588e0c132f530c8c179`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7087c18673457308e9fd87fecc31b0718f06f5bfa21ab588e0c132f530c8c179`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 17 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should classify missing Wine substrate capability rows explicitly' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify missing Wine substrate capability rows explicitly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require evidence before a row can be verified' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require evidence before a row can be verified' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should link verified capability rows to implementation paths and evidence commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should link verified capability rows to implementation paths and evidence commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject resident fallback as complete evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require Browser Demo, Hello World, Editor, Terminal, and File Manager process markers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require full SimpleOS executable-environment evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_substrate_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require full SimpleOS executable-environment evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
