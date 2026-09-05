# Wine Substrate Specification

> Tests covering Wine substrate readiness gates, capability state, process evidence, VM and renderer gates, hello.exe gate, full Wine gate.

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

- reports completed research without claiming platform readiness
   - Expected: wine_substrate_capability_state("research") equals `verified`
   - Expected: wine_substrate_capability_state("exec_env") equals `partial`
   - Expected: wine_substrate_capability_state("pe_loader") equals `partial`
   - Expected: wine_substrate_capability_state("pthread") equals `partial`
   - Expected: wine_substrate_capability_state("dynload") equals `partial`
   - Expected: wine_substrate_capability_state("registry") equals `partial`
   - Expected: wine_substrate_capability_state("user32") equals `partial`
   - Expected: wine_substrate_capability_state("gdi32") equals `partial`
   - Expected: wine_substrate_capability_state("kernel32_core") equals `partial`
   - Expected: wine_substrate_capability_state("audio") equals `missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports completed research without claiming platform readiness")
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

- does not verify unfinished rows just because evidence text exists
   - Expected: state equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not verify unfinished rows just because evidence text exists")
val state = wine_substrate_verify_capability("pthread", "doc/some-evidence.md")
expect(state).to_equal("partial")
```

</details>

#### derives verified capability rows from explicit gate evidence

- derives verified capability rows from explicit gate evidence
   - Expected: wine_substrate_capability_state_from_gates("pthread", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("fs_semantics", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("user32", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("gdi32", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("kernel32_core", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("registry", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("audio", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("fonts", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("input", gates) equals `verified`
   - Expected: wine_substrate_capability_state_from_gates("audio", "host=verified") equals `missing`
   - Expected: wine_substrate_capability_state_from_gates("hello_exe", gates) equals `verified`
   - Expected: posix.state equals `verified`
   - Expected: row.state equals `verified`
   - Expected: row.implementation_path equals `src/lib/common/wine_nt_bridge.spl`
   - Expected: row.evidence_command equals `bin/simple test test/unit/lib/common/wine_nt_bridge_spec.spl --mode=interpret... (full value in folded executable source)`
   - Expected: exec_env.state equals `verified`
   - Expected: exec_env.evidence_command equals `bin/simple test test/unit/lib/common/wine_simpleos_exec_env_gate_spec.spl --m... (full value in folded executable source)`
   - Expected: pe_loader.state equals `verified`
   - Expected: user32.state equals `verified`
   - Expected: gdi32.state equals `verified`
   - Expected: kernel32_core.state equals `verified`
   - Expected: dynload.state equals `verified`
   - Expected: pthread.state equals `verified`
   - Expected: ipc.state equals `verified`
   - Expected: registry.state equals `verified`
   - Expected: registry.implementation_path equals `src/lib/common/wine_advapi32_registry.spl`
   - Expected: audio.state equals `verified`
   - Expected: audio.evidence_command equals `bin/simple test test/unit/lib/common/wine_service_adapter_spec.spl --mode=int... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives verified capability rows from explicit gate evidence")
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

- lists explicit matrix rows for modeled Wine preconditions
   - Expected: matrix.len() equals `21`
   - Expected: matrix[0].capability equals `process`
   - Expected: matrix[1].capability equals `exec_env`
   - Expected: matrix[5].capability equals `user32`
   - Expected: matrix[6].capability equals `gdi32`
   - Expected: matrix[7].capability equals `kernel32_core`
   - Expected: matrix[9].capability equals `fs_semantics`
   - Expected: matrix[10].capability equals `ipc_wait`
   - Expected: matrix[11].capability equals `registry`
   - Expected: matrix[15].capability equals `fonts`
   - Expected: matrix[19].capability equals `nt_bridge`
   - Expected: matrix[20].state equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists explicit matrix rows for modeled Wine preconditions")
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

- rejects resident fallback markers
   - Expected: result equals `resident-fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects resident fallback markers")
val result = wine_substrate_check_process_evidence("[desktop-e2e] process-backed:resident")
expect(result).to_equal("resident-fallback")
```

</details>

#### requires all baseline process-backed app markers

- requires all baseline process-backed app markers
   - Expected: wine_substrate_check_process_evidence(log) equals `process-backed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires all baseline process-backed app markers")
val log = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3\n" +
    "[desktop-e2e] process-backed:ok app=terminal pid=4\n" +
    "[desktop-e2e] process-backed:ok app=file_manager pid=5"
expect(wine_substrate_check_process_evidence(log)).to_equal("process-backed")
```

</details>

#### rejects partial process-backed evidence without terminal and file manager

- rejects partial process-backed evidence without terminal and file manager
   - Expected: wine_substrate_check_process_evidence(log) equals `insufficient-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects partial process-backed evidence without terminal and file manager")
val log = "[desktop-e2e] process-backed:ok app=browser_demo pid=1\n" +
    "[desktop-e2e] process-backed:ok app=hello_world pid=2\n" +
    "[desktop-e2e] process-backed:ok app=editor pid=3"
expect(wine_substrate_check_process_evidence(log)).to_equal("insufficient-evidence")
```

</details>

### VM and renderer gates

#### reports full-OS executable environment gaps before Wine readiness

- reports full-OS executable environment gaps before Wine readiness
   - Expected: wine_substrate_exec_env_gate(partial) equals `missing-simpleos-vmspace`
   - Expected: wine_substrate_exec_env_gate_from_serial_log(serial_log) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports full-OS executable environment gaps before Wine readiness")
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

- reports the first missing VM requirement
   - Expected: wine_substrate_vm_gate("reserve commit unmap fixed-map") equals `missing-mprotect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing VM requirement")
expect(wine_substrate_vm_gate("reserve commit unmap fixed-map")).to_equal("missing-mprotect")
```

</details>

#### reports renderer backend gaps in X11-class behavior

- reports renderer backend gaps in X11-class behavior
   - Expected: wine_substrate_renderer_gate(features) equals `missing-atom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports renderer backend gaps in X11-class behavior")
val features = "display screen window map-unmap configure surface damage clip expose present input focus cursor"
expect(wine_substrate_renderer_gate(features)).to_equal("missing-atom")
```

</details>

#### reports host substrate gaps for all other Wine features

- reports host substrate gaps for all other Wine features
   - Expected: wine_substrate_host_gate(features) equals `missing-fs-attrs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports host substrate gaps for all other Wine features")
val features = "fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv spawn fs-paths"
expect(wine_substrate_host_gate(features)).to_equal("missing-fs-attrs")
```

</details>

#### reports PE loader preparation gaps before hello.exe

- reports PE loader preparation gaps before hello.exe
   - Expected: wine_substrate_pe_gate(features) equals `missing-section-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports PE loader preparation gaps before hello.exe")
val features = "mz pe-signature machine-x86_64 pe32plus"
expect(wine_substrate_pe_gate(features)).to_equal("missing-section-bounds")
```

</details>

#### requires nogc async primitives for Wine async readiness

- requires nogc async primitives for Wine async readiness
   - Expected: wine_substrate_async_gate(features) equals `missing-submit-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires nogc async primitives for Wine async readiness")
val features = "nogc-future poll waker io-driver submit-open submit-read"
expect(wine_substrate_async_gate(features)).to_equal("missing-submit-write")
```

</details>

### hello.exe gate

#### blocks hello.exe until substrate gates are verified

- blocks hello.exe until substrate gates are verified
   - Expected: state equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks hello.exe until substrate gates are verified")
val state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified")
expect(state).to_equal("blocked")
```

</details>

#### still blocks hello.exe until the modeled NT bridge is verified

- still blocks hello.exe until the modeled NT bridge is verified
   - Expected: state equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still blocks hello.exe until the modeled NT bridge is verified")
val state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified")
expect(state).to_equal("blocked")
```

</details>

#### allows hello.exe only after async and NT bridge gates are verified too

- allows hello.exe only after async and NT bridge gates are verified too
   - Expected: state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows hello.exe only after async and NT bridge gates are verified too")
val state = wine_substrate_hello_exe_gate("process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified")
expect(state).to_equal("ready")
```

</details>

### full Wine gate

#### does not treat controlled hello.exe readiness as full Wine readiness

- does not treat controlled hello.exe readiness as full Wine readiness
   - Expected: wine_substrate_hello_exe_gate(hello_gates) equals `ready`
   - Expected: wine_substrate_full_wine_gate(hello_gates) equals `blocked-missing-renderer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat controlled hello.exe readiness as full Wine readiness")
val hello_gates = "process=verified exec_env=verified vm=verified host=verified posix=verified pthread=verified dynload=verified pe_loader=verified async=verified nt_bridge=verified"
expect(wine_substrate_hello_exe_gate(hello_gates)).to_equal("ready")
expect(wine_substrate_full_wine_gate(hello_gates)).to_equal("blocked-missing-renderer")
```

</details>

#### requires every tracked Wine substrate row before full Wine readiness

- requires every tracked Wine substrate row before full Wine readiness
   - Expected: wine_substrate_full_wine_gate(gates) equals `ready`
   - Expected: wine_substrate_full_wine_gate(missing_registry) equals `blocked-missing-registry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires every tracked Wine substrate row before full Wine readiness")
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
| Source | `test/unit/lib/common/wine_substrate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine substrate readiness gates, capability state, process evidence, VM and renderer gates, hello.exe gate, full Wine gate.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e0cfb3b9c3f5d12579564cd643b99d7d3edae0b39e09832394fef4528cc15c11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0cfb3b9c3f5d12579564cd643b99d7d3edae0b39e09832394fef4528cc15c11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0cfb3b9c3f5d12579564cd643b99d7d3edae0b39e09832394fef4528cc15c11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_substrate_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_substrate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_substrate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_substrate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_substrate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_substrate_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports completed research without claiming platform readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_substrate_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not verify unfinished rows just because evidence text exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_substrate_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives verified capability rows from explicit gate evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
