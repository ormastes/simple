# simpleos_arm64_native_link_contract_spec

> ARM64 SimpleOS native link ownership contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_arm64_native_link_contract_spec

ARM64 SimpleOS native link ownership contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_arm64_native_link_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

ARM64 SimpleOS native link ownership contract.

## Scenarios

### SimpleOS ARM64 native linker

#### keeps the host GPU daemon out of the compiler CLI closure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the host GPU daemon out of the compiler CLI closure
   - Expected: daemon does not contain `app.io.cli_ops`
   - Expected: args_owner does not contain `rt_cli_arg_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the host GPU daemon out of the compiler CLI closure")
val entry = file_read("src/app/simpleos_gpu_host/main.spl")
val daemon = file_read("src/app/simpleos_gpu_host/daemon_runner.spl")
val args_owner = file_read("src/app/io/args_ops.spl")
expect(entry).to_contain("app.simpleos_gpu_host.daemon_runner")
expect(entry).to_contain("simpleos_gpu_host_run(SimpleOsGpuHostAllPlatform.create())")
expect(daemon.contains("app.io.cli_ops")).to_equal(false)
expect(args_owner).to_contain("extern fn rt_cli_get_args() -> [text]")
expect(args_owner.contains("rt_cli_arg_count")).to_equal(false)
```

</details>

#### dispatches freestanding ARM64 builds to the real boot owners

- dispatches freestanding ARM64 builds to the real boot owners
   - Expected: source does not contain `simpleos_arm64_link_stubs.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches freestanding ARM64 builds to the real boot owners")
val source = compiler_native_link_source()
expect(source).to_contain("if is_simpleos_arm64_link(output):")
expect(source).to_contain("examples/09_embedded/simple_os/arch/arm64/boot/crt0.S")
expect(source).to_contain("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_LINKER_SCRIPT")
expect(source).to_contain("SimpleOS ARM64 freestanding link failed")
expect(source).to_contain("simpleos_spl_start_symbol(user_objects)")
expect(source).to_contain("--defsym=spl_start={spl_start}")
expect(source.contains("simpleos_arm64_link_stubs.c")).to_equal(false)
```

</details>

#### keeps every host GPU probe out of generic whole-tree discovery

- keeps every host GPU probe out of generic whole-tree discovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps every host GPU probe out of generic whole-tree discovery")
val runner = file_read("src/os/_QemuRunner/os_build_run.spl")
expect(runner).to_contain("if _is_host_gpu_probe_target(target):")
expect(runner).to_contain("target.entry.ends_with(\"/host_gpu_smoke_entry.spl\")")
expect(runner).to_contain("[\"build/os/generated\", \"src/os\", \"src/lib\", \"examples/09_embedded/simple_os\"]")
```

</details>

#### links the RV64 host GPU probe with the real freestanding runtime

- links the RV64 host GPU probe with the real freestanding runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("links the RV64 host GPU probe with the real freestanding runtime")
val source = compiler_native_link_source()
expect(source).to_contain("val uses_freestanding_runtime = is_display_smoke or output.contains(\"simpleos_riscv64_host_gpu_probe\")")
expect(source).to_contain("if uses_freestanding_runtime:")
expect(source).to_contain("if not uses_freestanding_runtime:")
expect(source).to_contain("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
expect(source).to_contain("val linker_script = if configured_script != \"\": configured_script")
```

</details>

#### enables minimal boot mode for host GPU targets

- enables minimal boot mode for host GPU targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables minimal boot mode for host GPU targets")
val runner = file_read("src/os/_QemuRunner/os_build_run.spl")
expect(runner).to_contain("_is_riscv64_live_helper_target(target) or _is_host_gpu_probe_target(target):")
```

</details>

#### keeps one ABI-correct real RV64 TLB invalidation owner

- keeps one ABI-correct real RV64 TLB invalidation owner
   - Expected: runtime does not contain `void rt_invlpg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps one ABI-correct real RV64 TLB invalidation owner")
val runtime = file_read("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
expect(runtime).to_contain("spl_i64 rt_invlpg(spl_i64 addr)")
expect(runtime).to_contain("sfence.vma %0, zero")
expect(runtime).to_contain("fence rw, rw")
expect(runtime.contains("void rt_invlpg")).to_equal(false)
```

</details>

#### terminates RV64 through OpenSBI instead of a generated runtime exit

- terminates RV64 through OpenSBI instead of a generated runtime exit
   - Expected: common does not contain `rt_qemu_exit_success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("terminates RV64 through OpenSBI instead of a generated runtime exit")
val common = file_read("examples/09_embedded/simple_os/arch/common/host_gpu_ivshmem_probe_entry.spl")
val entry = file_read("examples/09_embedded/simple_os/arch/riscv64/host_gpu_smoke_entry.spl")
val sbi = file_read("src/os/kernel/arch/riscv64/sbi.spl")
expect(common.contains("rt_qemu_exit_success")).to_equal(false)
expect(entry).to_contain("sbi_shutdown()")
expect(sbi).to_contain("pub fn sbi_shutdown()")
```

</details>

#### keeps the boot ivshmem map out of the syscall-device monolith

- keeps the boot ivshmem map out of the syscall-device monolith
   - Expected: syscall_device does not contain `map_qemu_host_gpu_ivshmem_bar2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the boot ivshmem map out of the syscall-device monolith")
val common = file_read("examples/09_embedded/simple_os/arch/common/host_gpu_ivshmem_probe_entry.spl")
val mapping = file_read("src/os/kernel/ipc/host_gpu_ivshmem_map.spl")
val syscall_device = file_read("src/os/kernel/ipc/syscall_device.spl")
expect(common).to_contain("os.kernel.ipc.host_gpu_ivshmem_map")
expect(common).to_contain("common.gpu.simpleos_host_gpu_protocol")
expect(mapping).to_contain("fn map_qemu_host_gpu_ivshmem_bar2() -> i64")
expect(mapping).to_contain("return -71  # EPROTO: ivshmem identity visible but class shape rejected")
expect(mapping).to_contain("return -6  # ENXIO: QEMU vendor visible without ivshmem device 1110")
expect(mapping).to_contain("-2  # ENOENT: no matching ivshmem function on bus 0")
val pci = file_read("src/os/drivers/pci/pci.spl")
expect(pci).to_contain("fn _pci_ecam_base() -> u64: 0x4010000000u64")
expect(pci).to_contain("pci_ecam_addr(_pci_ecam_base()")
expect(syscall_device.contains("map_qemu_host_gpu_ivshmem_bar2")).to_equal(false)
```

</details>

#### keeps the early host GPU poll bound independent of cross-module initialization

- keeps the early host GPU poll bound independent of cross-module initialization
   - Expected: common does not contain `HOST_GPU_PROBE_TIMEOUT_POLLS: i64 = HOST_GPU_IVSHMEM_DEFAULT_TIMEOUT_POLLS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the early host GPU poll bound independent of cross-module initialization")
val common = file_read("examples/09_embedded/simple_os/arch/common/host_gpu_ivshmem_probe_entry.spl")
expect(common).to_contain("val HOST_GPU_PROBE_TIMEOUT_POLLS: i64 = 50000000")
expect(common.contains("HOST_GPU_PROBE_TIMEOUT_POLLS: i64 = HOST_GPU_IVSHMEM_DEFAULT_TIMEOUT_POLLS")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `c17603c25cf78afe470e010cdf74c3710baaeabaf67e27d97e13a569acbc7303`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c17603c25cf78afe470e010cdf74c3710baaeabaf67e27d97e13a569acbc7303`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c17603c25cf78afe470e010cdf74c3710baaeabaf67e27d97e13a569acbc7303`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_arm64_native_link_contract_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_arm64_native_link_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_arm64_native_link_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_arm64_native_link_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_arm64_native_link_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/os/simpleos_arm64_native_link_contract_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the host GPU daemon out of the compiler CLI closure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_arm64_native_link_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches freestanding ARM64 builds to the real boot owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_arm64_native_link_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every host GPU probe out of generic whole-tree discovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
