# Spawn Binary Kernel ABI Specification

> Structural regression coverage for syscall 13. These checks keep argv/envp

<!-- sdn-diagram:id=spawn_binary_kernel_abi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spawn_binary_kernel_abi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spawn_binary_kernel_abi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spawn_binary_kernel_abi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spawn Binary Kernel ABI Specification

Structural regression coverage for syscall 13. These checks keep argv/envp

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/spawn_binary_kernel_abi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Structural regression coverage for syscall 13. These checks keep argv/envp
copy-in wired through the kernel spawn path even when broader kernel specs are
blocked by unrelated compile failures.

## Scenarios

### spawn_binary kernel ABI

#### copies argv and envp vectors in the syscall handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read("src/os/kernel/ipc/syscall.spl")
expect(content).to_contain("fn _copy_spawn_string_vectors(argv_ptr: u64, envp_ptr: u64)")
expect(content).to_contain("val spawn_vectors_result = _copy_spawn_string_vectors(args.arg3, args.arg4)")
expect(content).to_contain("spawn_vectors.argv")
expect(content).to_contain("spawn_vectors.envp")
```

</details>

#### threads argv and envp through direct spawn handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read("src/os/kernel/ipc/syscall.spl")
expect(content).to_contain("fn dispatch_spawn_binary_direct(path_ptr: u64, path_len: u64, priority_raw: u64, argv_ptr: u64, envp_ptr: u64")
expect(content).to_contain("return _spawn_from_resolved_bytes(path, [], bytes_result.unwrap(), priority_raw, scheduler, klog, spawn_vectors.argv, spawn_vectors.envp)")
expect(content).to_contain("return _spawn_from_resolved_bytes(path, path_bytes, bytes_result.unwrap(), priority_raw, scheduler, klog, spawn_vectors.argv, spawn_vectors.envp)")
```

</details>

#### exposes argv and envp on the x86 syscall fast path and shim docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interrupt_content = _read("src/os/kernel/arch/x86_64/interrupt.spl")
expect(interrupt_content).to_contain("dispatch_spawn_binary_direct(arg0, arg1, arg2, arg3, arg4, g_trap_scheduler, g_trap_klog)")
val shim_content = _read("src/os/kernel/abi/syscall_shim.spl")
expect(shim_content).to_contain("# a3 = optional argv vector")
expect(shim_content).to_contain("# a4 = optional envp vector")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
