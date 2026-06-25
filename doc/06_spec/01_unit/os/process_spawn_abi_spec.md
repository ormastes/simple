# Process Spawn ABI Specification

> Regression coverage for the userspace spawn wrappers. These checks keep

<!-- sdn-diagram:id=process_spawn_abi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_spawn_abi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_spawn_abi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_spawn_abi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Spawn ABI Specification

Regression coverage for the userspace spawn wrappers. These checks keep

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/process_spawn_abi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for the userspace spawn wrappers. These checks keep
argv/envp forwarding on the spawn path from silently regressing back to
path-only behavior.

## Scenarios

### process spawn ABI shims

#### forwards argv pointers from SOSIX spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read("src/os/sosix/process.spl")
expect(content).to_contain("val argv_marshaled = _marshal_exec_string_vector(args)")
expect(content).to_contain("argv_marshaled.ptr")
```

</details>

#### exposes a userlib spawn helper with argv and envp

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read("src/os/userlib/process.spl")
expect(content).to_contain("fn spawn_binary_with_args(path: text, args: [text], envp: [text], priority: u8)")
expect(content).to_contain("argv_marshaled.ptr")
expect(content).to_contain("envp_marshaled.ptr")
```

</details>

#### documents that POSIX spawn now forwards argv

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _read("src/os/posix/process_compat.spl")
expect(content).to_contain("SpawnBinary forwards argv through syscall 13")
expect(content.contains("ignores `args` until argv/envp support lands")).to_equal(false)
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
