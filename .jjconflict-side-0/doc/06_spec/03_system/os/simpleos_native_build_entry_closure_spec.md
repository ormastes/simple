# SimpleOS Native Build Entry Closure

> System-level regression check for FR-SOS-023. The OS native-build lane must

<!-- sdn-diagram:id=simpleos_native_build_entry_closure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_native_build_entry_closure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_native_build_entry_closure_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_native_build_entry_closure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Native Build Entry Closure

System-level regression check for FR-SOS-023. The OS native-build lane must

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_native_build_entry_closure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-SOS-023. The OS native-build lane must
compile the explicit entry closure instead of scanning unrelated entry modules.

## Scenarios

### SimpleOS native-build entry closure

#### builds x86_64 os_entry through the explicit entry closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = os_native_build_args(x86_64_os_entry_target(), "llvm")
expect(args).to_contain("--entry-closure")
expect(args).to_contain("--entry")
expect(args).to_contain("examples/09_embedded/simple_os/arch/x86_64/os_entry.spl")
expect(args).to_contain("--target")
expect(args).to_contain("x86_64-unknown-none")
expect(args.contains("examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
