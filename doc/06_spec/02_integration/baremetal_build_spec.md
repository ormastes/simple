# Bare-Metal Build Checks

> Verifies that the checked-in bare-metal build path has a real compile pipeline

<!-- sdn-diagram:id=baremetal_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_build_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Build Checks

Verifies that the checked-in bare-metal build path has a real compile pipeline

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/baremetal_build_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the checked-in bare-metal build path has a real compile pipeline
and that the ARM support files can be linked into a valid ELF on hosts with the
required LLVM tools installed.

## Scenarios

### Bare-metal build readiness

#### uses a real source compile path in the checked-in builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(build_source_is_ready()).to_equal(true)
```

</details>

#### selects ARM and RISC-V32 LLVM targets in the pure compiler path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compile_to_llvm_target_selection_ready()).to_equal(true)
```

</details>

#### links a minimal ARM bare-metal ELF with the checked-in support files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = arm_minimal_link_status()
expect(status == "ok" or status.starts_with("skip:")).to_equal(true)
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
