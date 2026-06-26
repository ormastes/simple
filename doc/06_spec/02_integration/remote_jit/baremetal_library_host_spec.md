# Baremetal Library Workload — Host

> <details>

<!-- sdn-diagram:id=baremetal_library_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_library_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_library_host_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_library_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Library Workload — Host

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/baremetal_library_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Baremetal library workload — host

<details>
<summary>Advanced: passes on host interpreter</summary>

#### passes on host interpreter _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_baremetal_library_workload()).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
