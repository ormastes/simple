# loader_shared_core_spec

> Loader Shared-Core Refactor Invariants — AC-10

<!-- sdn-diagram:id=loader_shared_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loader_shared_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loader_shared_core_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loader_shared_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# loader_shared_core_spec

Loader Shared-Core Refactor Invariants — AC-10

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-10-001 through #AC-10-020 |
| Category | Compiler / Loader |
| Status | Active |
| Design | doc/05_design/graphics_backend_acceleration.md |
| Source | `test/01_unit/compiler/loader/loader_shared_core_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Loader Shared-Core Refactor Invariants — AC-10

20 tests covering shared-core invariants: unload policy, metadata priority,
JIT state lifecycle, global ownership, and deterministic rebuild properties.


## Related Documentation

- **Design:** [doc/05_design/graphics_backend_acceleration.md](doc/05_design/graphics_backend_acceleration.md)


</details>
