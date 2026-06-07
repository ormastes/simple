# host_cpu_variant_spec

> AC-10: Host CPU runtime variant selection — 20 unit tests.

<!-- sdn-diagram:id=host_cpu_variant_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_cpu_variant_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_cpu_variant_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_cpu_variant_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# host_cpu_variant_spec

AC-10: Host CPU runtime variant selection — 20 unit tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/host_cpu_variant_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

AC-10: Host CPU runtime variant selection — 20 unit tests.

Covers SIMD tier ranking, hardware clamping, dispatch name qualification,
loader probing, manifest entries, and variant selection with fallback.
All helpers are self-contained (no external imports beyond io_runtime).


</details>
