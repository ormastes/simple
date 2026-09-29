# Minimality Specification

<!-- sdn-diagram:id=minimality_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=minimality_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

minimality_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=minimality_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# Minimality Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/spipe/minimality_spec.spl` |
| Updated | 2026-07-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Covered Behavior

- `spipe_minimality_check` prefers native date inputs and keeps validation.
- `spipe_minimality_check` covers the core Ponytail rungs: `delete`, `yagni`,
  `stdlib`, `native`, and `shrink`.
- `spipe_minimality_review` reports delete, shrink, and dependency findings
  with line numbers.
- `spipe_minimality_debt` lists `ponytail:` debt markers.

</details>
