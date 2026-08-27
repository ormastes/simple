# simple_db_nvfs_constants_spec

> Root-level coverage for FR-SIMPLE_DB-M2-002 canonical NVFS constants.

<!-- sdn-diagram:id=simple_db_nvfs_constants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_db_nvfs_constants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_db_nvfs_constants_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_db_nvfs_constants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_db_nvfs_constants_spec

Root-level coverage for FR-SIMPLE_DB-M2-002 canonical NVFS constants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/simple_db_nvfs_constants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Root-level coverage for FR-SIMPLE_DB-M2-002 canonical NVFS constants.

## Scenarios

### NVFS shared constants

#### exports the canonical ordinals requested by FR-SIMPLE_DB-M2-002

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STORAGE_CLASS_DB_WAL).to_equal(1)
expect(STORAGE_CLASS_META_DURABLE).to_equal(2)
expect(STORAGE_CLASS_DB_TEMP).to_equal(3)
expect(DURABILITY_DATA_DURABLE).to_equal(1)
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
