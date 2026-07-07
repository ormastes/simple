# gc_strategy_naming_spec

> GC mode and barrier strategy naming regression.

<!-- sdn-diagram:id=gc_strategy_naming_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_strategy_naming_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_strategy_naming_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_strategy_naming_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gc_strategy_naming_spec

GC mode and barrier strategy naming regression.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/gc_strategy_naming_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

GC mode and barrier strategy naming regression.

Family-level GC mode and MIR barrier strategy are separate concepts; this keeps
their type names separate so imports stay unambiguous.

## Scenarios

### GC strategy naming

#### has only one compiler enum named GcMode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = _non_empty_scan_lines(_scan("enum GcMode:", "src/compiler"))
expect(matches.len()).to_equal(1)
expect(matches[0].starts_with("src/compiler/00.common/gc_config.spl:")).to_equal(true)
```

</details>

#### uses GcStrategy for write barrier GC algorithms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = _non_empty_scan_lines(_scan("enum GcStrategy:", "src/compiler/55.borrow/gc_analysis/barriers.spl"))
expect(matches.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
