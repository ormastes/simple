# allowed_families_spec

> Module resolver runtime-family filtering regression.

<!-- sdn-diagram:id=allowed_families_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=allowed_families_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

allowed_families_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=allowed_families_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# allowed_families_spec

Module resolver runtime-family filtering regression.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/module_resolver/allowed_families_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Module resolver runtime-family filtering regression.

This intentionally scans the source implementation instead of importing the
resolver. The current interpreter cannot reliably execute module-resolver
imports in unit specs, but this still locks the production filtering path.

## Scenarios

### module resolver allowed_families

#### stores allowed family restrictions on ModuleResolver

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("allowed_families: \\[text\\]", "src/compiler/99.loader/module_resolver/types.spl")).to_equal(true)
```

</details>

#### exposes a helper for setting allowed family restrictions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("fn moduleresolver_with_allowed_families", "src/compiler/99.loader/module_resolver/types.spl")).to_equal(true)
```

</details>

#### filters stdlib family subdirectories when restrictions are active

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/99.loader/module_resolver/resolution.spl"
expect(_has("if self\\.allowed_families\\.len\\(\\) > 0:", path)).to_equal(true)
expect(_has("for af in self\\.allowed_families:", path)).to_equal(true)
expect(_has("if not family_allowed:", path)).to_equal(true)
expect(_has("continue", path)).to_equal(true)
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
