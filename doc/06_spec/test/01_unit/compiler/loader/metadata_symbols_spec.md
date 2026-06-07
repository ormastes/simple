# Loader metadata symbol helpers

> Verifies extraction of mangled instantiation symbol names from

<!-- sdn-diagram:id=metadata_symbols_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metadata_symbols_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metadata_symbols_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metadata_symbols_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader metadata symbol helpers

Verifies extraction of mangled instantiation symbol names from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/metadata_symbols_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies extraction of mangled instantiation symbol names from
    LoadedMetadata, including filtering by source file path and removal
    of paths from the loaded-metadata map.

## Scenarios

### Loader metadata symbol helpers

#### returns mangled names from metadata instantiations in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = LoadedMetadata(
    possible: [],
    instantiations: [
        InstantiationRecord(
            id: 0,
            template_name: "Vec",
            type_args: "i64",
            mangled_name: "Vec$i64",
            from_file: "a.smf",
            from_loc: "a.smf:0:0",
            to_obj: "jit_obj",
            status: "jit_compiled"
        ),
        InstantiationRecord(
            id: 1,
            template_name: "Map",
            type_args: "text_i64",
            mangled_name: "Map$text_i64",
            from_file: "a.smf",
            from_loc: "a.smf:0:1",
            to_obj: "jit_obj",
            status: "jit_compiled"
        )
    ]
)

val names = metadata_instantiation_symbol_names(metadata)
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("Vec$i64")
expect(names[1]).to_equal("Map$text_i64")
```

</details>

#### returns empty for metadata with no instantiations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = LoadedMetadata(possible: [], instantiations: [])
val names = metadata_instantiation_symbol_names(metadata)
expect(names.len()).to_equal(0)
```

</details>

#### returns instantiation names for a specific loaded-metadata path

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = LoadedMetadata(
    possible: [],
    instantiations: [
        InstantiationRecord(
            id: 0,
            template_name: "Hot",
            type_args: "reload",
            mangled_name: "hot_reload_fn",
            from_file: "target.smf",
            from_loc: "target.smf:0:0",
            to_obj: "jit_obj",
            status: "jit_compiled"
        )
    ]
)
val other = LoadedMetadata(possible: [], instantiations: [])
val all = {"target.smf": target, "other.smf": other}

val names = loaded_metadata_instantiation_symbol_names(all, "target.smf")
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("hot_reload_fn")
```

</details>

#### returns empty when the loaded-metadata path is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = {}
val names = loaded_metadata_instantiation_symbol_names(all, "missing.smf")
expect(names.len()).to_equal(0)
```

</details>

#### removes a loaded-metadata path when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = LoadedMetadata(possible: [], instantiations: [])
val all = {"present.smf": metadata}
val updated = loaded_metadata_remove_path(all, "present.smf")
expect(updated.has("present.smf")).to_equal(false)
```

</details>

#### leaves loaded metadata unchanged when path is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = LoadedMetadata(possible: [], instantiations: [])
val all = {"present.smf": metadata}
val updated = loaded_metadata_remove_path(all, "missing.smf")
expect(updated.has("present.smf")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
