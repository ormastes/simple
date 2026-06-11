# Loader unload ownership helpers

> Verifies the helpers used during module unload to filter the global

<!-- sdn-diagram:id=unload_ownership_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unload_ownership_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unload_ownership_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unload_ownership_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader unload ownership helpers

Verifies the helpers used during module unload to filter the global

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/unload_ownership_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the helpers used during module unload to filter the global
    symbol table by owning module path and to drop a set of symbols
    by name.

## Scenarios

### Loader unload ownership helpers

#### collects only symbols owned by the requested module path

1. "a fn":
2. "b fn":
3. "c fn":
   - Expected: names.len() equals `2`
   - Expected: names contains `a_fn`
   - Expected: names contains `c_fn`
   - Expected: names does not contain `b_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_a = LoadedSymbol(
    name: "a_fn",
    address: 1,
    size: 1,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val sym_b = LoadedSymbol(
    name: "b_fn",
    address: 2,
    size: 1,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val sym_c = LoadedSymbol(
    name: "c_fn",
    address: 3,
    size: 1,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val global_symbols = {
    "a_fn": ("path_a", sym_a),
    "b_fn": ("path_b", sym_b),
    "c_fn": ("path_a", sym_c)
}

val names = owned_global_symbol_names(global_symbols, "path_a")
expect(names.len()).to_equal(2)
expect(names.contains("a_fn")).to_equal(true)
expect(names.contains("c_fn")).to_equal(true)
expect(names.contains("b_fn")).to_equal(false)
```

</details>

#### filters requested names from the global symbol table

1. "a fn":
2. "b fn":
3. "c fn":
   - Expected: kept.has("a_fn") is false
   - Expected: kept.has("c_fn") is false
   - Expected: kept.has("b_fn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_a = LoadedSymbol(
    name: "a_fn",
    address: 1,
    size: 1,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val sym_b = LoadedSymbol(
    name: "b_fn",
    address: 2,
    size: 1,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val sym_c = LoadedSymbol(
    name: "c_fn",
    address: 3,
    size: 1,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val global_symbols = {
    "a_fn": ("path_a", sym_a),
    "b_fn": ("path_b", sym_b),
    "c_fn": ("path_a", sym_c)
}

val kept = global_symbols_without_names(global_symbols, ["a_fn", "c_fn"])
expect(kept.has("a_fn")).to_equal(false)
expect(kept.has("c_fn")).to_equal(false)
expect(kept.has("b_fn")).to_equal(true)
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
