# Wine Kernel32 Atom Table Specification

> 1. wine kernel32 atom table new

<!-- sdn-diagram:id=wine_kernel32_atom_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_atom_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_atom_table_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_atom_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Atom Table Specification

## Scenarios

### Wine KERNEL32 atom table bridge

#### executes a bounded add, find, and delete atom sequence

1. wine kernel32 atom table new
   - Expected: result.ok is true
   - Expected: result.atom equals `0xc000`
   - Expected: result.name equals `SimpleOSWindowClass`
   - Expected: result.table.atoms.len() equals `0`
   - Expected: result.operations equals `GlobalAddAtomW GlobalFindAtomW GlobalDeleteAtom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_atom_table(
    ["GlobalAddAtomW", "GlobalFindAtomW", "GlobalDeleteAtom"],
    wine_kernel32_atom_table_new(),
    "SimpleOSWindowClass"
)

expect(result.ok).to_equal(true)
expect(result.atom).to_equal(0xc000)
expect(result.name).to_equal("SimpleOSWindowClass")
expect(result.table.atoms.len()).to_equal(0)
expect(result.operations).to_equal("GlobalAddAtomW GlobalFindAtomW GlobalDeleteAtom")
```

</details>

#### exposes direct atom table helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val added = wine_kernel32_global_add_atom_w(wine_kernel32_atom_table_new(), "SimpleOSWindowClass")
val found = wine_kernel32_global_find_atom_w(added.table, "SimpleOSWindowClass")
val deleted = wine_kernel32_global_delete_atom(found.table, found.atom)

expect(added.ok).to_equal(true)
expect(found.atom).to_equal(0xc000)
expect(deleted.ok).to_equal(true)
expect(deleted.table.atoms.len()).to_equal(0)
```

</details>

#### keeps atom table dispatch ordered and bounded

1. wine kernel32 atom table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-atom-table-sequence-expected:GlobalAddAtomW`
2. wine kernel32 atom table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_atom_table(
    ["GlobalFindAtomW", "GlobalAddAtomW", "GlobalDeleteAtom"],
    wine_kernel32_atom_table_new(),
    "SimpleOSWindowClass"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-atom-table-sequence-expected:GlobalAddAtomW")

val wrong_family = wine_kernel32_execute_atom_table(
    ["GlobalAddAtomW", "GlobalFindAtomW", "HeapAlloc"],
    wine_kernel32_atom_table_new(),
    "SimpleOSWindowClass"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid atom names and ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_kernel32_atom_table_new()
expect(wine_kernel32_global_add_atom_w(table, "").error).to_equal("GlobalAddAtomW:invalid-name")
expect(wine_kernel32_global_find_atom_w(table, "MissingClass").error).to_equal("GlobalFindAtomW:not-found")
expect(wine_kernel32_global_delete_atom(table, 0xc000).error).to_equal("GlobalDeleteAtom:invalid-atom")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_atom_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 atom table bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
