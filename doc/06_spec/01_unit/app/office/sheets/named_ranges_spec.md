# named_ranges_spec

> Office sheets named ranges (defined names) core behaviour spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# named_ranges_spec

Office sheets named ranges (defined names) core behaviour spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/named_ranges_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets named ranges (defined names) core behaviour spec.

Covers defining a name for a single cell and for a range, lookup, listing,
removal, target normalization, and resolution to concrete cell references.

## Scenarios

### NameStore.define and lookup
_Define names for cells and ranges, then look them up._

#### defines a name for a single cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
val reason = store.define("TaxRate", "B7")
expect(reason).to_equal("")
expect(store.lookup("TaxRate")).to_equal("B7")
```

</details>

#### defines a name for a range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(store.define("Sales", "A1:C3")).to_equal("")
expect(store.lookup("Sales")).to_equal("A1:C3")
```

</details>

#### normalizes the target to upper case

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(store.define("Region", "a1:c3")).to_equal("")
expect(store.lookup("Region")).to_equal("A1:C3")
```

</details>

#### reports an undefined name as nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(store.lookup("Missing") == nil).to_equal(true)
```

</details>

#### reports presence with has

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Total", "D10")
expect(store.has("Total")).to_equal(true)
expect(store.has("Nope")).to_equal(false)
```

</details>

### NameStore.list_names and count
_List defined names in sorted original spelling._

#### lists names sorted case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Zebra", "A1")
store.define("alpha", "A2")
store.define("Mid", "A3")
expect(store.list_names()).to_equal(["alpha", "Mid", "Zebra"])
```

</details>

#### counts defined names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(store.count()).to_equal(0)
store.define("One", "A1")
store.define("Two", "A2")
expect(store.count()).to_equal(2)
```

</details>

### NameStore.remove and redefine
_Remove and deliberately overwrite definitions._

#### removes an existing name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Temp", "B2")
expect(store.remove("Temp")).to_equal(true)
expect(store.has("Temp")).to_equal(false)
```

</details>

#### redefines an existing name to a new target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("SalesBlock", "A1:A5")
expect(store.redefine("SalesBlock", "B1:B9")).to_equal("")
expect(store.lookup("SalesBlock")).to_equal("B1:B9")
```

</details>

### name resolution
_Resolve a name to a CellRange or to concrete cell references._

#### resolves a range name to its cell references

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Block", "A1:B2")
expect(name_target_refs(store, "Block")).to_equal(["A1", "A2", "B1", "B2"])
```

</details>

#### resolves a single-cell name to one reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Cell", "C4")
expect(name_target_refs(store, "Cell")).to_equal(["C4"])
```

</details>

#### resolves an undefined name to an empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(name_target_refs(store, "Ghost")).to_equal([])
```

</details>

#### resolves a range name to a CellRange

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Block", "A1:B2")
val range = name_target_range(store, "Block")
expect(range != nil).to_equal(true)
expect(range.start.col).to_equal(0)
expect(range.end_ref.row).to_equal(1)
```

</details>

### target validation
_Only valid A1 cells and ranges are accepted as targets._

#### accepts a cell target

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_target("b7")).to_equal("B7")
```

</details>

#### rejects a non-A1 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_target("not a ref")).to_equal("")
```

</details>

#### rejects a definition with an invalid target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
val reason = store.define("Bad", "hello")
expect(reason.contains("not a valid cell reference")).to_equal(true)
expect(store.has("Bad")).to_equal(false)
```

</details>

#### accepts a valid name in validate_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("Tax_Rate.2")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
