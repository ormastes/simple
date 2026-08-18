# named_ranges_edge_spec

> Office sheets named ranges edge-case spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# named_ranges_edge_spec

Office sheets named ranges edge-case spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/named_ranges_edge_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets named ranges edge-case spec.

Covers rejection of names colliding with A1 cell references, duplicates,
case-insensitive lookup and duplicate detection, removal of a name that was
never defined, and empty/whitespace/invalid-character names.

## Scenarios

### collision with A1 cell references
_A name that reads as a cell reference is ambiguous and rejected._

#### rejects a plain A1 collision

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("A1").contains("collides with cell reference")).to_equal(true)
```

</details>

#### rejects the last Excel cell XFD1048576

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("XFD1048576").contains("collides with cell reference")).to_equal(true)
```

</details>

#### rejects a lower-case cell reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("b7").contains("collides with cell reference")).to_equal(true)
```

</details>

#### does not store a colliding name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
val reason = store.define("A1", "B2")
expect(reason.contains("collides")).to_equal(true)
expect(store.count()).to_equal(0)
```

</details>

#### rejects a word-plus-digits name that parses as a reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RANGE1 looks like a word but is column RANGE, row 1.
expect(validate_name("Range1").contains("collides with cell reference")).to_equal(true)
```

</details>

#### accepts a name that merely starts like a reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("A1Total")).to_equal("")
```

</details>

### reserved R1C1 letters
_R and C alone are reserved by R1C1 notation._

#### rejects R

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("R").contains("reserved")).to_equal(true)
```

</details>

#### rejects lower-case c

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("c").contains("reserved")).to_equal(true)
```

</details>

#### accepts RC as a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("RC")).to_equal("")
```

</details>

### duplicates
_A second definition of the same name is rejected, not silently applied._

#### rejects an exact duplicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Sales", "A1:A5")
val reason = store.define("Sales", "B1:B5")
expect(reason.contains("duplicate")).to_equal(true)
```

</details>

#### leaves the original target intact after a rejected duplicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Sales", "A1:A5")
store.define("Sales", "B1:B5")
expect(store.lookup("Sales")).to_equal("A1:A5")
expect(store.count()).to_equal(1)
```

</details>

#### treats a differently-cased name as a duplicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("TaxRate", "B7")
expect(store.define("TAXRATE", "C9").contains("duplicate")).to_equal(true)
```

</details>

### case sensitivity
_Lookup is case-insensitive but the original spelling is preserved._

#### looks a name up in any case

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("TaxRate", "B7")
expect(store.lookup("taxrate")).to_equal("B7")
expect(store.lookup("TAXRATE")).to_equal("B7")
```

</details>

#### preserves the original spelling in list_names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("TaxRate", "B7")
expect(store.list_names()).to_equal(["TaxRate"])
```

</details>

#### removes a name given in a different case

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("TaxRate", "B7")
expect(store.remove("taxrate")).to_equal(true)
expect(store.count()).to_equal(0)
```

</details>

### removing a name that does not exist
_Removal reports false rather than failing or removing something else._

#### returns false for an unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(store.remove("Ghost")).to_equal(false)
```

</details>

#### leaves other names untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
store.define("Keep", "A1")
store.remove("Ghost")
expect(store.count()).to_equal(1)
expect(store.lookup("Keep")).to_equal("A1")
```

</details>

### empty and malformed names
_Empty, whitespace-only and badly-formed names are rejected._

#### rejects an empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("").contains("empty")).to_equal(true)
```

</details>

#### rejects a whitespace-only name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("   ").contains("empty")).to_equal(true)
```

</details>

#### rejects a name starting with a digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("1Total").contains("must start with")).to_equal(true)
```

</details>

#### rejects a name containing a space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("Tax Rate").contains("invalid character")).to_equal(true)
```

</details>

#### rejects a name containing a hyphen

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("Tax-Rate").contains("invalid character")).to_equal(true)
```

</details>

#### accepts a leading underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_name("_hidden")).to_equal("")
```

</details>

#### trims surrounding whitespace when defining

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NameStore.new()
expect(store.define("  Padded  ", "A1")).to_equal("")
expect(store.list_names()).to_equal(["Padded"])
expect(store.lookup("Padded")).to_equal("A1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
