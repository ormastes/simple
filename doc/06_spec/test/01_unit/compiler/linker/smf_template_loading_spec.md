# SMF Template Loading Specification

> Tests for SMF/Template Loading implementation covering:

<!-- sdn-diagram:id=smf_template_loading_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_template_loading_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_template_loading_spec -> std
smf_template_loading_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_template_loading_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Template Loading Specification

Tests for SMF/Template Loading implementation covering:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | F5-STUB007-STUB009-STUB010 |
| Category | Tooling |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Source | `test/01_unit/compiler/linker/smf_template_loading_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SMF/Template Loading implementation covering:
- STUB-007: Section table population from FFI reads
- STUB-009: GTPL binary deserialization and template loading from SMF
- STUB-010: note.sdn section reading and SmfReaderMemory bridging

## Key Concepts

| Concept | Description |
|---------|-------------|
| GTPL | Generic Template binary format (magic 0x4754504C) |
| SmfSectionRaw | Raw section entry with type, flags, offset, size |
| derive_section_type_from_index | Maps section index to type code |
| parse_gtpl_constraints | Extracts type constraints from GTPL body |

## Scenarios

### Section Type Mapping

#### maps index 0 to Code section type 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = derive_section_type_from_index(0)
expect(result as i32).to_equal(1)
```

</details>

#### maps index 1 to Data section type 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = derive_section_type_from_index(1)
expect(result as i32).to_equal(2)
```

</details>

#### maps index 2 to TemplateCode section type 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = derive_section_type_from_index(2)
expect(result as i32).to_equal(12)
```

</details>

#### maps index 3 to TemplateMeta section type 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = derive_section_type_from_index(3)
expect(result as i32).to_equal(13)
```

</details>

#### maps unknown index to type 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = derive_section_type_from_index(99)
expect(result as i32).to_equal(0)
```

</details>

### GTPL Constraint Parsing

#### when no constraints are present

#### returns empty list for offset beyond data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0, 0, 0]
val result = parse_gtpl_constraints(bytes, 10)
expect(result.len()).to_equal(0)
```

</details>

#### returns empty list for zero count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4-byte count = 0
val bytes: [u8] = [0, 0, 0, 0]
val result = parse_gtpl_constraints(bytes, 0)
expect(result.len()).to_equal(0)
```

</details>

#### when a single constraint is present

#### parses one constraint with param T and bound Display

1. bytes = bytes push
2. bytes = bytes push
3. bytes = bytes push
4. bytes = bytes push
5. bytes = bytes push
6. bytes = bytes push
7. bytes = bytes push
8. bytes = bytes push
9. bytes = bytes push
10. bytes = bytes push
11. bytes = bytes push
12. bytes = bytes push
13. bytes = bytes push
14. bytes = bytes push
15. bytes = bytes push
16. bytes = bytes push
   - Expected: result.len() equals `1`
   - Expected: result[0].param equals `T`
   - Expected: result[0].bound equals `Display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# count = 1 (u32 LE)
# param_len = 1 (u16 LE), param = 'T' (0x54)
# bound_len = 7 (u16 LE), bound = 'Display' (0x44,0x69,0x73,0x70,0x6C,0x61,0x79)
var bytes: [u8] = []
# count: 1
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
# param_len: 1
bytes = bytes.push(1)
bytes = bytes.push(0)
# param: T
bytes = bytes.push(0x54)
# bound_len: 7
bytes = bytes.push(7)
bytes = bytes.push(0)
# bound: Display
bytes = bytes.push(0x44)
bytes = bytes.push(0x69)
bytes = bytes.push(0x73)
bytes = bytes.push(0x70)
bytes = bytes.push(0x6C)
bytes = bytes.push(0x61)
bytes = bytes.push(0x79)

val result = parse_gtpl_constraints(bytes, 0)
expect(result.len()).to_equal(1)
expect(result[0].param).to_equal("T")
expect(result[0].bound).to_equal("Display")
```

</details>

#### when data is truncated

#### returns partial results for truncated data

1. bytes = bytes push
2. bytes = bytes push
3. bytes = bytes push
4. bytes = bytes push
5. bytes = bytes push
6. bytes = bytes push
7. bytes = bytes push
8. bytes = bytes push
9. bytes = bytes push
10. bytes = bytes push
   - Expected: result.len() equals `1`
   - Expected: result[0].param equals `T`
   - Expected: result[0].bound equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# count = 2, but only one constraint fits
var bytes: [u8] = []
# count: 2
bytes = bytes.push(2)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
# param_len: 1
bytes = bytes.push(1)
bytes = bytes.push(0)
# param: T
bytes = bytes.push(0x54)
# bound_len: 1
bytes = bytes.push(1)
bytes = bytes.push(0)
# bound: X
bytes = bytes.push(0x58)
# second constraint would start here but data ends

val result = parse_gtpl_constraints(bytes, 0)
# Should parse first constraint successfully, stop at truncated second
expect(result.len()).to_equal(1)
expect(result[0].param).to_equal("T")
expect(result[0].bound).to_equal("X")
```

</details>

### Type Parameter Generation

#### generates zero parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = generate_type_params(0)
expect(params.len()).to_equal(0)
```

</details>

#### generates single parameter T

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = generate_type_params(1)
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("T")
```

</details>

#### generates three parameters T U V

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = generate_type_params(3)
expect(params.len()).to_equal(3)
expect(params[0]).to_equal("T")
expect(params[1]).to_equal("U")
expect(params[2]).to_equal("V")
```

</details>

#### generates all seven alphabet names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = generate_type_params(7)
expect(params.len()).to_equal(7)
expect(params[6]).to_equal("Z")
```

</details>

#### generates numbered names after alphabet

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = generate_type_params(9)
expect(params.len()).to_equal(9)
expect(params[7]).to_equal("T7")
expect(params[8]).to_equal("T8")
```

</details>

### GTPL Template Parsing

#### when parsing valid GTPL data

#### parses GTPL header with Function kind

1. bytes = bytes push
2. bytes = bytes push
3. bytes = bytes push
4. bytes = bytes push
5. bytes = bytes push
6. bytes = bytes push
7. bytes = bytes push
8. bytes = bytes push
9. bytes = bytes push
10. bytes = bytes push
11. bytes = bytes push
   - Expected: tmpl.name equals `test_fn`
   - Expected: tmpl.type_params.len() equals `2`
   - Expected: tmpl.type_params[0] equals `T`
   - Expected: tmpl.type_params[1] equals `U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a minimal GTPL: magic GTPL (0x47,0x54,0x50,0x4C) + version 1.0 + count 1 + kind 0 (Function)
var bytes: [u8] = []
# Magic: GTPL
bytes = bytes.push(0x47)
bytes = bytes.push(0x54)
bytes = bytes.push(0x50)
bytes = bytes.push(0x4C)
# Version 1.0
bytes = bytes.push(1)
bytes = bytes.push(0)
# template_count: 1 (u32 LE)
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
# kind: 0 = Function
bytes = bytes.push(0)

val sym = make_test_symbol("test_fn", 2)
val tmpl = parse_template(bytes, sym)

expect(tmpl.name).to_equal("test_fn")
expect(tmpl.type_params.len()).to_equal(2)
expect(tmpl.type_params[0]).to_equal("T")
expect(tmpl.type_params[1]).to_equal("U")
```

</details>

#### parses GTPL with Struct kind

1. bytes = bytes push
2. bytes = bytes push
3. bytes = bytes push
4. bytes = bytes push
5. bytes = bytes push
6. bytes = bytes push
7. bytes = bytes push
8. bytes = bytes push
9. bytes = bytes push
10. bytes = bytes push
11. bytes = bytes push
   - Expected: tmpl.name equals `MyStruct`
   - Expected: tmpl.type_params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = []
# Magic
bytes = bytes.push(0x47)
bytes = bytes.push(0x54)
bytes = bytes.push(0x50)
bytes = bytes.push(0x4C)
# Version 1.0
bytes = bytes.push(1)
bytes = bytes.push(0)
# count: 1
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
# kind: 1 = Struct
bytes = bytes.push(1)

val sym = make_test_symbol("MyStruct", 1)
val tmpl = parse_template(bytes, sym)

expect(tmpl.name).to_equal("MyStruct")
expect(tmpl.type_params.len()).to_equal(1)
```

</details>

#### preserves body bytes after kind byte

1. bytes = bytes push
2. bytes = bytes push
3. bytes = bytes push
4. bytes = bytes push
5. bytes = bytes push
6. bytes = bytes push
7. bytes = bytes push
8. bytes = bytes push
9. bytes = bytes push
10. bytes = bytes push
11. bytes = bytes push
12. bytes = bytes push
13. bytes = bytes push
14. bytes = bytes push
15. bytes = bytes push


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = []
# Magic
bytes = bytes.push(0x47)
bytes = bytes.push(0x54)
bytes = bytes.push(0x50)
bytes = bytes.push(0x4C)
# Version 1.0
bytes = bytes.push(1)
bytes = bytes.push(0)
# count: 1
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
# kind: 0
bytes = bytes.push(0)
# body data
bytes = bytes.push(0xDE)
bytes = bytes.push(0xAD)
bytes = bytes.push(0xBE)
bytes = bytes.push(0xEF)

val sym = make_test_symbol("with_body", 1)
val tmpl = parse_template(bytes, sym)

expect(tmpl.body.len()).to_be_greater_than(0)
```

</details>

#### separates a trailing constraint block from opaque body bytes

1. bytes = bytes push
2. bytes = bytes push
3. bytes = bytes push
4. bytes = bytes push
5. bytes = bytes push
6. bytes = bytes push
7. bytes = bytes push
8. bytes = bytes push
9. bytes = bytes push
10. bytes = bytes push
11. bytes = bytes push
12. bytes = bytes push
13. bytes = bytes push
14. bytes = bytes push
15. bytes = bytes push
16. bytes = bytes push
17. bytes = bytes push
18. bytes = bytes push
19. bytes = bytes push
20. bytes = bytes push
21. bytes = bytes push
22. bytes = bytes push
23. bytes = bytes push
24. bytes = bytes push
25. bytes = bytes push
26. bytes = bytes push
27. bytes = bytes push
28. bytes = bytes push
29. bytes = bytes push
   - Expected: tmpl.body equals `[0xDE, 0xAD]`
   - Expected: tmpl.constraints.len() equals `1`
   - Expected: tmpl.constraints[0].param equals `T`
   - Expected: tmpl.constraints[0].bound equals `Display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = []
bytes = bytes.push(0x47)
bytes = bytes.push(0x54)
bytes = bytes.push(0x50)
bytes = bytes.push(0x4C)
bytes = bytes.push(1)
bytes = bytes.push(1)
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)

# Opaque body bytes
bytes = bytes.push(0xDE)
bytes = bytes.push(0xAD)

# Constraint block: count=1, param=T, bound=Display
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(0)
bytes = bytes.push(1)
bytes = bytes.push(0)
bytes = bytes.push(0x54)
bytes = bytes.push(7)
bytes = bytes.push(0)
bytes = bytes.push(0x44)
bytes = bytes.push(0x69)
bytes = bytes.push(0x73)
bytes = bytes.push(0x70)
bytes = bytes.push(0x6C)
bytes = bytes.push(0x61)
bytes = bytes.push(0x79)

val sym = make_test_symbol("with_constraints", 1)
val tmpl = parse_template(bytes, sym)

expect(tmpl.body).to_equal([0xDE, 0xAD])
expect(tmpl.constraints.len()).to_equal(1)
expect(tmpl.constraints[0].param).to_equal("T")
expect(tmpl.constraints[0].bound).to_equal("Display")
```

</details>

#### when data has no GTPL magic

#### treats entire data as opaque body

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = [0x00, 0x01, 0x02, 0x03, 0x04]

val sym = make_test_symbol("opaque_fn", 1)
val tmpl = parse_template(bytes, sym)

expect(tmpl.name).to_equal("opaque_fn")
expect(tmpl.body).to_equal(bytes)
```

</details>

#### when data is too small for GTPL header

#### treats small data as opaque body

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = [0x47, 0x54]  # partial magic

val sym = make_test_symbol("small_fn", 0)
val tmpl = parse_template(bytes, sym)

expect(tmpl.name).to_equal("small_fn")
expect(tmpl.type_params.len()).to_equal(0)
expect(tmpl.body).to_equal(bytes)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
