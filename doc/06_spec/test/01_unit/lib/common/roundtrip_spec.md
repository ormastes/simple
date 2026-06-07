# Roundtrip Specification

> _Verify parse -> serialize -> parse idempotency for all SDN value types._

<!-- sdn-diagram:id=roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

roundtrip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Roundtrip Specification

## Scenarios

### SDN Round-trip
_Verify parse -> serialize -> parse idempotency for all SDN value types._

#### parse -> serialize -> parse

#### preserves primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "int_val: 42\nfloat_val: 3.14\nstr_val: hello\nbool_val: true\nnull_val: null"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val int_v = reparsed.get("int_val")
                expect(int_v.?).to_equal(true)
                val str_v = reparsed.get("str_val")
                expect(str_v.?).to_equal(true)
                val bool_v = reparsed.get("bool_val")
                expect(bool_v.?).to_equal(true)
                val null_v = reparsed.get("null_val")
                expect(null_v.?).to_equal(true)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves inline dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "point = " + "{" + "xval: 10, yval: 20, zval: 30" + "}"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val point = reparsed.get("point")
                expect(point.?).to_equal(true)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves inline arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "items = [1, 2, 3, 4, 5]"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val items = reparsed.get("items")
                expect(items.?).to_equal(true)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves block dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "server:\n    host: localhost\n    port: 8080"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val server = reparsed.get("server")
                expect(server.?).to_equal(true)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves block arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fruits:\n    apple\n    banana\n    cherry"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val fruits = reparsed.get("fruits")
                expect(fruits.?).to_equal(true)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves nested structures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "config:\n    server:\n        host: localhost\n        port: 8080\n    database:\n        name: mydb\n        port: 5432"
match parse(source):
    case Ok(original):
        val server_host = original.get_path("config.server.host")
        expect(server_host.?).to_equal(true)
        val db_name = original.get_path("config.database.name")
        expect(db_name.?).to_equal(true)
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN Round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
