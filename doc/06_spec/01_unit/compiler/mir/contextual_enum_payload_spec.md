# Contextual Enum Payload Specification

> Tests covering declared enum payload contextual containers, declared enum collection MIR metadata, explicit payload type authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contextual Enum Payload Specification

## Scenarios

### declared enum payload contextual containers

#### empty recursive array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Empty\n    Array([Value])\nfn make() -> Value:\n    Value.Array([])\n")
expect(errors.len()).to_equal(0)
```

</details>

#### empty recursive dictionary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Empty\n    Dict(Dict<text, Value>)\nfn make() -> Value:\n    Value.Dict({})\n")
expect(errors.len()).to_equal(0)
```

</details>

#### nested empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Empty\n    Matrix([[Value]])\nfn make() -> Value:\n    Value.Matrix([[]])\n")
expect(errors.len()).to_equal(0)
```

</details>

#### empty array in positional tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Pair([i64], text)\nfn make() -> Value:\n    Value.Pair([], \"ok\")\n")
expect(errors.len()).to_equal(0)
```

</details>

#### generic empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Box<T>:\n    Wrap([T])\nfn make() -> Box<i64>:\n    Box.Wrap([])\n")
expect(errors.len()).to_equal(0)
```

</details>

#### actual SDN empty constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("# SDN Value — Simple Data Notation value types.\n#\n# Provides: SdnValue, SdnSpan.\n\n# Source location span for error reporting.\npub class SdnSpan:\n    line: i64\n    column: i64\n    start: i64 = 0\n    end: i64 = 0\n\n    static fn empty() -> SdnSpan:\n        SdnSpan(line: 0, column: 0, start: 0, end: 0)\n\n    static fn at(line: i64, column: i64) -> SdnSpan:\n        SdnSpan(line: line, column: column, start: 0, end: 0)\n\n    fn merge(self, other: SdnSpan) -> SdnSpan:\n        var lo = self.start\n        if other.start < lo:\n            lo = other.start\n        var hi = self.end\n        if other.end > hi:\n            hi = other.end\n        SdnSpan(line: self.line, column: self.column, start: lo, end: hi)\n\n# The core SDN value type.\npub enum SdnValue:\n    Null\n    Bool(bool)\n    Int(i64)\n    Float(f64)\n    String(text)\n    Array([SdnValue])\n    Dict(Dict<text, SdnValue>)\n    Table(headers: [text], rows: [[SdnValue]])\n\n    static fn null() -> SdnValue:\n        SdnValue.Null\n\n    static fn bool(b: bool) -> SdnValue:\n        SdnValue.Bool(b)\n\n    static fn int(i: i64) -> SdnValue:\n        SdnValue.Int(i)\n\n    static fn float(f: f64) -> SdnValue:\n        SdnValue.Float(f)\n\n    static fn string(s: text) -> SdnValue:\n        SdnValue.String(s)\n\n    static fn array(items: [SdnValue]) -> SdnValue:\n        SdnValue.Array(items)\n\n    static fn empty_array() -> SdnValue:\n        SdnValue.Array([])\n\n    static fn empty_dict() -> SdnValue:\n        SdnValue.Dict({})\n\n")
expect(errors.len()).to_equal(0)
```

</details>

#### reject nonempty wrong element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Empty\n    Array([Value])\nfn make() -> Value:\n    Value.Array([1])\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

#### reject wrong following argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Pair([i64], text)\nfn make() -> Value:\n    Value.Pair([], 17)\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

#### reject wrong nested element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Matrix([[i64]])\nfn make() -> Value:\n    Value.Matrix([[\"bad\"]])\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

#### mixed empty and nonempty nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Matrix([[i64]])\nfn make() -> Value:\n    Value.Matrix([[], [1]])\n")
expect(errors.len()).to_equal(0)
```

</details>

#### dictionary with nested empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Map(Dict<text, [f64]>)\nfn make() -> Value:\n    Value.Map({\"a\": []})\n")
expect(errors.len()).to_equal(0)
```

</details>

#### named empty payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Named(items: [f64])\nfn make() -> Value:\n    Value.Named(items: [])\n")
expect(errors.len()).to_equal(0)
```

</details>

#### reject wrong dictionary key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Map(Dict<text, [f64]>)\nfn make() -> Value:\n    Value.Map({7: []})\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

#### reject conflicting typed dictionary variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Map(Dict<text, i64>)\nfn make() -> Value:\n    val values: Dict<i64, i64> = {}\n    Value.Map(values)\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

#### decode then insert and access float payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Floats([f64])\nfn probe() -> f64:\n    val value = Value.Floats([])\n    match value:\n        case Value.Floats(items):\n            items.push(1.5)\n            items[0]\n        case _: 0.0\n")
expect(errors.len()).to_equal(0)
```

</details>

### declared enum collection MIR metadata

#### emits an empty float array with the declared MIR element type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = contextual_payload_mir_types("enum Value:\n    Floats([f64])\nfn make() -> Value:\n    Value.Floats([])\n")
expect(evidence).to_contain("array-f64")
expect(evidence.contains("errors")).to_equal(false)
```

</details>

#### emits declared dictionary key and nested value MIR types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = contextual_payload_mir_types("enum Value:\n    Map(Dict<text, [f64]>)\nfn make() -> Value:\n    Value.Map({})\n")
expect(evidence).to_contain("dict-str-array-f64")
expect(evidence.contains("errors")).to_equal(false)
```

</details>

### explicit payload type authority

#### rejects an explicitly typed empty array variable of another element type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Floats([f64])\nfn make() -> Value:\n    val values: [text] = []\n    Value.Floats(values)\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

#### rejects an empty array cast to another element type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = contextual_payload_errors("enum Value:\n    Floats([f64])\nfn make() -> Value:\n    Value.Floats([] as [text])\n")
expect(errors.len() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/mir/contextual_enum_payload_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering declared enum payload contextual containers, declared enum collection MIR metadata, explicit payload type authority.
- declared enum payload contextual containers
- declared enum collection MIR metadata
- explicit payload type authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
