# Runtime Parser Bugs Reproduction Specification

> Reproduction tests for 9 runtime parser/interpreter bugs discovered during Remote RISC-V 32 debug module implementation (2026-02-06).

<!-- sdn-diagram:id=runtime_parser_bugs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_parser_bugs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_parser_bugs_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_parser_bugs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Parser Bugs Reproduction Specification

Reproduction tests for 9 runtime parser/interpreter bugs discovered during Remote RISC-V 32 debug module implementation (2026-02-06).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BUG-RT-001 through #BUG-RT-009 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/common/runtime_parser_bugs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Reproduction tests for 9 runtime parser/interpreter bugs discovered
during Remote RISC-V 32 debug module implementation (2026-02-06).

These tests document known limitations of the bootstrap runtime parser
and verify that workarounds function correctly.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Slice syntax | `s[start:end]` string/array slicing |
| Dict.get() | Dictionary key lookup method |
| Reserved words | Identifiers the parser treats as keywords |
| Function fields | Class fields with function types |

## Behavior

- Bug tests marked `skip` will fail on bootstrap runtime (expected)
- Workaround tests should always pass
- When a bug is fixed in the runtime, remove the `skip` tag

## Related Specifications

- [Runtime Parser Bugs Report](../../doc/09_report/runtime_parser_bugs_2026-02-06.md)

## Scenarios

### BUG-RT-001: Slice syntax [:variable]

#### workaround: explicit 0 start

#### slices string with s[0:end]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
val end = 5
val result = s[0:end]
expect(result).to_equal("hello")
```

</details>

#### slices with expression s[0:s.len()-1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val slen = s.len()
val result = s[0:slen - 1]
expect(result).to_equal("hell")
```

</details>

#### trims trailing char with explicit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = "quoted\""
val slen = s.len()
s = s[0:slen - 1]
expect(s).to_equal("quoted")
```

</details>

#### literal end works

#### slices with literal s[:3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val result = s[:3]
expect(result).to_equal("hel")
```

</details>

#### omitted end works

#### slices with s[1:]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val result = s[1:]
expect(result).to_equal("ello")
```

</details>

### BUG-RT-002: Dict.get() return type

#### workaround: nil check

#### finds existing key with nil check

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, text> = {}
d["key"] = "value"
val got = d.get("key")
if got != nil:
    expect(got).to_equal("value")
else:
    fail("should have found key")
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, text> = {}
d["key"] = "value"
val got = d.get("missing")
expect(got == nil).to_equal(true)
```

</details>

#### works with null coalescing operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, text> = {}
d["key"] = "value"
expect(d.get("key") ?? "default").to_equal("value")
expect(d.get("missing") ?? "default").to_equal("default")
```

</details>

#### workaround: Dict with array values

#### stores and retrieves arrays with nil check

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, [text]> = {}
d["items"] = ["a", "b", "c"]
val got = d.get("items")
if got != nil:
    expect(got.len()).to_equal(3)
    expect(got[0]).to_equal("a")
else:
    fail("should have found items")
```

</details>

#### workaround: contains_key

#### checks key existence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, text> = {}
d["key"] = "value"
expect(d.has("key")).to_equal(true)
expect(d.has("missing")).to_equal(false)
```

</details>

#### workaround: in operator

#### checks membership

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d: Dict<text, text> = {}
d["key"] = "value"
if "key" in d:
    pass
else:
    fail("'key' should be in d")
```

</details>

#### workaround: mutable class method with nil check

#### registers and looks up handlers

- var reg = BugTestRegistry empty
- reg add
   - Expected: reg.lookup("halt") is true
   - Expected: reg.lookup("missing") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = BugTestRegistry.empty()
reg.add("halt", "gdb_handler")
expect(reg.lookup("halt")).to_equal(true)
expect(reg.lookup("missing")).to_equal(false)
```

</details>

### BUG-RT-003: 'feature' reserved word

#### workaround: rename to feat

#### uses feat as field name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BugTestHandler.of("halt", 0)
expect(h.feat).to_equal("halt")
```

</details>

#### uses feat as parameter name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bug_test_lookup_feat("halt")
expect(result).to_equal("found: halt")
```

</details>

### BUG-RT-004: 'class' reserved word

#### workaround: rename to cls

#### uses cls in match pattern

- BugTestRecord Info
   - Expected: cls equals `done`
   - Expected: msg equals `ok`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = BugTestRecord.Info(cls: "done", msg: "ok")
match record:
    BugTestRecord.Info(cls, msg):
        expect(cls).to_equal("done")
        expect(msg).to_equal("ok")
    _:
        fail("wrong match")
```

</details>

### BUG-RT-005: static val not supported

#### workaround: static fn getter

#### uses static fn instead of static val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BugTestConstants.NATIVE()).to_equal(0)
expect(BugTestConstants.BRIDGE()).to_equal(1)
expect(BugTestConstants.EMULATED()).to_equal(4)
```

</details>

### BUG-RT-006: val field defaults

#### workaround: factory method

#### uses static fn create with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = BugTestTarget.create()
var n = t.names
expect(n.len()).to_equal(3)
expect(n[0]).to_equal("zero")
expect(n[1]).to_equal("ra")
expect(n[2]).to_equal("sp")
```

</details>

### BUG-RT-007: empty class body

#### workaround: dummy field

#### uses _unused field for empty class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BugTestEmptyClass(_unused: 0)
expect(p.do_work()).to_equal("works")
```

</details>

### BUG-RT-008: named params in fn types

#### workaround: unnamed params

#### uses fn([text]) without param names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BugTestFnHolder.of("got {_1.len()} items")
val cb = h.callback
val result = cb(["a", "b"])
expect(result).to_equal("got 2 items")
```

</details>

### BUG-RT-009: fn field direct call

#### workaround: extract to local variable

#### extracts fn field then calls it

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BugTestFnHolder.of("processed {_1.len()}")
# Extract to local first
val cb = h.callback
val result = cb(["x", "y", "z"])
expect(result).to_equal("processed 3")
```

</details>

#### works with Result-returning fn fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BugTestResultHolder.of(\items: Ok("ok: {items.len()}"))
val handler = h.handler
val result = handler(["a"])
expect(result.ok.?).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
