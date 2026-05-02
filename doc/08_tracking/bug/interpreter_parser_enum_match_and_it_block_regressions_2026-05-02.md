# Bug: Named-Field Enum Match Patterns + Two it-Block Parser Issues

**Date:** 2026-05-02
**Severity:** High (blocks writing idiomatic encoding/decoding modules and spec tests)
**Affected modes:** Interpreter (all three bugs); compiled mode not verified

---

## Bug 1: Named-field enum match patterns fail to parse

### Description

Match arms using named-field binding syntax (`case Variant(field: bind):`) fail with a parse error:

```
expected Comma, found Colon
```

This affects every encoding module that was written with named enum fields: `bencode.spl`, `msgpack.spl`, `protobuf_wire.spl`, and `bson.spl`.

### Minimal repro

```spl
enum Foo:
  Bar(value: i64)

fn test(x: Foo) -> i64:
  match x:
    case Foo.Bar(value: v):   # ← parse error: expected Comma, found Colon
      v
```

### Workaround

Rewrite all enum fields and match arms to use **positional** form throughout:

```spl
enum Foo:
  Bar(i64)

fn test(x: Foo) -> i64:
  match x:
    case Foo.Bar(v):
      v
```

Also note: a wildcard `_` in a named-field position (`case Foo.Bar(value: _):`) triggers the same error.

### Affected files (already worked around)

- `src/lib/common/encoding/bson.spl` — rewritten to positional
- `src/lib/common/encoding/bencode.spl` — still uses named fields (not yet worked around)
- `src/lib/common/encoding/msgpack.spl` — still uses named fields (not yet worked around)
- `src/lib/common/encoding/protobuf_wire.spl` — still uses named fields (not yet worked around)

---

## Bug 2: `{...}` in `it` description strings triggers template interpolation

### Description

Inside `describe`/`it` blocks, a description string containing `{identifier:...}` or any `{...}` content is parsed as a template interpolation expression. If the identifier does not name a variable in scope, the compiler/interpreter reports:

```
variable `<name>` not found
```

### Minimal repro

```spl
it "encodes {a:1} as 0x0C bytes":
  expect(true).to_equal(true)
```

Triggers: `variable 'a' not found` (even though the string is a description, not a template).

### Workaround

Use plain English descriptions with no `{...}` syntax in `it` / `describe` strings:

```spl
it "encodes the a-equals-1 document as 12 bytes":
  expect(true).to_equal(true)
```

---

## Bug 3: Bitwise-AND chain `expect(x & 0xFF).to_equal(y)` misbehaves inside `it` blocks

### Description

Inside `it` blocks, an expression of the form:

```spl
expect(b[0].to_i64() & 0xFF).to_equal(0x0C)
```

produces incorrect results — e.g., `expected 0 ? 255 to hold` — even when the value is correct. The same expression extracted into a module-level helper function returns the expected result.

This appears to be related to the general "chained methods broken" interpreter limitation combined with how `it`-block closures capture variables, but the exact root cause is unknown.

### Workaround

Move all byte-level assertions into module-level helper functions that return `bool`, and have `it` blocks only call `expect(helper_fn()).to_equal(true)`:

```spl
fn _check_byte(b: [u8]) -> bool:
  b[0].to_i64() & 0xFF == 0x0C

it "first byte is 0x0C":
  expect(_check_byte(result)).to_equal(true)
```

---

## Impact summary

All three bugs were encountered and worked around during implementation of `src/lib/common/encoding/bson.spl` and `test/unit/lib/common/encoding/bson_spec.spl`. The workarounds are stable (29 tests pass), but the underlying issues should be fixed in the parser/interpreter so that the idiomatic patterns can be used.
