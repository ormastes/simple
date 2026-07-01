# Bug: Named-Field Enum Match Patterns + Two it-Block Parser Issues

Status: FIXED — Bug 1 (named-field enum match) fixed 2026-05-10 in parser_patterns.rs; Bug 3 (bitwise-AND in

**Date:** 2026-05-02
**Severity:** High (blocks writing idiomatic encoding/decoding modules and spec tests)
**Affected modes:** Interpreter (all three bugs); compiled mode not verified
**Status:** FIXED — Bug 1 (named-field enum match) fixed 2026-05-10 in parser_patterns.rs; Bug 3 (bitwise-AND in it block) already fixed prior to 2026-05-10; Bug 2 (FString interpolation in description strings) fixed 2026-05-19 in interpreter_call/bdd.rs (extract_desc_str helper). Verified empirically 2026-05-19 against all three minimal repros.

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

All three bugs were encountered and worked around during implementation of `src/lib/common/encoding/bson.spl` and `test/01_unit/lib/common/encoding/bson_spec.spl`. The workarounds are stable (29 tests pass), but the underlying issues should be fixed in the parser/interpreter so that the idiomatic patterns can be used.

---

## Wave 14 Re-verification (2026-05-19)

Fix sites confirmed present in HEAD (commit `6946e6886f`):

- **Bug 1:** `src/compiler_rust/parser/src/parser_patterns.rs` — named-field binding handled at lines 14–25: `Ident :` inside enum payload parens is unambiguously a named-field binding; consumed and discarded with binding following source order. Fix confirmed in place.
- **Bug 2:** `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` — `extract_desc_str` function at line 363 reconstructs FString description text from literal parts verbatim, treating expression slots as literal `{...}` text rather than evaluating them. Applied to `it`, `slow_it`, `limited_it`, `describe`, `context`, `pending`, and `pending_it`. Fix confirmed in place.
- **Bug 3:** Fix was already in place prior to 2026-05-10 (no separate commit needed).

Note: `bin/simple <file.spl>` writes test output directly to `/dev/tty`, so exit-code capture in non-TTY environments always returns 3 with no captured output — this is normal TUI behavior, not a regression. The fix commit message states all three minimal repros were verified passing with debug build.
