# Runtime Parser Bugs Report - 2026-02-06

**Status:** In Progress
**Context:** Discovered during Remote RISC-V 32 module implementation
**Runtime:** `bin/bootstrap/simple_runtime` (bootstrap build)
**Reproduce Tests:** `test/runtime/runtime_parser_bugs_spec.spl`

---

## Summary

During implementation of the remote RISC-V 32-bit debug module, 9 runtime parser/interpreter bugs were discovered. These are limitations of the bootstrap runtime that don't match the language specification.

### Bug Table

| # | Bug | Severity | Workaround | Status |
|---|-----|----------|------------|--------|
| 1 | `s[:variable]` slice treats `:variable` as symbol | High | Use `s[0:variable]` | Workaround applied |
| 2 | `Dict.get()` returns raw value, not `Option<T>` | High | Use nil check instead of `match Some/None` | Workaround applied |
| 3 | `feature` is a reserved word in parameter context | Medium | Rename to `feat` | Workaround applied |
| 4 | `class` is a reserved word in all identifier contexts | Medium | Rename to `cls` | Workaround applied |
| 5 | `static val` not supported in class bodies | Medium | Use `static fn` getter | Workaround applied |
| 6 | `val` field defaults not supported in class bodies | Medium | Use factory method + plain field | Workaround applied |
| 7 | Empty class body before `impl` block fails parse | Low | Add `_unused: i32` dummy field | Workaround applied |
| 8 | Named params in fn types cause parse error | Low | Remove param names from fn type | Workaround applied |
| 9 | Calling fn-typed class fields directly fails | Medium | Extract to local `val` first | Workaround applied |

---

## Bug 1: Slice Syntax `[:variable]` Treated as Symbol

**Error:** `semantic: cannot index string with type 'symbol'`
**Also:** `semantic: method 'len' not found on type 'symbol' (receiver value: :s)`

**Description:** When using slice syntax `s[:end]` where `end` is a variable, the runtime parser interprets `:end` as a symbol literal instead of the slice start-omitted syntax.

**Affected patterns:**
```simple
# FAILS - :end becomes symbol :end
val result = s[:end]
s = s[:s.len() - 1]
inner = inner[:inner.len() - 1]

# WORKS - literal end value
val result = s[:3]

# WORKS - explicit start value
val result = s[0:end]
s = s[0:s.len() - 1]
```

**Workaround:** Always use explicit `0` start: `s[0:variable]` instead of `s[:variable]`.

**Root cause:** The lexer/parser doesn't distinguish between `:identifier` (symbol) and `[: identifier]` (slice with omitted start) when the end index is a variable expression.

---

## Bug 2: Dict.get() Returns Raw Value, Not Option

**Error:** `match` on `Some/None` always falls through to default arm.

**Description:** `Dict.get(key)` returns the raw value directly (or `nil` for missing keys), NOT wrapped in `Some(value)` / `None` as the language spec implies. This means `match dict.get(key): Some(x): ... None: ...` patterns silently fail.

**Affected patterns:**
```simple
# FAILS - dict.get() doesn't return Option
match self.handlers.get(key):
    Some(list):
        list.len() > 0    # Never reached
    None:
        false              # Never reached either
    # Falls through to implicit default, returns nil

# WORKS - nil check
val list = self.handlers.get(key)
if list != nil:
    list.len() > 0
else:
    false

# WORKS - null coalescing
val value = dict.get("key") ?? "default"
```

**Workaround:** Replace all `match dict.get(): Some/None` with `if val != nil` pattern.

**Impact:** Any code using the standard Option-matching pattern on Dict.get() silently produces wrong results.

---

## Bug 3: `feature` is a Reserved Word

**Error:** `semantic: expected Comma, found Colon` when used as parameter name.

**Description:** The identifier `feature` is treated as a keyword/reserved word in function parameter context. Using it as a field name, parameter name, or variable name in certain contexts causes parse errors.

**Affected patterns:**
```simple
# FAILS
class Handler:
    feature: FeatureId    # Parse error

fn lookup(feature: FeatureId):    # Parse error
    feature.to_string()

# WORKS
class Handler:
    feat: FeatureId       # Renamed

fn lookup(feat: FeatureId):    # Renamed
    feat.to_string()
```

**Workaround:** Use `feat` instead of `feature`.

---

## Bug 4: `class` is a Reserved Word in All Contexts

**Error:** `semantic: expected pattern, found Class`

**Description:** `class` cannot be used as a variable name in match patterns, field names, or local variables, even though it's a valid field name in GDB MI protocol types.

**Affected patterns:**
```simple
# FAILS
match record:
    GdbMiRecord.Result(token, class, data):  # Parse error
        print class

# WORKS
match record:
    GdbMiRecord.Result(token, cls, data):    # Renamed
        print cls
```

**Workaround:** Use `cls` instead of `class`.

---

## Bug 5: `static val` Not Supported in Class Bodies

**Error:** `semantic: expected Fn, found Val`

**Description:** The runtime parser doesn't support `static val` (compile-time constant fields) inside class bodies. Only `static fn` is supported.

**Affected patterns:**
```simple
# FAILS
class FeatureRank:
    static val NATIVE: i32 = 0
    static val BRIDGE: i32 = 1

# WORKS
class FeatureRank:
    static fn NATIVE() -> i32:
        0
    static fn BRIDGE() -> i32:
        1
```

**Workaround:** Convert `static val` to `static fn` getters. Call with `FeatureRank.NATIVE()`.

---

## Bug 6: `val` Field Defaults Not Supported

**Error:** `semantic: expected identifier, found Val`

**Description:** Default values for class fields using `val field: Type = default_value` are not supported by the runtime parser.

**Affected patterns:**
```simple
# FAILS
class Target:
    val abi_names: [text] = ["zero", "ra", "sp"]

# WORKS
class Target:
    abi_names: [text]

    static fn create() -> Target:
        Target(abi_names: ["zero", "ra", "sp"])
```

**Workaround:** Use plain fields with a factory `static fn`.

---

## Bug 7: Empty Class Body Before `impl` Block

**Error:** `semantic: expected Indent, found Impl`

**Description:** A class with no fields (empty body) followed by an `impl` block fails to parse.

**Affected patterns:**
```simple
# FAILS
class MyParser:

impl MyParser:
    static fn parse(line: text) -> text:
        line

# WORKS
class MyParser:
    _unused: i32

impl MyParser:
    static fn parse(line: text) -> text:
        line
```

**Workaround:** Add a dummy `_unused: i32` field.

---

## Bug 8: Named Parameters in Function Types

**Error:** `semantic: expected Comma, found Colon`

**Description:** Function type signatures with named parameters fail to parse. Only unnamed parameter types are supported.

**Affected patterns:**
```simple
# FAILS
handler_fn: fn(args: [text]) -> Result<text, text>

# WORKS
handler_fn: fn([text]) -> Result<text, text>
```

**Workaround:** Remove parameter names from function types.

---

## Bug 9: Cannot Call Function-Typed Class Fields Directly

**Error:** `semantic: method 'handler_fn' not found`

**Description:** When a class has a field of function type, calling it directly as a method fails. The runtime treats it as a method lookup instead of a field access + call.

**Affected patterns:**
```simple
class Handler:
    handler_fn: fn([text]) -> Result<text, text>

# FAILS
val result = handler.handler_fn(args)

# WORKS
val callback = handler.handler_fn
val result = callback(args)
```

**Workaround:** Extract the function field into a local variable, then call it.

---

## Metrics

- **Bugs found:** 9
- **Workarounds applied:** 9/9
- **Files affected:** 8 source files in `src/remote/` + 1 test file
- **Discovery method:** Systematic binary-search testing with minimal scripts

---

## Recommendations

1. **High priority:** Fix Bug 1 (slice syntax) and Bug 2 (Dict.get return type) - these are silent failures
2. **Medium priority:** Fix Bug 9 (fn field calling) - common pattern in functional code
3. **Low priority:** Bugs 3-8 are parser limitations that have clean workarounds
4. **Testing:** Add `test/runtime/runtime_parser_bugs_spec.spl` to regression suite
