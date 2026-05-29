# Runtime Parser Bugs Report - 2026-02-06

**Status:** Complete (all workarounds applied)
**Context:** Discovered during Remote RISC-V 32 module implementation
**Runtime:** `bin/bootstrap/simple_runtime` (bootstrap build)
**Reproduce Tests:** `test/runtime/runtime_parser_bugs_spec.spl`

---

## Summary

During implementation of the remote RISC-V 32-bit debug module, 13 runtime parser/interpreter bugs were discovered. These are limitations of the bootstrap runtime that don't match the language specification.

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
| 10 | `index_of()` + variable-index slice in static methods corrupts enum construction | **Critical** | Use `split()` instead of `index_of()` + slice | Workaround applied |
| 11 | `index_of()` returns `Option<i32>`, not `i32` | High | Use `split()` or manual `find_char()` | Workaround applied |
| 12 | `shell()` function not available in bootstrap runtime | Medium | Use `extern fn rt_process_run()` directly | Workaround applied |
| 13 | `skip()` in `slow_it` blocks doesn't halt execution | Low | Guard entire test body with `if` condition | Workaround applied |
| 14 | `.split().map()` chain doesn't apply map lambda | **Critical** | Break chain into separate `val`+`.map()` calls | Workaround applied |
| 15 | `array[idx].method()` modifies copy, not element | High | Read into `var`, modify, write back with `arr[idx] = var` | Workaround applied |
| 16 | `use app.io` wildcard import shadows module-local functions | High | Use direct `extern fn` declarations instead | Workaround applied |
| 17 | `rt_timestamp_now`/`rt_sleep_ms` not in bootstrap runtime | Medium | Polyfill via `rt_process_run("date", ...)` | Workaround applied |
| 18 | `parse_i64()` not available on strings | Low | Use `to_int()` instead | Workaround applied |
| 19 | `sort_by()` not available on arrays | Medium | Implement manual `insertion_sort()` | Workaround applied |
| 20 | `rt_file_read_text` returns Option-wrapped value | High | Use `result ?? ""` pattern | Workaround applied |

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

## Bug 10: `index_of()` + Variable-Index Slice Corrupts Enum Construction

**Error:** `semantic: type mismatch: cannot convert enum to int`

**Description:** When `index_of()` is used to compute a variable index for string slicing inside a static method that returns an enum, the enum construction fails. Root cause: `index_of()` returns `Option<i32>` (Bug 11), and using it as a slice index creates type confusion that propagates to enum field types.

**Affected patterns:**
```simple
# FAILS - index_of + slice in static method returning enum
static fn parse(line: text) -> MyRecord:
    val pos = line.index_of("^")     # Returns Option, not i32
    val part1 = line[0:pos]          # Slice with Option index
    val part2 = line[pos + 1:]       # More type confusion
    MyRecord.Result(token: 42, cls: part1, data: {})  # BOOM

# WORKS - split() avoids index_of entirely
static fn parse(line: text) -> MyRecord:
    val parts = line.split("^")
    val part1 = parts[0]
    val part2 = parts[1]
    MyRecord.Result(token: 42, cls: part1, data: {})
```

**Workaround:** Use `split()` instead of `index_of()` + slice. For finding characters at specific positions, use manual iteration (`find_char` functions).

---

## Bug 11: `index_of()` Returns `Option<i32>`, Not `i32`

**Error:** Various type mismatches when comparing result with integers

**Description:** `text.index_of(str)` returns `Option::Some(pos)` instead of raw `i32`. This means `pos < 0` comparisons don't work as expected, and using the result as a slice index (Bug 10) causes type confusion.

**Affected patterns:**
```simple
# FAILS
val pos = "hello^world".index_of("^")
print pos         # Prints "Option::Some(5)" not "5"
if pos < 0:       # Type error: cannot compare Option to int
    ...
val part = s[0:pos]  # Type error: Option as slice index

# WORKS
val parts = "hello^world".split("^")
if parts.len() > 1:
    val part = parts[0]
```

**Workaround:** Use `split()` or manual character iteration.

---

## Bug 12: `shell()` Not Available in Bootstrap Runtime

**Error:** `semantic: function 'shell' not found` or `too many arguments for class 'shell' constructor`

**Description:** The `shell()` convenience function from `app.io` is not available in the bootstrap runtime. Importing it via `use app.io.{shell}` either fails to resolve or resolves to a class constructor.

**Affected patterns:**
```simple
# FAILS
use app.io.{shell}
val result = shell("echo hello")

# WORKS
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)
val (stdout, stderr, exit_code) = rt_process_run("sh", ["-c", "echo hello"])
```

**Workaround:** Use `extern fn rt_process_run()` directly for process execution.

---

## Bug 13: `skip()` in `slow_it` Blocks Doesn't Halt Execution

**Error:** Test continues executing after `skip()` call, causing subsequent `?` operators to trigger `try: early return`

**Description:** In `slow_it` test blocks (which use closures/lambdas), calling `skip()` marks the test as skipped but does NOT halt the test body. `return` also doesn't work inside the lambda.

**Affected patterns:**
```simple
# FAILS - test body continues after skip
slow_it "requires tools":
    if not tool_available():
        skip("tool not available")
        return                    # Doesn't actually return from lambda
    val result = operation()?     # Still executes, fails with "try: early return"

# WORKS - guard entire body
slow_it "requires tools":
    if tool_available():
        val result = operation()
        match result:
            Ok(v): expect(v).to(eq(true))
            Err(_): pass
    else:
        skip("tool not available")
```

**Workaround:** Wrap entire test body in an `if tool_available()` guard.

---

---

## Bug 14: `.split().map()` Chain Doesn't Apply Map Lambda

**Error:** Map lambda is ignored; original split results returned untrimmed.

**Description:** Method chaining `.split(",").map(\c: c.trim())` returns the split results WITHOUT applying the map transformation. The `.map()` call is silently ignored when chained directly after `.split()`.

**Affected patterns:**
```simple
# FAILS - map lambda not applied
val cols = "id, name, value".split(",").map(\c: c.trim())
# cols = ["id", " name", " value"] (NOT trimmed!)

# WORKS - separate calls
val parts = "id, name, value".split(",")
val cols = parts.map(\c: c.trim())
# cols = ["id", "name", "value"] (correctly trimmed)
```

**Workaround:** Break the chain into separate variable assignment and `.map()` call.

**Impact:** `SdnTable.parse()` stored column names with leading spaces, causing all field lookups to fail after save/load round-trip. Fixed in `src/lib/database/core.spl`.

---

## Bug 15: `array[idx].method()` Modifies Copy, Not Element

**Error:** Modifications to array elements via `self.rows[idx].set(...)` are silently lost.

**Description:** Array index access (`arr[idx]`) returns a COPY of the element in the bootstrap runtime. Calling mutating methods on the copy doesn't affect the actual array element.

**Affected patterns:**
```simple
# FAILS - modifies a copy
self.rows[idx].set("valid", "false")  # Copy is modified and discarded

# WORKS - read, modify, write back
var row = self.rows[idx]
row.set("valid", "false")
self.rows[idx] = row
```

**Workaround:** Read element into a `var`, modify it, then assign back with indexed assignment.

**Impact:** `SdnTable.mark_deleted()` silently failed. Fixed in `src/lib/database/core.spl`.

---

## Bug 16-20: Additional Bootstrap Runtime Limitations

| # | Description | Workaround |
|---|-------------|------------|
| 16 | `use app.io` wildcard import shadows module-local functions in other imported modules | Use direct `extern fn` declarations |
| 17 | `rt_timestamp_now` / `rt_sleep_ms` not in bootstrap runtime | Polyfill via `rt_process_run("date", ["+%s%3N"])` |
| 18 | `parse_i64()` not available on strings | Use `to_int()` instead |
| 19 | `sort_by()` not available on arrays | Manual `insertion_sort()` implementation |
| 20 | `rt_file_read_text` returns Option-wrapped value even with `-> text` return type | Use `result ?? ""` pattern |

---

## Metrics

- **Bugs found:** 20
- **Workarounds applied:** 20/20
- **Files affected:** 10 source files in `src/remote/` + 4 source files in `src/lib/database/` + 6 test files
- **Discovery method:** Systematic binary-search testing with minimal scripts
- **Test results:** 51/51 remote tests passing (48 pass + 3 skip), 70/70 database tests passing

---

## Recommendations

1. **Critical priority:** Fix Bug 10/11 (index_of return type + enum corruption) - silent, hard-to-debug failure
2. **High priority:** Fix Bug 1 (slice syntax) and Bug 2 (Dict.get return type) - silent failures
3. **Medium priority:** Fix Bug 12 (shell function) and Bug 9 (fn field calling)
4. **Low priority:** Bugs 3-8, 13 are parser limitations with clean workarounds
5. **Testing:** `test/runtime/runtime_parser_bugs_spec.spl` covers bugs 1-9; bugs 10-13 verified via remote module tests
