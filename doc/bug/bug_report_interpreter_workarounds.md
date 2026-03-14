# Interpreter Bug Workarounds

Summary of known interpreter-mode bugs and their workarounds. These bugs affect code running in interpreter mode (`bin/simple run`). Compiled mode may not exhibit these issues.

**Last Updated:** 2026-03-14

---

## Bug Index

| # | Bug | Severity | Status | Test |
|---|-----|----------|--------|------|
| 1 | Module-level `.len()` corrupts variable | P2 | Open | `memory/bug_len_corruption.md` |
| 2 | `substring()` is destructive | P2 | Open | `memory/language_substring_mutation.md` |
| 3 | Module-level `.push()` → "unsupported path call" | P2 | Open | `test/bug/interp_push_spec.spl` |
| 4 | `split("\n")` strips leading whitespace | P2 | Open | `test/bug/interp_split_ws_spec.spl` |
| 5 | `rt_cli_get_args()` includes runtime args | P3 | Open | `test/bug/interp_cli_args_spec.spl` |
| 6 | Double execution in interpreter | P2 | Open | `test/bug/interp_double_exec_spec.spl` |

---

## Bug 1: Module-level `.len()` corrupts variable

**Severity:** P2
**Discovered:** Pre-existing
**Component:** Interpreter — array method dispatch

### Description

Calling `.len()` on a module-level array variable corrupts the variable itself. After `.len()` is called, the array may become unusable or return incorrect values.

### Workaround

Use a manual counter variable alongside the array:

```simple
var MY_ARRAY: [text] = []
var MY_COUNT = 0  # manual counter

fn add_item(item: text):
    MY_ARRAY = MY_ARRAY + [item]
    MY_COUNT = MY_COUNT + 1

# Use MY_COUNT instead of MY_ARRAY.len()
```

### Impact

Affects all module-level arrays. Local variables are NOT affected — `.len()` works correctly on local arrays.

---

## Bug 2: `substring()` is destructive

**Severity:** P2
**Discovered:** Pre-existing
**Component:** Interpreter — string method dispatch

### Description

Calling `.substring()` on a string mutates the original variable instead of returning a new string. The original string is modified in-place.

### Workaround

Use slice syntax `s[start:end]` instead of `.substring(start, end)`:

```simple
# BAD: mutates original
# val part = original.substring(0, 5)

# GOOD: non-destructive slice
val part = original[0:5]
```

### Impact

Affects all string variables. Use slice syntax consistently throughout codebase.

---

## Bug 3: Module-level `.push()` → "unsupported path call"

**Severity:** P2
**Discovered:** 2026-03-14
**Component:** Interpreter — module-level method resolution
**Test:** `test/bug/interp_push_spec.spl`

### Description

Calling `.push()` on a module-level array variable produces an "unsupported path call" error at runtime. The interpreter fails to resolve the `.push()` method when the receiver is a module-level `var`.

### Workaround

Use array concatenation assignment instead of `.push()`:

```simple
var MODULE_ARRAY: [text] = []

# BAD: "unsupported path call"
# MODULE_ARRAY.push("item")

# GOOD: concatenation
MODULE_ARRAY = MODULE_ARRAY + ["item"]
```

### Impact

Affects all module-level arrays. Local variables work fine with `.push()`. This is the same class of bug as `.len()` corruption — module-level method dispatch is broken.

---

## Bug 4: `split("\n")` strips leading whitespace

**Severity:** P2
**Discovered:** 2026-03-14
**Component:** Interpreter — string split method
**Test:** `test/bug/interp_split_ws_spec.spl`

### Description

When splitting a string by `"\n"`, the resulting array elements have their leading whitespace stripped. This breaks any parsing that relies on indentation (e.g., SDN config files, YAML-like formats).

### Workaround

Use manual line parsing with index scanning:

```simple
fn _parse_lines_preserving_indent(content: text) -> [text]:
    var lines: [text] = []
    var start = 0
    var pos = 0
    val clen = content.len()
    while pos < clen:
        val ch = content[pos:pos + 1]
        if ch == "\n":
            val line = content[start:pos]
            lines.push(line)
            start = pos + 1
        pos = pos + 1
    if start < clen:
        val line = content[start:clen]
        lines.push(line)
    lines
```

### Impact

Affects all SDN/config parsing. The `_parse_lines_with_indent()` function in `main.spl` uses this workaround pattern.

---

## Bug 5: `rt_cli_get_args()` includes runtime args

**Severity:** P3
**Discovered:** 2026-03-14
**Component:** Runtime — CLI argument passthrough
**Test:** `test/bug/interp_cli_args_spec.spl`

### Description

`rt_cli_get_args()` returns ALL command-line arguments, including the runtime's own arguments (e.g., `simple`, `run`, `path/to/script.spl`). User code receives unwanted prefix arguments.

### Workaround

Strip arguments up to and including the `.spl` script path:

```simple
fn strip_runtime_args(raw_args: [text]) -> [text]:
    var user_args: [text] = []
    var found_script = false
    for a in raw_args:
        if found_script:
            user_args.push(a)
        elif a.ends_with(".spl"):
            found_script = true
    user_args
```

### Impact

Every program using CLI arguments must apply this stripping. The pattern is used in `main.spl`'s main function.

---

## Bug 6: Double execution in interpreter

**Severity:** P2
**Discovered:** 2026-03-14
**Component:** Interpreter — module loading
**Test:** `test/bug/interp_double_exec_spec.spl`

### Description

The interpreter executes top-level code twice during module loading. This causes side effects to run twice: duplicate prints, double initialization, incorrect counter values.

### Workaround

Use a guard flag to prevent re-entry:

```simple
var MAIN_EXECUTED = false

fn main():
    if MAIN_EXECUTED:
        return
    MAIN_EXECUTED = true
    # ... actual main logic ...

main()
```

### Impact

Every program with top-level side effects must use this guard pattern. The `MAIN_EXECUTED` flag is standard in all `main.spl` entry points.

---

## Summary of Workaround Patterns

| Bug | Pattern | Replace With |
|-----|---------|--------------|
| `.len()` corruption | `arr.len()` on module var | Manual counter variable |
| `substring()` mutation | `s.substring(start, end)` | `s[start:end]` slice |
| `.push()` unsupported | `arr.push(item)` on module var | `arr = arr + [item]` |
| `split("\n")` whitespace | `s.split("\n")` | Manual index-scanning parser |
| `rt_cli_get_args()` | Direct use of raw args | Strip up to `.spl` path |
| Double execution | Bare top-level code | `MAIN_EXECUTED` guard flag |
