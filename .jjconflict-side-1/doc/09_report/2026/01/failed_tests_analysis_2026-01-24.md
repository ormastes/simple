# Failed Test Analysis Report

**Generated:** 2026-01-24
**Total Failed:** 14 tests
**Location:** `test/lib/std/unit/tooling/`

---

## Summary by Error Type

| Error Type | Count | Tests |
|------------|-------|-------|
| `expected expression, found Return` | 9 | base64, color, csv, ds, format, json, list, path, string |
| `expected Newline, found ...` | 2 | html, markdown |
| `Inline if expression requires else` | 1 | math |
| `undefined identifier` | 1 | parse |
| `expected expression, found Newline` | 1 | url |

---

## Detailed Analysis

### Category 1: Return Statement in Expression Context (9 tests)

**Error Message:**
```
parse error: Unexpected token: expected expression, found Return
```

**Affected Files:**
- `base64_utils_spec.spl`
- `color_utils_spec.spl`
- `csv_utils_spec.spl`
- `ds_utils_spec.spl`
- `format_utils_spec.spl`
- `json_utils_spec.spl`
- `list_utils_spec.spl`
- `path_utils_spec.spl`
- `string_utils_spec.spl`

**Root Cause:**
The code uses `return` statements inside single-line `if` expressions where the parser expects an expression, not a statement.

**Example (base64_utils_spec.spl:12-14):**
```simple
fn char_to_byte(c: text) -> i64:
    if c == "A": return 65    # ERROR: return is a statement, not expression
    if c == "B": return 66
```

**Fix Required:**
Replace single-line `if` with `return` to proper multi-line `if-else` blocks or use expression-based patterns:

**Option A - Multi-line if blocks:**
```simple
fn char_to_byte(c: text) -> i64:
    if c == "A":
        return 65
    if c == "B":
        return 66
    0
```

**Option B - Match expression:**
```simple
fn char_to_byte(c: text) -> i64:
    match c:
        case "A": 65
        case "B": 66
        case _: 0
```

---

### Category 2: Single-line Function Definition Syntax (1 test)

**Error Message:**
```
parse error: Unexpected token: expected Newline, found Identifier { name: "tag", pattern: Immutable }
```

**Affected File:** `html_utils_spec.spl`

**Root Cause (Line 58):**
```simple
fn h1(txt: text) -> text: tag("h1", txt)
```

The parser doesn't support single-line function definitions with colon followed by expression on the same line.

**Fix Required:**
Convert to multi-line function body:
```simple
fn h1(txt: text) -> text:
    tag("h1", txt)
```

---

### Category 3: String Starting with `#` Confused as Comment (1 test)

**Error Message:**
```
parse error: Unexpected token: expected Newline, found FString([Literal("# ")])
```

**Affected File:** `markdown_utils_spec.spl`

**Root Cause (Lines 8-10):**
```simple
fn h1(txt: text) -> text: "# " + txt
fn h2(txt: text) -> text: "## " + txt
fn h3(txt: text) -> text: "### " + txt
```

Two issues combined:
1. Single-line function definition (same as Category 2)
2. String literal `"# "` at function body start may confuse parser with comment syntax

**Fix Required:**
```simple
fn h1(txt: text) -> text:
    "# " + txt

fn h2(txt: text) -> text:
    "## " + txt

fn h3(txt: text) -> text:
    "### " + txt
```

---

### Category 4: Inline If Without Else Clause (1 test)

**Error Message:**
```
parse error: Syntax error at 18:5: Inline if expression requires an else clause
```

**Affected File:** `math_utils_spec.spl`

**Root Cause (Line 17-20):**
```simple
fn clamp_i64(x: i64, min_val: i64, max_val: i64) -> i64:
    if x < min_val: min_val       # ERROR: inline if needs else
    else if x > max_val: max_val
    else: x
```

The first `if` is parsed as an inline if expression which requires an `else` clause.

**Fix Required:**
Use proper block syntax:
```simple
fn clamp_i64(x: i64, min_val: i64, max_val: i64) -> i64:
    if x < min_val:
        min_val
    else if x > max_val:
        max_val
    else:
        x
```

---

### Category 5: Missing Module Import (1 test)

**Error Message:**
```
compile failed: semantic: Undefined("undefined identifier: parse_int")
```

**Affected File:** `parse_utils_spec.spl`

**Root Cause (Line 3):**
```simple
use tooling.parse_utils.*
```

The module `tooling.parse_utils` does not exist or is not accessible.

**Fix Required:**
Either:
1. Create the `tooling/parse_utils.spl` module with the required functions
2. Define functions locally in the test file (like other `*_utils_spec.spl` files do)
3. Update import path to correct module location

**Note:** This test uses a different pattern than other utils specs - it imports from a module instead of defining implementations locally.

---

### Category 6: Expression Expected at Line Start (1 test)

**Error Message:**
```
parse error: Unexpected token: expected expression, found Newline
```

**Affected File:** `url_utils_spec.spl`

**Root Cause:**
Likely related to the `as` cast syntax or empty line handling. The file uses patterns like:
```simple
val code = c as i64
```

**Fix Required:**
Review the file for:
1. Empty lines in unexpected places
2. Cast expressions that may have syntax issues
3. Single-line function definitions (same pattern as above)

---

## Implementation Priority

### High Priority (Blocking 9 tests)
1. **Fix single-line return syntax** - Convert to multi-line blocks in all 9 affected files

### Medium Priority (Blocking 3 tests)
2. **Fix single-line function definitions** - Add newline after colon in html_utils, markdown_utils, url_utils

### Low Priority (Blocking 2 tests)
3. **Add else clause to inline if** - math_utils_spec.spl line 17-20
4. **Create or import parse_utils module** - parse_utils_spec.spl needs tooling.parse_utils

---

## Quick Fix Commands

To fix all files with single-line return pattern, the following patterns need conversion:

**Search pattern:**
```
if condition: return value
```

**Replace with:**
```
if condition:
    return value
```

Or better, refactor to use match expressions or early returns with proper block structure.

---

## Recommendations

1. **Parser Enhancement**: Consider allowing `return` in single-line `if` expressions as a language improvement
2. **Linter Rule**: Add lint for single-line function definitions to catch this pattern
3. **Test Template**: Update `.claude/templates/sspec_template.spl` to avoid these patterns
4. **Documentation**: Add syntax guidelines in `/coding` skill about proper if/return usage

---

## Detailed Examples with Fixes

### Example 1: Single-line Function Definition

**Location:** `html_utils_spec.spl:58-67`

**Broken Code:**
```simple
fn h1(txt: text) -> text: tag("h1", txt)
fn h2(txt: text) -> text: tag("h2", txt)
fn p(txt: text) -> text: tag("p", txt)
fn div(content: text) -> text: tag("div", content)
fn span(txt: text) -> text: tag("span", txt)
fn strong(txt: text) -> text: tag("strong", txt)
fn br() -> text: "<br />"
fn hr() -> text: "<hr />"
```

**Error:** `expected Newline, found Identifier { name: "tag" }`

**Problem:** Parser expects newline after `:` in function definition, but finds expression on same line.

**Fixed Code:**
```simple
fn h1(txt: text) -> text:
    tag("h1", txt)

fn h2(txt: text) -> text:
    tag("h2", txt)

fn p(txt: text) -> text:
    tag("p", txt)

fn div(content: text) -> text:
    tag("div", content)

fn span(txt: text) -> text:
    tag("span", txt)

fn strong(txt: text) -> text:
    tag("strong", txt)

fn br() -> text:
    "<br />"

fn hr() -> text:
    "<hr />"
```

---

### Example 2: Inline If Without Else

**Location:** `math_utils_spec.spl:17-20`

**Broken Code:**
```simple
fn clamp_i64(x: i64, min_val: i64, max_val: i64) -> i64:
    if x < min_val: min_val
    else if x > max_val: max_val
    else: x
```

**Error:** `Syntax error at 18:5: Inline if expression requires an else clause`

**Problem:** First `if x < min_val: min_val` is parsed as inline if expression. Inline if expressions MUST have else clause on same construct. The `else if` on next line is separate.

**Fixed Code (Option A - Block syntax):**
```simple
fn clamp_i64(x: i64, min_val: i64, max_val: i64) -> i64:
    if x < min_val:
        min_val
    else if x > max_val:
        max_val
    else:
        x
```

**Fixed Code (Option B - Proper inline syntax):**
```simple
fn clamp_i64(x: i64, min_val: i64, max_val: i64) -> i64:
    if x < min_val: min_val else: (if x > max_val: max_val else: x)
```

**Valid inline if examples:**
```simple
# Correct - inline if with else on same line
val result = if x > 0: "positive" else: "non-positive"

# Correct - nested inline if
val grade = if score >= 90: "A" else: (if score >= 80: "B" else: "C")

# WRONG - inline if without else
val bad = if x > 0: "positive"   # ERROR!
```

---

### Example 3: Missing Module Import

**Location:** `parse_utils_spec.spl:1-10`

**Broken Code:**
```simple
# Tests for parse utilities

use tooling.parse_utils.*

# =====================================
# Integer Parsing Tests
# =====================================

fn test_parse_int_positive():
    match parse_int("123"):      # ERROR: parse_int undefined
        Some(n) =>
            assert(n == 123)
```

**Error:** `compile failed: semantic: Undefined("undefined identifier: parse_int")`

**Problem:** Module `tooling.parse_utils` doesn't exist. Functions like `parse_int`, `parse_bool`, `parse_key_value` are not defined.

**Fixed Code (Option A - Define locally like other specs):**
```simple
# Tests for parse utilities
# NOTE: Implementations provided locally

# =====================================
# Parse Utility Implementations
# =====================================

fn parse_int(s: text) -> Option<i64>:
    if s.len() == 0:
        return nil
    var result: i64 = 0
    var is_negative = false
    val chars = s.chars()
    var start = 0

    if chars[0].to_string() == "-":
        is_negative = true
        start = 1

    for i in start..chars.len():
        val c = chars[i]
        if c >= '0' and c <= '9':
            result = result * 10 + (c as i64 - '0' as i64)
        else:
            return nil

    if is_negative:
        Some(-result)
    else:
        Some(result)

fn parse_bool(s: text) -> Option<bool>:
    val lower = s.to_lowercase()
    if lower == "true" or lower == "yes" or lower == "1":
        Some(true)
    else if lower == "false" or lower == "no" or lower == "0":
        Some(false)
    else:
        nil

# ... rest of implementations ...

# =====================================
# BDD Tests
# =====================================

describe "Parse Utilities":
    describe "Integer Parsing":
        it "parses positive integer":
            match parse_int("123"):
                case Some(n): expect n == 123
                case nil: expect false
```

**Fixed Code (Option B - Create module file):**

Create `simple/std_lib/src/tooling/parse_utils.spl`:
```simple
# Parse utilities module

pub fn parse_int(s: text) -> Option<i64>:
    # implementation...

pub fn parse_bool(s: text) -> Option<bool>:
    # implementation...

pub fn parse_key_value(s: text, sep: text) -> Option<(text, text)>:
    # implementation...
```

---

### Example 4: Expression Expected (Newline Issue)

**Location:** `url_utils_spec.spl:13-16`

**Broken Code:**
```simple
fn url_encode(s: text) -> text:
    var result = ""
    for c in s.chars():
        if is_unreserved_char(c):
            result = result + c.to_string()
        else:
            val code = c as i64
            result = result + "%" + to_hex_byte(code)
    result
```

**Error:** `expected expression, found Newline`

**Problem:** The `c as i64` cast syntax or the context around it causes parser confusion. The parser may have issues with:
1. Cast expression `c as i64`
2. Empty line handling
3. Block structure after `else:`

**Fixed Code:**
```simple
fn url_encode(s: text) -> text:
    var result = ""
    for c in s.chars():
        val ch = c.to_string()
        if is_unreserved_char(c):
            result = result + ch
        else:
            val code = char_code(ch)  # Use function instead of cast
            result = result + "%" + to_hex_byte(code)
    result

fn char_code(s: text) -> i64:
    if s.len() == 0:
        0
    else:
        s.chars()[0] as i64
```

**Alternative - Avoid `as` cast in complex expression:**
```simple
fn url_encode(s: text) -> text:
    var result = ""
    for c in s.chars():
        if is_unreserved_char(c):
            result = result + c.to_string()
        else:
            val char_val: i64 = c as i64   # Explicit type annotation
            result = result + "%" + to_hex_byte(char_val)
    result
```
