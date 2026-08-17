# BUG: text_advanced case conversions corrupted by `ch[0] ± 32` char arithmetic

- **Status:** OPEN (RED on `origin/main`)
- **Found:** 2026-08-11, during skeptical review of the escape_json dedup commits
- **Severity:** HIGH — `to_snake_case` / `to_title_case` / `to_camel_case` in
  `src/lib/common/text_advanced.spl` return corrupted text for every input that
  needs a case flip.
- **Introduced by:** `a9d3e0f0b1a` ("dedupe escape_json"), re-landed by
  `f45936abc35` whose message states "no other change".

## What happened

`a9d3e0f0b1a` was described (and reviewed) as an `escape_json` delegation. Its
diff also silently rewrote the character-case arithmetic in three unrelated
functions:

```
-            val upper_code = char_code(ch) - 32
-            sb.push(char_from_code(upper_code))
+            val upper_code = ch[0] - 32
+            sb.push("{upper_code}")
```

`char_from_code(char_code(ch) - 32)` is correct. `ch[0]` does **not** yield an
integer code point — it yields a one-character `text`. So:

- `"H"[0] + 32` performs **string concatenation** → `"H32"`.
- `"h"[0] - 32` produces garbage (measured: `"g"`).
- `"{code}"` then interpolates that text, not a character.

Affected: `to_title_case` (line ~182), `to_snake_case` (~216),
`to_camel_case` (~243). `char_from_code` was also dropped from the
`std.string_core` import list.

## Reproduction (seed interpreter, 2026-08-11, origin/main @ 8f91e5229ec)

```simple
use std.text_advanced.{to_snake_case}
fn main():
    print("snake=[{to_snake_case("HelloWorld")}]")
```

```
snake=[H32ello_W32orld]      # expected: hello_world
```

`to_title_case` does not even survive semantic analysis on the same run:
`error: semantic: type mismatch: cannot convert string to int`.

Minimal primitive probe:

```simple
fn main():
    val a = "h"
    val b = "H"
    print("idx=[{a[0]}] up=[{a[0] - 32}] low=[{b[0] + 32}]")
# idx=[h] up=[g] low=[H32]
```

## Fix

Restore the original form in all three functions and re-add `char_from_code` to
the `use std.string_core.{...}` list:

```simple
val upper_code = char_code(ch) - 32
sb.push(char_from_code(upper_code))
```

The `escape_json` delegation itself (the actual subject of `a9d3e0f0b1a` /
`f45936abc35`) is correct and should be kept.

## Regression test to add with the fix

`test/01_unit/lib/common/text_advanced_case_spec.spl` asserting
`to_snake_case("HelloWorld") == "hello_world"`,
`to_title_case("hello world") == "Hello World"`,
`to_camel_case("hello world") == "helloWorld"`. No spec covers these functions
today, which is why a silent rewrite of their core arithmetic landed unnoticed.

## Process finding

A commit whose message says "no other change" carried an unrelated,
behavior-breaking rewrite of three functions. Diffs must be read in full even
when the stated scope is a one-line delegation.

## RESOLVED (verified 2026-08-17)

`src/lib/common/text_advanced.spl` again uses `char_from_code(char_code(ch) ± 32)`
at lines 182/189, 216/217, 243/244, and `char_from_code` is back in the
`std.string_core` import (line 23). Runtime probe on the seed interpreter:
`to_snake_case("HelloWorld")` -> `hello_world`, `to_title_case("hello world")`
-> `Hello World`, `to_camel_case("hello_world")` -> `helloWorld`. Doc was stale.

Spec coverage (2026-08-17): repro spec
`test/01_unit/lib/common/text_advanced_case_conversion_spec.spl` (snake/title/
camel oracles that fail under the `ch[0] ± 32` rewrite) and generalization spec
`test/01_unit/lib/common/text_advanced_case_class_generalization_spec.spl`
(kebab/pascal/screaming-snake + round-trip, same defect class; mirrored in
`test/unit/lib/common/`). Both run green: 5 examples, 0 failures.
