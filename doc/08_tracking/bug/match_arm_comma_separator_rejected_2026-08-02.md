# Comma between `match` arms is rejected — two shipped std modules were unloadable

- **Date:** 2026-08-02
- **Status:** FIXED (Rust seed parser + pure-Simple parser)
- **Severity:** high (whole modules silently invisible to every spec and census
  that imports them)
- **Parent:** `vacuous_spec_census_2026-07-30.md`, "Defects recorded, not
  absorbed" item 4 (which filed the gap and normalised one file as a stopgap)
- **Sites fixed:**
  - `src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`
    (`parse_match_stmt`, `parse_match_suspend`, new
    `consume_match_arm_separator_comma`)
  - `src/compiler_rust/parser/src/expressions/primary/control.rs`
    (`parse_match_expr`)
  - `src/compiler/10.frontend/core/parser_stmts.spl`
    (`parse_match_arms_common` — serves BOTH statement and expression position)
- **Regression tests:** `src/compiler_rust/parser/tests/control_flow.rs`
  (`parse_match_arm_separator_*`, `parse_match_multi_pattern_*`)

## Symptom

```
match ch:
    "A" => 65, "B" => 66, "C" => 67
    _ => 0
```

```
Unexpected token: expected pattern, found Comma
```

One arm per line works. The rejected form is the natural, compact spelling for
character/byte lookup tables, so the two std modules that contain such tables
were rejected **in their entirety** — a parse error kills the whole module, so
nothing that imports them can see anything they define.

## Root cause

`,` has two distinct roles around a match arm:

| position | role | consumed by |
|---|---|---|
| BEFORE the arm's `:` / `=>` / `->` | multi-pattern separator (`case 1, 2, 3:`) | the pattern parser |
| AFTER the arm's body | arm separator (`0 => 10, 1 => 20`) and trailing comma (`_ => 0,`) | **nobody** |

Only the first role was implemented. In the seed, the arms loop re-entered
`parse_match_arm` while sitting on the comma, so `parse_pattern` reported
"expected pattern, found Comma". In the pure-Simple parser the comma instead
fell into the `ends_enclosing_list` break added for
`Box(a: match x: 1: "one" _: "o", b: x)` — so the match was silently truncated
at its first arm and the *enclosing* parser then produced the same error.

The two roles never collide: by the time the arm body has been parsed, the
pattern list is already consumed, so a comma in that position is unambiguously
an arm separator. The fix consumes it there and nowhere else.

The pure-Simple fix is gated on `saw_indent` so the INLINE shape keeps its
meaning — an inline `match` used as a call argument or struct-literal field
value has no INDENT, and its trailing comma still terminates the enclosing list.

## Family enumerated (PROVED, `simple run`, Rust seed)

RED before / GREEN after, same binary source tree, only the parser changed:

| shape | before | after |
|---|---|---|
| `"A" => 65, "B" => 66` (arms on one line) | FAIL | PASS |
| `0 => 10,` / `1 => 20,` / `_ => 0,` (trailing comma per line) | FAIL | PASS |
| `0 => 10, 1 => 20` on several lines | FAIL | PASS |
| `0: y = 10, 1: y = 20` (colon arms, comma separated) | FAIL | PASS |
| `0: y = 10,` per line (colon arms, trailing comma) | FAIL | PASS |
| `val r = match n:` with comma arms (expression position) | FAIL | PASS |
| `case 1, 2, 3:` (multi-pattern comma) | PASS | PASS |
| `1, 2, 3 => 100` (caseless multi-pattern comma) | PASS | PASS |
| `case 1 \| 2 \| 3:` and `1 \| 2 \| 3 => 100` (pipe) | PASS | PASS |
| `case 0 => 10` one per line | PASS | PASS |

## Blast radius (PROVED)

`simple_parser::Parser::parse()` run over all **33,736** non-vendor `.spl` files
under `src/**` and `test/**` at base `e4b4561c803`, before and after:

| | files failing to parse |
|---|---|
| before | 235 |
| after | 234 |
| newly broken by the fix | **0** |

Files this gap explains — i.e. unloadable **solely** because of it:

1. `src/compiler_rust/lib/std/src/tooling/url_utils.spl` — the std URL module
   (`url_encode`, `url_decode`, `parse_url`, `build_url`, `parse_query_string`,
   …, 20 public functions). Its full 95-entry ASCII `char_code` table is written
   with comma-separated arms. **Never loadable; nobody had noticed.**
2. `src/compiler_rust/lib/std/src/tooling/base64_utils.spl` — already known;
   the parent lane normalised it one-arm-per-line as a stopgap. The natural
   comma-separated form is **restored** by this change.

Only 1 file appears in the census delta because base64_utils was already
normalised at the base sha; both are counted above.

`url_utils.spl` now parses and loads, and immediately surfaces a **semantic**
defect that was invisible while the module could not parse:
`method get not found on type str`. Recorded as a follow-up below, not absorbed.

## Restored natural form (PROVED)

`base64_utils.spl` `char_to_byte` / `byte_to_char` are back to comma-separated
arms and the stopgap NOTE is removed. Verified end-to-end with the fixed
binary: `encode_base64("ABC")` → `QUJD`, and
`parse_check` says `OK` for the restored file where the base parser says
`ERR … expected pattern, found Comma`.

## Adjacent gaps found while enumerating — recorded, NOT fixed here

1. **`=>` with an indented block body is rejected by the Rust seed** but
   accepted by the pure-Simple parser (`G28` branch in
   `parse_match_arms_common`). The seed emits the misleading hint
   *"Use ':' for function bodies, '=>' is for lambdas"* for
   `Some(code) =>` followed by an indented block. Both `url_utils.spl` and
   `base64_utils.spl` use this shape. A real seed/pure-Simple divergence.
2. **Inline caseless `match` in an argument list is unsupported by the seed** —
   `g(match x: 1: "one" _: "o", x)` fails with
   `function arguments: expected Comma, found Integer(1)`. The pure-Simple
   parser supports it, and `test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl`
   pins it — meaning **that spec file itself cannot be loaded by the seed.**
3. **`receive` arms** (`parse_receive_stmt`,
   `src/compiler/10.frontend/core/parser_stmts.spl:1445`) have their own arm
   loop and did not get the comma separator. Not exercised by any file in the
   tree at this sha.
4. `src/compiler_rust/lib/std/src/tooling/url_utils.spl` fails semantic
   analysis with `method get not found on type str` once it parses.

## Which parser needed the fix

**Both.** They are separate implementations and shared the defect (the seed is
not a clean control for it). The seed fix is verified by build + run + the new
`cargo test -p simple-parser` cases; the pure-Simple fix is source-level and
mirrors the seed's rule with the extra `saw_indent` gate described above.
