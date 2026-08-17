# Comma between `match` arms is rejected — two shipped std modules were unloadable

- **Date:** 2026-08-02
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

## Adjacent gaps — RESOLVED in the follow-up lane (see next section)

The four gaps listed immediately below were recorded here when the comma fix
landed. All four were re-derived from runtime evidence in the follow-up lane
and are now resolved; two of them were **described wrongly** on first
recording. Read the "Follow-up resolution" section for the corrected findings.

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

---

# Follow-up resolution (2026-08-02)

All four adjacent gaps above are resolved. Two were misdescribed on first
recording; the corrected finding is given for each. Every claim below is
labelled PROVED (runtime-measured) or INFERRED.

## Gap 1 — "`=>` with an indented block body is rejected by the Rust seed"

**The original description was WRONG.** The seed's *parser* accepts `=>` with
an indented block body in both statement and expression position — PROVED by
four new `cargo test -p simple-parser` cases
(`parse_match_arm_fat_arrow_indented_block_body_*`), which passed **before any
change in this lane**, and by the census: `url_utils.spl` and
`base64_utils.spl` both parse `OK`.

What actually happens is a **false-positive diagnostic**, not a rejection.
`detect_common_mistake` (`parser/src/error_recovery.rs:463`) flags the
TypeScript arrow-function mistake on the purely lexical shape `) =>`:

```rust
if matches!(current.kind, TokenKind::FatArrow) && matches!(previous.kind, TokenKind::RParen)
```

A match arm whose pattern is call-shaped or tuple-shaped ends in `)` too, so
every `Some(code) =>`, `Ok(v) =>` and `(a, b) =>` arm was reported as a
TypeScript mistake. std `url_utils.spl` alone emitted **160 lines** of these
hints for a file that parses perfectly — PROVED by running the seed driver on a
probe importing it.

The hints are `ErrorHintLevel::Hint` and do **not** fail the run, so this was
diagnostic noise, not a gate. It still had to be fixed: it is a loud false
report on core grammar, and it buried the one real error in the same output.

**Fix.** The detector sees only a three-token window and cannot tell the two
apart, so the arm context is supplied by the parser instead. A new
`Parser::match_arm_depth` counter is incremented around **all four** arm loops
(statement block, statement inline, expression block, expression inline), and
`is_spurious_match_arm_fat_arrow` in `parser_helpers.rs` drops **only**
`TsArrowFunction` **only** while that counter is non-zero. The detection rule
itself is untouched — guarded by `ts_arrow_detection_rule_itself_is_untouched`
and the pre-existing `test_typescript_arrow_function_detection`.

Result: probe output 162 lines → **12 lines, 0 TsArrow hints, exit 0** (PROVED).

## Gap 2 — inline `match` in an argument list: the REAL seed divergence

Confirmed and fixed. This was the genuine two-parser divergence.

* pure-Simple parser: **accepts** (fix `8fdc21c67b5`, `ends_enclosing_list` in
  `parse_match_arms_common`).
* Rust seed: **rejected** — PROVED, `parse_tree_census --why` on
  `test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl` gave
  `expected comma before argument 'b'` at line 58. That spec file was therefore
  invisible to every seed-run gate.

The spec's own docstring claims *"The Rust seed parses both"* — **that claim was
false** (PROVED).

**The failure pre-dates the comma fix** (PROVED, not inferred): with
`consume_match_arm_separator_comma` reverted to a no-op and everything else at
this sha, the spec still fails, with the older error `expected pattern, found
Comma` at line 57. The comma fix changed the failure mode, it did not cause the
failure — consistent with the comma lane's "0 newly broken".

**Fix** (`stmt_parsing/control_flow.rs`, mirrored into the expression loop):

* `consume_match_arm_separator_comma` now returns `bool` and consumes the
  arm-boundary comma **only at `lexer.bracket_depth == 0`**. Inside a call's
  argument list, a struct-literal field list or a collection literal the comma
  belongs to the enclosing list and is left unconsumed.
* `at_enclosing_list_terminator` breaks the arm loop on `)`/`]`/`}`. It is
  deliberately **not** gated on `bracket_depth`: the lexer decrements the depth
  as it produces the closer itself, so by the time the closer is the current
  token the depth has already dropped back. No gate is needed anyway — a match
  arm can never *begin* with a closer.

## Gap 3 — `receive` arms (the arm-parsing family sweep)

Fixed in `parse_receive_stmt`
(`src/compiler/10.frontend/core/parser_stmts.spl`). It duplicates the arm loop
rather than sharing `parse_match_arms_common`, so it never got the separator
fix. Unlike `match`, `receive` is always a statement with a real INDENT and can
never be an element of an enclosing list, so it needs no bracket-depth gate — a
`saw_arm` flag distinguishes an arm-boundary comma from a stray leading one.

### Every place that parses arms — full enumeration

**Rust seed**

| Site | Own arm loop? | Status |
|---|---|---|
| `parse_match_stmt` block branch, `control_flow.rs` | yes | comma fix + depth gate + terminator break |
| `parse_match_stmt` inline branch (`;` separated) | yes | `;` by design; comma belongs to the enclosing list. `match_arm_depth` wrapped |
| `parse_match_suspend`, `control_flow.rs` | yes | same as block branch |
| `parse_match_expr` block branch, `primary/control.rs` | yes | same, plus `lexer.pop_indent()` resync |
| `parse_match_expr` inline branch | yes | as inline branch above |
| `parse_match_arm` / `parse_match_arm_expr` | no — parse ONE arm | separator handled by callers |
| `parse_asm_match`, `asm.rs` | **no** — delegates to `parse_block()` → `parse_match_stmt` | inherits every fix automatically |
| `parse_when_block`, `control_flow.rs` | n/a | compile-time `when`/`else` over *items*; no patterns, no arms — **not** a family member |

**pure-Simple**

| Site | Own arm loop? | Status |
|---|---|---|
| `parse_match_arms_common`, `parser_stmts.spl` | yes | fixed in `75c6fff3b1a`; serves both `parse_match_stmt_tail` and `parse_match_expr_tail` |
| `parse_receive_stmt`, `parser_stmts.spl` | yes | **fixed here** |
| `parse_asm_match`, `parser_asm.spl` | yes | `case`-only loop, no separator support — see open item below |
| `parse_asm_match`, `_ParserPrimary/asm_match_suffix.spl` | yes | **duplicate** of the above, same gap |

`parser_stmts.spl:782/1008/1015/1582/1586` construct arms while desugaring
`if` / `if-let`; they do not parse an arm LIST and are not family members.

### Open, recorded not fixed: `asm match` comma divergence

The Rust seed's `asm match` routes through `parse_block()` → `parse_match_stmt`
and therefore now **accepts** comma-separated arms; the two pure-Simple
`parse_asm_match` copies do not. No file in the tree uses that form at this sha,
so this is recorded rather than speculatively implemented. The **duplication**
of `parse_asm_match` across `parser_asm.spl` and
`_ParserPrimary/asm_match_suffix.spl` is itself a defect — a fix to one will not
reach the other.

## Gap 4 — `url_utils.spl`: a module that had never been loaded

20 public functions, unreachable behind the parse error until `75c6fff3b1a`, so
never once executed. Every function was treated as unverified and exercised
against the seed. **Four real defects**, all PROVED at runtime:

1. **`method get not found on type str`** (the reported one), `is_unreserved`:
   `ch.get(0).unwrap()`. `get` is not a text method; the rest of the file
   already uses `char_at`, which is the real accessor. → `ch.char_at(0)`.
2. **`url_decode` silently DROPPED a trailing `%`** — `url_decode("100%")`
   returned `"100"`. The `if i + 2 < input.len()` guard had no `else`, so a
   truncated escape appended nothing. A malformed escape must survive as
   literal text, exactly as the existing non-hex `None` arm already does.
   → now `100%`, and `abc%A` → `abc%A`.
3. **Every non-ASCII character was silently encoded as a SPACE.** `char_code`
   ended `_ => 32`, so `char_code("é")` returned 32 and `url_encode("é")`
   produced `"%20"` — a wrong answer with no error. → falls back to
   `ch.char_code_at(0)`; now 233 / `%E9`. A `TODO` records that full
   correctness needs per-UTF-8-**byte** encoding (`%C3%A9`), which needs a byte
   accessor on text.
4. **`use super.string_utils.{split, trim, starts_with, ends_with}` imported
   four names that do not exist.** `string_utils.spl` defines `trim_start` /
   `trim_end` / `split_take` / `split_once` / `starts_with_any` /
   `ends_with_any` — none of the four. `trim`, `starts_with` and `ends_with`
   were dead (the code uses the text methods), but `split` was live, so
   `parse_query_string` died with `function 'split' not found` the moment the
   module became loadable. `split` is a text method → `query.split("&")`, and
   the bogus import is gone.

Verified correct after the fixes (PROVED, seed driver, exit 0): `url_encode` /
`url_decode` incl. `+`, `%`-roundtrip and malformed escapes; `parse_url` on a
full `scheme://user:pass@host:port/path?query#frag` and on a bare
`https://x.com`; `build_url`, `get_base_url`, `get_full_path`,
`parse_query_string`, `build_query_string`, `parse_int`, `hex_digit`, `to_hex`,
`is_valid_url`, `is_absolute_url`, `join_url`, `add_query_param`.

**Sibling check.** `base64_utils.spl`'s previously reported A-J/a-e/0-2 table
gap is NOT present at this sha — its tables are complete (INFERRED from reading
the restored comma-separated form; its `encode_base64("ABC") → QUJD` evidence is
in the section above).

## Which parser is authoritative

**The pure-Simple parser is authoritative; the seed was brought up to it.**

* It is the shipped tooling. Per `CLAUDE.md`, `test`/`lint`/`fmt`/`build`/`run`
  /MCP/LSP all run on the self-hosted binary; **the seed is bootstrap-only.**
  The language is what the self-hosted compiler accepts.
* The disputed form is short, safe and already used in production
  (`src/os/hosted/hosted_web_content_session.spl:983`), and a spec exists to
  pin it. The repo rule is to fix the parser, never to normalise the source.
* A form the shipped compiler accepts but the seed rejects makes the pinning
  spec **invisible on the seed path** — which is exactly how this survived.

The seed still must accept everything the self-hosted compiler's own source,
std and specs use, because it compiles them during bootstrap. So the seed's
grammar has to be a superset here, not a second opinion.

## Evidence

* **Blast radius.** `simple_parser::Parser::parse()` over all non-vendor `.spl`
  files in `src/**` + `test/**`: **33,684 files, 234 failing before → 233
  after, 0 newly broken**, the single delta being
  `parser_inline_match_in_argument_list_spec.spl`. Failure **name sets** were
  diffed, not just counts. Harness:
  `src/compiler_rust/parser/examples/parse_tree_census.rs` (not committed).
  It must skip symlinks — following them inflates the census to 95,846.
* **Non-vacuity.** With the three implementation pieces sabotaged (depth gate
  removed, terminator break disabled, hint suppression disabled) and **all tests
  kept**, exactly **6** of the new tests fail — the 4 inline-match-terminator
  cases and the 2 hint-suppression cases — while all **9** pre-existing
  comma-separator and multi-pattern guards still pass.
* `cargo test -p simple-parser`: all green (43/43 in `control_flow`).
* The `=>` block-body tests passed **before** any change here, which is what
  disproved the original Gap 1 description.

## Verification constraints

* `bin/simple` at this sha is the **Rust seed** (enum-probe = 0). The
  pure-Simple `parse_receive_stmt` fix is therefore **source-level and INFERRED**
  — there is no self-hosted binary to run it against. The Rust-side fixes are
  PROVED by build + run + tests.
* The frozen std snapshot `/home/ormastes/dev/.simple-build-36f5e286` **does not
  exist** at this sha, so it did not constrain verification; the probe loaded
  `url_utils.spl` from the worktree, as the error paths in the transcript show.
