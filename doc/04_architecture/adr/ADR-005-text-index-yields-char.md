# ADR-005: `text[i]` yields a `char` code-point value

**Status:** accepted (2026-11-03, user decision). The language contract is in
force now. Enforcement is staged (see § Staging).
**Resolves:** `indexed_char_to_i64_silent_zero_family_2026-08-10` (was
`blocked-on-design`).
**History:** the first decision on 2026-11-03 was "Ruby-like: `text[i]` returns
1-character `text`". The user replaced it the same day with a `char` value type,
because a 1-character `text` allocates on every index under a no-GC runtime.

## Problem

`text[i]` had no well-defined element type. Below HIR, `char` is erased to
`text`, so the engines disagreed whenever an indexed character reached an
integer context:

| expression | JIT (`run`) | interpreter |
|---|---|---|
| `"a"[0].to_i64()` | 0 (`rt_string_to_int` parse failure) | 97 (single-char fallback) |
| `"72"[0].to_i64()` | 7 (digit parse) | 7 |
| `"72"[0] as i64` | parse / pointer-dependent | 55 (code point) |

A checksum loop written as `h = h * 31 + s[i].to_i64()` collided under the JIT,
and digit characters gave their digit value (7) rather than their code point
(55). Nothing in the type system flagged either mistake.

## Decision

1. **`s[i]` returns `char`**: a 4-byte Unicode scalar value (a code point, not a
   byte, not a grapheme cluster). It is a value type and never allocates.
   Printing a `char`, or interpolating it, shows the character.
2. **Char literals** are written `'x'`, including escapes (`'\n'`, `'\''`,
   `'\u{e9}'`). `c == '7'` is the comparison form. Single quotes mean ONLY
   char; raw text is `r"..."` (see "Char literal syntax"). A `char` is never a
   condition: `if c:` is a type error, write `c != '\0'`.
3. **No implicit conversion to text or int.**
   - `c == "7"` is a compile error. Use `c.to_text() == "7"`, or compare with
     `'7'`.
   - `c + 1` is a compile error. Arithmetic needs an explicit code point.
4. **Explicit conversions:**
   - `c.ord()` and `c as i64` give the code point (`'7'.ord() == 55`).
   - `char.from_code(n)` goes the other way. It returns `char` and fails on a
     non-scalar value (a surrogate, or a value above `0x10FFFF`).
   - `c.to_digit()` returns `Option<i64>` (`'7'.to_digit() == Some(7)`,
     `'a'.to_digit() == None`).
   - `c.to_text()` returns a 1-character `text`.
5. **Indexing is per code point.** `"72é"[2] == 'é'`. `s.len()` counts code
   points and `s.byte_len()` counts bytes.
6. **Byte and iteration APIs stay:** `s.byte_at(i)` (u8, O(1)), `s.chars()`
   (O(n) iteration yielding `char`), `s[a..b]` (returns `text`), and
   `s.char_code_at(i)` (i64 code point, kept for existing callers).
7. **Out of range** follows the existing text-index policy. `s[i]` with `i`
   outside `-len..len` is a runtime *index out of bounds* error. Negative
   indices count from the end in code points (`"abc"[-1] == 'c'`). The
   `char_at(i)` method keeps its own policy: over-run returns `""` (see
   `text_char_primitive_engine_contract_spec.spl`).

### Comparison

| | element of `s[i]` | unit | int conversion |
|---|---|---|---|
| Ruby | 1-char `String` (allocates) | code point | `.ord` explicit; `"7".to_i == 7` |
| Rust | no `s[i]`; `s.chars().nth(i)` -> `char`; `s.as_bytes()[i]` -> `u8` | scalar / byte | `c as u32`, `c.to_digit(10)` |
| Python | 1-char `str` (allocates) | code point | `ord(c)` |
| **Simple** | `char` value (no allocation) | code point | `.ord()` / `as i64`; `.to_digit()` -> Option |

Simple takes Ruby's and Python's ergonomics (`s[i]` works, per code point) and
Rust's element type (a distinct scalar `char` with explicit conversions). The
type-level distinction is what removes the silent-zero family: `s[i].to_i64()`
no longer type-checks as "parse this text", because `char` has no `to_i64`.

## Performance (no-GC runtime)

- `char` is an unboxed 32-bit value, so `s[i]` allocates nothing.
- Text carries an **is-ASCII header flag**, so `s[i]` is O(1) on ASCII text and
  O(i) otherwise (UTF-8 has to be scanned to find the i-th code point).
  `for i in 0..s.len(): s[i]` is therefore O(n^2) on non-ASCII text.
- **Lint (perf warning):** `s[i]` inside `for i in 0..s.len()` or the
  equivalent `while i < s.len()` loop. Fix it with `for c in s.chars()`, or with
  `s.byte_at(i)` when the code works on bytes.
- **Lexers and tokenizers** (compiler and stdlib) must use `byte_at` or
  `char_code_at`, never `text[i]`.
- A budget spec pins the indexing cost:
  `test/05_perf/text_index_char_budget_spec.spl`.

## Staging

Same staging as exhaustive match: a warning now, an error after phase 3.

| item | now | after phase 3 passes once |
|---|---|---|
| `s[i]` used where an i64/int is expected | **warning** | error (TODO + bug row `text_index_char_int_context_warning_to_error_2026-11-03`) |
| `c == "x"`, `c + 1` on a char | warning while `char` is still erased in a lane; error once the lane types `char` | error |
| seed interpreter / JIT / runtime returning `char` | lands now (Rust PR) | — |
| pure-Simple compiler codegen meaning switch | **held** behind the phase-3 gate (TODO + bug row) | lands |
| compiler-source call sites converted to `byte_at` / `char_code_at` / `.ord()` | land now (semantics-neutral today) | — |

The frozen stage2 compiles the compiler's own lexer and parser, so the
pure-Simple codegen switch cannot land while phase 3 is in flight. Any
compiler-source site that would change meaning must already use an explicit
byte or code-point accessor before the switch lands.
`@workaround(text_index_char)` markers are allowed only where a
stage2-compiled path still needs the old behaviour until a rebuild.

## Consequences

- The silent-zero and digit-value divergence becomes a type error (staged).
- `scripts/check/check-string-index-char-to-i64.shs` remains as the
  lexical guard until the type-checker error is enforced.
- Existing `s.char_code_at(i)` code is unaffected.

## Representation and ABI (from the 2026-11-03 Fable design review)

- **Interpreter:** a new `Value::Char(char)` variant. Today there is none
  (`interpreter_method/string.rs:424`); 1-char `Value::Str` is what `s[i]`
  returns now.
- **MIR/native:** `TypeId::CHAR` is already an unboxed i32 scalar in MIR
  (`mir/lower/lowering_expr_ops.rs:650-687`). At a `RuntimeValue` boundary
  (collections, `Any`-free generic slots, `rt_index_get`) a char is boxed as a
  **`TAG_SPECIAL` sub-kind** beside nil/bool/symbol, never as `TAG_INT`. With
  `TAG_INT`, `'7' == 55` would be true and `'7'` would print `55`.
- **Indexing entry point:** a dedicated `rt_string_index_char(s, i) -> char`
  replaces the `rt_index_get -> rt_string_char_at` route for text receivers.
  `rt_string_char_at` keeps returning text (with `""` on over-run) for the
  `char_at` method.
- **JIT out of range:** `rt_string_index_char` raises the same runtime
  index-out-of-bounds abort that array indexing uses. It does not return `""`
  or nil, because neither is a `char`.
- **Lexer (amended 2026-11-03, see "Char literal syntax" below):** after the
  switch, `'...'` is a char literal only: exactly one Unicode scalar or one
  escape. Any other content between single quotes is a lex error that points
  to `r"..."`. `'ident` with no closing quote stays a label.
- **ASCII flag:** `RT_STRING_FLAG_ASCII` is set lazily today, on the first
  `char_code_at`, so the first `s[i]` on a fresh non-literal text costs O(n).
  The deliverable is to set it eagerly at construction (literals, concat,
  slice, from_bytes). Until then the O(1) claim holds only after the first
  access.
- **`char.from_code(n)` failure:** a runtime abort on a non-scalar value in
  every engine (`rt_char_from_code` returns text today and must change).

### Additional staging rows

| item | now | after phase 3 |
|---|---|---|
| `s.len()` = code points (today it counts bytes in the interpreter, `rt_string_len`) | **held**: `len()` stays bytes; `char_count()` and `byte_len()` are explicit | switch `len()` to code points (bug row `text_len_codepoint_switch_2026-11-03`) |
| interpreter `to_i64` 1-char code-point fallback (`string.rs:441`) and `"x" as i64` (`casting.rs:143`) | warning when the receiver is an indexed char | removed: `char` has `.ord()` and no `to_i64` |
| seed interpreter and seed JIT switch | land **together** in one PR, so the seed never disagrees with itself | — |
| interpreter vs pure-Simple native divergence while codegen is held | accepted and recorded. Call sites are converted first, so no compiler-source site observes it | closed |
| a single-scalar `'x'` literal (today a 1-char raw string) | lexes as `char` once the lexer change lands. Existing `'x'` sites compared with text are converted to `"x"` in the call-site PR, before the lexer switch | — |
| `if c:` / `while c:` with a `char` condition | type error (a char is not a bool; write `c != '\0'`) | type error |
| staged warnings (non-exhaustive match, `Any`/erased access outside `unsafe:`, `case None` on a scalar, `char` used as `i64`, char-vs-text comparison, new `'...'` raw strings) | warning | **error once Windows, macOS and Linux all have a working self-hosted Simple binary** (the promotion trigger; "phase 3" above is the first gate, this is the last) |

## Char literal syntax (decision 2026-11-03)

A char literal is the plain single-quoted form `'x'` (Rust/C style). Single
quotes mean **only** char. Text forms:

| form | meaning |
|---|---|
| `"..."` | text, interpolates `{expr}`, escapes processed |
| `r"..."`, `r"""..."""` | raw text: no interpolation, no escapes |
| `"""..."""` | multi-line text, braces literal |
| `'x'` | `char`: one Unicode scalar (U+0000..U+10FFFF minus surrogates, 1-4 UTF-8 bytes) or one escape (`'\n'`, `'\''`, `'\u{1F600}'`) |

Why plain `'x'` and not a prefixed `c'x'`:

- Familiar to Rust and C readers; no new prefix to learn or lex.
- Single quotes are freed once the legacy raw-string meaning moves out.
- `r"..."` already exists, so raw text needs no new syntax.

Scalar rules: `'é'`, `'한'`, `'😀'` are one char each. A user-perceived
character can be several scalars (decomposed `e` + U+0301, a ZWJ emoji
sequence): that is **not** a valid char literal and stays text
(`"é"`). Grapheme handling is a separate API. `s[i]` indexes by code point,
`.len()` counts code points (staged, see above), `.byte_len()` / `byte_at` are
byte-level.

A `char` is not a condition: `if c:` is a type error; compare explicitly
(`c != '\0'`).

### Migration plan

1. A rewrite tool converts the ~7.8k legacy `'...'` raw-string sites to
   `r"..."`, in per-directory batches. Each batch is verified token-neutral:
   the lexer token stream (kind and value) before and after is identical, so a
   batch cannot change behavior.
2. `scripts/check/check-no-single-quoted-raw-string.shs` ratchets new sites out
   of `src/**/*.spl` (advisory now, blocking after the lexer switch).
3. **The lexer switch lands only after the stage3 self-build passes.** The
   frozen stage2 compiles the compiler's own lexer; changing what `'...'` means
   before every compiler-source site is converted would break the bootstrap.
4. After the switch, a multi-scalar `'...'` is a lex error. The staged warnings
   become errors once Windows, macOS and Linux all have a self-hosted binary.

Tracking: bug row `char_literal_lexer_switch_staged_2026-11-03` (blocked on the
stage3 self-build).

## Char truthiness and construction (2026-11-03 decision)

- **Truthiness:** a `char` has no truthiness. `if c:`, `while c:`, `not c`,
  `c and x` are type errors in every engine; write an explicit comparison.
  Checker diagnostic is staged: a warning now, an error once Windows, macOS and
  Linux each have a self-hosted binary (same staging as exhaustive match; bug row
  `char_condition_type_check_staged_2026-11-03`).
- **Runtime:** until the checker enforces it, `truthy()` on a char tag fails
  closed (Rust `panic!`, C `spl_panic`) with the same message in both runtimes
  instead of silently returning false (previous behaviour, even for `'a'`).
- **Construction:** only Unicode scalar values form a char. Rust
  `from_char_code` returns `None` for surrogates (U+D800..U+DFFF) and values
  above U+10FFFF; C `RT_CHAR_FROM_CODE` returns `RT_NIL` for the same inputs.
  `RT_CHAR` is the unchecked constructor for known-valid scalars only.
