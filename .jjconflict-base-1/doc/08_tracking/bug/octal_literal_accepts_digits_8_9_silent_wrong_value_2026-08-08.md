# Octal literals accept the digits 8 and 9 — silent wrong value, and a seed↔self-host divergence

- **Status:** FIXED
- **Found:** 2026-08-08, during adversarial review of `b0f5308993`
  ("fix(frontend): lex binary/octal type suffixes and uncap radix digit runs")
- **Component:** `src/compiler/10.frontend/core/lexer_struct.spl` (`CoreLexer.scan_number`,
  octal branch) + `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`
  (`parse_int_literal_text`, octal branch, :193)
- **Severity:** HIGH — silently wrong constant value, no diagnostic, in the
  pure-Simple frontend. Bootstrap-visible.

## Summary

The pure-Simple lexer's octal branch validates digits with `is_digit(oc)`, which
accepts `0`-`9`, not `0`-`7`. `parse_int_literal_text` then accumulates
`oct_val * 8 + int(oc)` over whatever the lexer handed it. So an octal literal
containing an `8` or a `9` lexes as a single valid INT token and evaluates to a
wrong number with **no error anywhere in the pipeline**.

The Rust bootstrap seed does *not* share this hole: its octal digit predicate is
`|c| ('0'..='7').contains(&c)` (`src/compiler_rust/parser/src/lexer/numbers.rs`,
`scan_number`), so it stops the digit run at the first out-of-range digit.

This was left explicitly unfixed by `b0f5308993`, which noted "the octal branch
uses `is_digit`, so `0o789` lexes as valid" but did not assess the consequence.
The consequence is a silent wrong value, not a downstream rejection.

## Mechanism

`lexer_struct.spl`, octal branch:

```
val oc: text = self.source_chars[pos]
val is_oct: bool = is_digit(oc)      # <-- accepts 8 and 9
val is_under: bool = oc == "_"
val valid: bool = is_oct or is_under
```

`primary_expr.spl:193`, octal branch of `parse_int_literal_text`:

```
if oc != "_":
    oct_val = oct_val * 8 + int(oc)   # <-- int("8") = 8, int("9") = 9
```

Worked example, `0o789`:

| step | digit | accumulator |
|------|-------|-------------|
| 1 | `7` | `0*8 + 7 = 7` |
| 2 | `8` | `7*8 + 8 = 64` |
| 3 | `9` | `64*8 + 9 = 521` |

`0o789` evaluates to **521**, silently. There is no range check in the lexer, no
range check in `parse_int_literal_text`, and no diagnostic emitted.

Note the value is not even a consistent misinterpretation — it is a base-8
positional accumulation over base-10 digits, so it has no meaning in any radix.

## Concrete failure scenario

The in-tree `0o` literals are **file-permission constants**:

- `src/os/apps/coreutils/cp.spl:15` — `0o644u32`
- `src/os/apps/coreutils/mkdir.spl:13` — `0o755u32`

A typo of `0o755` as `0o855`, or `0o644` as `0o844`, produces:

- `0o855` -> `8*64 + 5*8 + 5 = 557` (correct `0o855` is meaningless; the intended
  `0o755` is 493) — wrong permission bits on a created file, no build error.
- `0o800` -> `8*64 = 512` — which is exactly `0o1000`, a plausible-looking but
  wrong mode.

Under the **Rust seed** the same source is rejected instead: the digit run stops
at the last valid octal digit and the remainder lexes as a separate decimal INT
token, so `0o855` becomes `INT("0o8")`... in fact `0o` with no valid digit at all,
followed by `855`. Either way the seed does not silently produce a number.

**This is therefore also a bootstrap-surfacing divergence**: a file that compiles
to one value under the self-hosted compiler compiles to a different value — or
fails — under the seed. Stage-to-stage comparison would diverge on any such
literal.

## Verification performed

- Read both implementations directly (pure-Simple lexer + `parse_int_literal_text`,
  and the seed's `numbers.rs`). The arithmetic above is directly readable from
  the source; no harness run is needed to establish the accumulator result.
- Swept the tree for existing exposure:
  `/usr/bin/grep -rEn '0o[0-7_]*[89][0-9_]*' --include=*.spl src/ test/ examples/`
  -> **0 hits**. No current source triggers the defect. It is latent, not active.
- The seed's behaviour was confirmed by reading `scan_radix_digits`' octal
  validator, which is `('0'..='7')`.

## NOT yet verified (stated rather than assumed)

What the pure-Simple **parser** does with the two adjacent INT tokens that a
0-7-restricted lexer would produce (`INT("0o7")` followed by `INT("89")`) has not
been tested. This matters for choosing the fix — see below.

## Proposed fix, and why it was not landed here

The one-line change is to restrict the octal digit predicate to `0`-`7`, matching
the seed. It is safe by exposure (0 in-tree hits) but it was **not** landed,
for two reasons:

1. Restricting the digit set converts a silent-wrong-value into a **token split**
   — which is exactly the defect class `b0f5308993` had just finished
   eliminating for suffixes. Unless the parser emits a clean diagnostic on two
   adjacent INT literals, that trades one silent failure for another. That
   parser behaviour is untested (above), so the fix is not yet known to be an
   improvement.
2. `lexer_struct.spl` is the highest-blast-radius file in the frontend. A change
   there needs a full RED -> GREEN -> SABOTAGE cycle. During this review a single
   spec-harness run against this file exceeded 25 minutes and ~1700 lines of
   module-load output without emitting a `SPEC FILE VERDICT` line, so that cycle
   could not be completed honestly.

The correct fix is probably **not** the digit-set restriction alone but a real
lex diagnostic ("invalid digit '8' in octal literal"), which also fixes the
seed's split-token behaviour. That is a larger change and needs its own design.

## Related, same family, also open

`0b123` splits into `INT("0b1")` + `INT("23")` in **both** the pure-Simple lexer
and the seed (the binary digit predicate is correctly `0`/`1`, but an invalid
digit terminates the run rather than erroring). Same missing-diagnostic root
cause, different symptom. It should be fixed by the same lex-diagnostic work.

## Fix landed

Both `scan_number` radix branches in `lexer_struct.spl` now consume the
**whole** decimal-digit run (not just the in-range digits), tracking the
first out-of-radix digit seen. If one was seen, the branch emits a single
`TOK_ERROR` (191) token — `"invalid digit <d> in octal literal <text>"` /
`"invalid digit <d> in binary literal <text>"` — instead of building an INT
token (octal) or silently stopping the run and letting the remainder become
a second adjacent token (binary). This reuses the exact channel the lexer
already uses for "unterminated string": `parse_primary_expr`'s existing
fallback (`_ParserPrimary/primary_expr.spl:958`) turns any unhandled
`TOK_ERROR` into a real `parser_error`, so no new plumbing was needed on the
parser side.

This also fixes the sibling noted above: `0b123` now gets one lex error
instead of silently splitting into `INT("0b1")` + `INT("23")`.

Hex was audited and left untouched: `is_hex_digit` (0-9a-fA-F) is exactly the
valid hex digit set, so there is no analogous hole — a non-hex character
correctly terminates the run today (that's the suffix boundary).

Valid literals, including the suffix forms fixed by `b0f5308993`
(`0o644u32`, `0o755u32`, `0b1010u64`, `0x1F`, underscore separators), are
unaffected — re-verified below.

### Verification

New spec:
`test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl`
(11 examples). Because `bin/simple test` interprets the compiler's `.spl`
sources live, this could be run directly without a bootstrap rebuild:

- **RED** (origin/main's unfixed `lexer_struct.spl` swapped in): `11 total, 7
  passed, 4 failed` — the 4 new invalid-digit assertions failed, the 7
  valid-literal controls passed.
- **GREEN** (fix restored): `11 total, 11 passed, 0 failed`.
- Sibling regression control, unchanged by this fix:
  `test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl` — `9
  total, 9 passed, 0 failed` both before and after.

The seed (`src/compiler_rust/target/release/simple`, confirmed via its
"bootstrap seed only" banner) was used as a reference oracle. Its actual
behavior turned out to be inconsistent rather than a clean single
diagnostic: `val x = 0o789` alone parses with exit 0 and no diagnostic
(the seed's octal digit scan stops at `7`, and the decl-statement parser
silently drops the trailing `89`), while `print(0o789)` does error —
`expected Comma, found Integer(89)`, a token-split artifact of the same
stop-at-first-invalid-digit design this fix deliberately avoids. The
self-hosted fix is therefore stricter and more consistent than the seed:
every malformed radix literal now gets one lex-level diagnostic regardless
of surrounding syntax, rather than sometimes silently truncating.

`src/os/apps/coreutils/cp.spl:15` (`0o644u32`) and `mkdir.spl:13`
(`0o755u32`) were not rebuilt directly (load was high); they are covered by
construction since the new spec's `"0o644u32"` / suffix-form rows exercise
the identical lexer code path with identical literal text.

Landed: `src/compiler/10.frontend/core/lexer_struct.spl` (blob
`63a71e0202f498cfdcd8e2812b90b92d621f617f`),
`test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl`
(blob `74874a3f3179a74f4cef6b80829eefdf289b069b`).

## See also

- `doc/08_tracking/bug/radix_literal_suffix_split_and_digit_cap_2026-08-08.md`
  (the suffix-split / digit-cap defect, FIXED by `b0f5308993`)
