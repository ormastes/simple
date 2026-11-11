# A non-parseable `{...}` interpolation body silently falls back to literal text, swallowing an enclosed `+` concatenation

- **Filed:** 2026-09-05
- **Status:** SUPERSEDED (2026-11-11, lane int10) — silent swallow closed on origin/release/1.0.0; failure mode is now the loud staged warning W-STR-BRACE-001 (`a67d50a53be8`), and the warning→error ratchet this record's unblock condition asks for is owned by successor bug `string_interp_malformed_brace_warning_to_error_2026-11-09`; see addendum below
- **Area:** language / lexer — text-literal interpolation
- **Severity:** HIGH (silent wrong value, no diagnostic)
- **Binary:** `src/compiler_rust/target/debug/simple` (Rust seed)

## Symptom

When a `+` concatenation sits **inside** an open `{...}` interpolation body, the
interpolation scanner treats the `"` characters around the concatenated
expression as a *nested* string within the interpolation body, scans on to the
matching `}`, fails to parse the body as an expression, and then emits the whole
body as **literal text**. No error, no warning: the program runs and the string
contains the source text `" + v + "`.

## Minimal repro

```simple
fn main():
    val v: text = "V"
    print "B1=[" + ("{a;b} " + v + " y") + "]"     # brace run CLOSES before the concat
    print "B2=[" + ("{x (" + v + ")} y") + "]"     # concat is INSIDE the open brace
    print "B3=[" + ("{b+=$1} " + v + " y") + "]"   # brace run CLOSES before the concat
```

Observed:

```
B1=[{a;b} V y]
B2=[{x (" + v + ")} y]
B3=[{b+=$1} V y]
```

`B2` is the defect: expected `{x (V)} y`.

## Mechanism, and why it is a bug rather than documented interpolation

Simple interpolates `"{expr}"`, and a body that *does* parse behaves as
documented — `"{b} ..."` correctly raises `semantic: variable 'b' not found`.
B1 and B3 also behave correctly: their brace runs close before the `+`, so the
literal terminates at its own `"` and the concatenation happens.

The defect is the failure mode for a body that does **not** parse. Rather than
being rejected, it is silently reinterpreted as literal characters — and because
the scanner has already run past the intervening `"` delimiters looking for the
matching `}`, the concatenated expression is absorbed with it. The trigger is
therefore precisely `{` ... `" + expr + "` ... `}` within one text literal, not
"any invalid brace run": `FIELD_AUDIT_AWK` in
`test/03_system/plan_acceptance/scilib_port_ndarray_spec.spl` is a chain of
brace-heavy literals joined by `+` and renders **correctly**, because each of its
brace runs closes before its `+`.

## Impact observed

This produced a **false-clean shape** on a compliance oracle. In
`scilib_port_ndarray_spec.spl` REQ-SCILIB-NDARRAY-06 the audit pipeline ended
with `awk '{b+=$1; n+=$2} END{print (" + column + ")+0}'` — the `+ column +`
sits inside the open `END{`. The mangled command made `awk` emit nothing,
`shell_count` read `0`, and the violation count read as `0`, i.e. "no violations
found" from a scan that never ran. It was caught only because the paired planted
control (which must return 1) also returned 0. An audit without such a control
would have reported a clean tree.

## Workaround in place

Select the column with `cut -d' ' -f<n>` instead of a second `awk`, so no
concatenation sits inside an open brace
(`scilib_port_ndarray_spec.spl:88-95`). This is a workaround, not a fix; the
lexer behaviour is unchanged.

## Unblock condition

A `{...}` interpolation body that does not parse as an expression is a **compile
error**. Note the naive alternative — "terminate the literal at its closing `"`
regardless of braces" — is wrong: it would break legitimate nested-string
interpolation such as `"{f("x")}"`.

## Specs to ship with the fix

1. Reproducing spec: `"{x (" + v + ")} y"` with `v = "V"` must yield `{x (V)} y`,
   or be rejected with a diagnostic naming the unparseable body — never the
   silent literal `{x (" + v + ")} y`.
2. Generalization spec: the same swallow with other non-parseable bodies wrapping
   a concatenation (`"{a; (" + v + ")}"`, `"{x=(" + v + ")}"`,
   `"{f(){(" + v + ")}}"`), plus controls that a valid interpolation `"{v}"`
   still interpolates and that a brace run closing before the `+` (B1/B3 above)
   still concatenates.

## Addendum 2026-11-11 (lane int10) — SUPERSEDED: no longer reproducible; silent failure mode replaced by staged warning

int10 re-ran this record's exact minimal repro unmodified on the tracked seed
(`bin/simple.exe`, build-commit `46fe8f6b6def`, plain run mode, fixture
`build/p3fix-int10/row8_repro.spl`, gitignored):

```
B1=[{a;b} V y]
B2=[{x (V)} y]     <- filed defect case: now the EXPECTED value, no swallow
B3=[{b+=$1} V y]
exit=0
```

B2 — the case that printed `B2=[{x (" + v + ")} y]` at filing — now prints
`{x (V)} y`. The concatenation is no longer absorbed: the `{x (` brace run is
kept as literal text and the literal terminates at its own `"`, so the `+`
concatenates normally. The failure mode is no longer silent: the seed lexer
and parser emit `W-STR-BRACE-001` ("... is kept as literal text; use `{{`
...") at every malformed-brace site. Controls guarding the documented
invariants all hold on the same seed (`build/p3fix-int10/row8_controls.spl`):
`"{v}" -> V`, `"{v + "!"}" -> V!`, `"{wrap("x")}" -> (x)` (the exact
nested-string interpolation case this doc warned must keep working), and a
brace literal concatenated from a separate string. Absorbing change:
`a67d50a53be8` (2026-11-09, "fix(string-interp): W-STR-BRACE-001 warning for
malformed brace in string literal (staged)") — ancestor of both this base
(`1771ca481337`) and the tracked seed build; it landed with regression
coverage re-run here: `test/01_unit/compiler/frontend/string_interp_brace_escape_spec.spl`
**6/6 PASS** (seed-smoke, `--mode=interpreter --no-cache`).

Residual, owned elsewhere: this record's unblock condition ("must be a
compile error") is deliberately NOT met — the behavior is staged as a warning
because the corpus has ~15,033 such sites; the warning→error ratchet
(including the corpus codemod) is the explicit subject of successor bug
`doc/08_tracking/bug/string_interp_malformed_brace_warning_to_error_2026-11-09.md`
(Status: open). The false-clean audit-oracle impact class named here is
closed by the loud warning: a swallowed/malformed brace can no longer produce
a silent wrong string.
