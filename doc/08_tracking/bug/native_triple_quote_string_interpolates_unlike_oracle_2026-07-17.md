# Native path: triple-quoted `"""..."""` strings interpolate `{...}`, but the oracle treats them as raw/literal

**Date:** 2026-07-17
**Severity:** Medium (silent behavioral divergence, no diagnostic on either
side — both paths compile and run successfully, they just disagree on the
resulting string content)
**Status:** open
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom

```simple
fn main():
    val inner = 9
    val ml = """line1 {inner}
line2 done"""
    print "MLZ:{ml}|END"
```

- Oracle (`bin/simple run`): `MLZ:line1 {inner}` / `line2 done|END` — `{inner}`
  printed **literally**, not interpolated. The oracle treats `"""..."""` as a
  raw/non-interpolating multi-line string literal.
- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): `MLZ:line1 9` /
  `line2 done|END` — `{inner}` **is** interpolated to `9`.

Reproduced with a fresh probe filename (cache keys on name+content) to rule
out a stale-cache artifact; the divergence is stable across two independent
runs with different filenames.

## Context

`"""..."""` is not documented in
`doc/07_guide/quick_reference/syntax_quick_reference.md`'s Strings section
(which documents `"..."` as interpolating-by-default and `'...'`/`r"..."` as
raw/non-interpolating, but says nothing about triple-quoted strings). Given
triple-quoted strings are used elsewhere in this codebase purely as
docstrings (e.g. the top-of-file docstring convention seen throughout
`test/**/*.spl`), the oracle's "raw, no interpolation" behavior is plausibly
the intended semantic (matching the common language convention that a
docstring literal shouldn't have surprise `{...}` substitution) — but this is
inferred from the oracle's behavior and the docstring-convention usage
pattern, not from an explicit spec. Filed as a divergence regardless of which
side is "more correct": the two paths silently disagree with no diagnostic
on either side.

## Expected

Native's handling of `"""..."""` should match the oracle: either both
interpolate or neither does. Given the absence of documentation and the
docstring-convention precedent, matching the oracle's raw/non-interpolating
behavior is the safer default unless a design decision says otherwise.

## Suggested direction

Find where the native lexer/parser distinguishes triple-quoted string
literals from ordinary double-quoted ones (if it distinguishes them at all —
the divergence suggests native may be lexing `"""..."""` as three
independent tokens or reusing the ordinary double-quoted-string interpolation
path without checking for the triple-quote form) and confirm whether it
should route through the same "no interpolation" handling as single-quoted
(`'...'`) / raw-string (`r"..."`) literals elsewhere in the lexer.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native), with two independently-named probe files to rule out caching.
