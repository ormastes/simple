# Seed interpreter: `text.bytes()` u8 elements compare wrong via `<=`/`>=` (BoxInt tag-shift)

- **Date:** 2026-07-17
- **Area:** `src/compiler_rust` seed interpreter (bootstrap seed only — `src/compiler_rust/target/release/simple`).
  NOT reproduced as a duplicate_check bug; found while root-causing an apparent
  `duplicate-check` token-mode detection failure (see
  `doc/08_tracking/bug/duplicate_check_cosine_quadratic_timeout_2026-07-01.md`
  sibling investigation, task: worker_O_dup_sanity).
- **Severity:** high (silently corrupts any code that does relational
  comparison — `<=`, `>=`, `<`, `>` — on a byte pulled out of `text.bytes()`
  against an integer literal, with no error/crash).
- **Status:** open — filed as a new, more precise repro; related to (but not
  the same code path as) `test_runner_expect_failure_swallowed_u8_bytes_2026-07-03.md`
  (test-runner matcher, `bytes[44] == 99u8`, still open) and
  `baremetal_u8_index_equality_2026-05-30.md` (native/freestanding codegen
  `[u8]` indexing, fixed 2026-05-30 — different code path, does not cover
  this interpreter case).

## Symptom

A byte read from `text.bytes()` prints correctly, but a relational comparison
against a plain `i64` literal gives the wrong answer, and an explicit
`val c: i64 = b` annotation does NOT fix it — only `int(b)` does.

Minimal repro (`bin/simple run` on the seed, `src/compiler_rust/target/release/simple`):

```simple
fn main():
    val s = "a\u{2014}b"          # any string with a multi-byte UTF-8 char
    val byte_arr = s.bytes()
    val b = byte_arr[0]           # the ASCII 'a' byte, decimal 97
    print "b={b}"                 # prints: b=97  (correct)
    print "b >= 97 -> {b >= 97}"  # true   (correct)
    print "b <= 122 -> {b <= 122}"# FALSE  (WRONG — 97 <= 122 is true)
    val c: i64 = b
    print "c={c}"                 # prints: c=776  (== 97 << 3 — WRONG, should be 97)
    print "int(b)={int(b)}"       # prints: int(b)=97 (correct — int() unboxes properly)
    print "int(b)<=122 -> {int(b) <= 122}"  # true (correct once explicitly cast)
```

`776 = 97 << 3`: the raw boxed/tagged representation of the `u8` (value shifted
left 3 bits, presumably a pointer/NaN-boxing tag scheme) leaks through
relational comparison and explicit `i64` re-annotation, but NOT through
`print` interpolation or the `int(...)` builtin cast (both of which correctly
unbox). Plain arithmetic (`b + 0`) also does *not* fix it — the result still
prints as `97` under interpolation but fails the same `<=` comparison as
`b` itself, i.e. the corrupted tag survives simple arithmetic.

## Impact discovered via

`src/compiler/90.tools/duplicate_check/tokenizer.spl`'s `tokenize()` iterates
`source.bytes()` and classifies each byte via range checks
(`b >= 97 and b <= 122`, `b >= 48 and b <= 57`, etc.) to find identifier/digit
runs. Any `.spl` file containing a multi-byte UTF-8 character *anywhere*
earlier in the file (even fully inside a `#` comment, a string literal, or as
a stray byte — position/context does not matter) causes every subsequent
byte's classification to become unreliable, which desyncs the tokenizer's
scan position for the rest of the file and corrupts all downstream
tokens/keywords. Confirmed this is not a `duplicate_check`-specific bug: the
tokenizer's dispatch logic is correct pure-Simple code; the seed interpreter's
comparison of the boxed `u8` is the actual defect.

**Not a production-path finding**: per repo convention (`bin/release/<triple>/simple`
is the self-hosted default; the seed at `src/compiler_rust/target/release/simple`
is bootstrap-only and known to have `BoxInt` tag artifacts elsewhere — see
`project_stage4_wall_and_hardening_2026-07-04` memory entry, "seed BoxInt <<3
mangles enum heap-handles thru ANY channels; SEED-specific, pure-Simple codegen
CLEAN"). This investigation could only run on the seed (deployed self-hosted
binary is stale / rejects `rt_cli_arg_count`, per current redeploy-wall
status), so this repro is NOT yet confirmed against the pure-Simple self-hosted
compiler. If the self-hosted binary is available, re-run the minimal repro
above against it before prioritizing a seed-side fix.

## Workaround (used in this task, NOT landed as a code change)

Wrap any byte pulled from `.bytes()` in `int(...)` before relational
comparison. Deliberately NOT applied inside
`src/compiler/90.tools/duplicate_check/tokenizer.spl` for this task: the
tokenizer's own logic is correct, the defect is in the seed's comparison
of boxed `u8`, and patching production Simple source to route around a
bootstrap-only interpreter artifact (unverifiable against the real
self-hosted compiler in this session) would be treating the symptom, not
the cause, in a file outside this task's fix scope.

## Next step

Bisect the seed interpreter's relational-operator lowering for `u8`-typed
operands (`src/compiler_rust`) — likely the same `BoxInt` tag-shift family as
the Stage4 wall note. Add a minimal `.spl` regression
(`xs = "a\u{2014}b".bytes(); assert xs[0] <= 122`) once a fix lands, and
re-verify `duplicate-check --mode token` against a fixture containing
non-ASCII comments/docstrings (common in this i18n'd repo) to confirm the
tokenizer needs no changes once the seed defect is fixed.
