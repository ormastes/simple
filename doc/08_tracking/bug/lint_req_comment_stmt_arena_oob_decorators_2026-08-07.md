# `bin/simple lint` crashes with stmt-arena OOB on `decorators.spl` (pre-existing)

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- Found: 2026-08-07, while landing WP-9 (skip governance,
  `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`)
- File: `src/lib/nogc_sync_mut/spec/decorators.spl`
- Likely cause: `src/compiler/35.semantics/lint/required_comment.spl`'s
  `req_comment_stmt_get_tag` walker (REQC001/REQC004 check)

## Symptom

`bin/simple lint src/lib/nogc_sync_mut/spec/decorators.spl` (single file,
foreground) crashes instead of producing a diagnostics summary:

```
[stmt_get_tag] OOB idx=66 arena_len=41 arena_gen=1 -> -1
error: semantic: array index out of bounds: index is 66 but length is 41
```

## Confirmed pre-existing, not introduced by WP-9

Reproduced on `git show HEAD:src/lib/nogc_sync_mut/spec/decorators.spl`
written back to the real path (verified byte-identical to `HEAD` via
`git show | md5sum`), linted in isolation, then restored — the untouched
`HEAD` version of the file crashes the same way (`idx=66 arena_len=41`).
WP-9's edits to the same file also crash (different arena size, same shape:
`idx=58 arena_len=50` before an extraction refactor, `idx=63 arena_len=45`
after), so the crash is content-size-sensitive but not caused by the WP-9
changes specifically — the same lint pass on `condition.spl` (an untouched
sibling in the same package) passes clean, and the WP-9 module
`skip_governance.spl` also lints clean (0 errors, only PTAG warnings).

## Impact

Cannot get a clean `bin/simple lint` verdict on `decorators.spl` alone (single
file or in any batch that includes it) — the pass crashes before printing a
"Found N error(s)" summary for that file. Every OTHER file changed under
WP-9 (`spec.spl`, `skip_governance.spl`, `mod.spl`, the new spec) lints
without crashing; `spec.spl`'s reported errors are pre-existing bare-primitive
API warnings unrelated to this WP (confirmed by line-shift diff against
`HEAD`).

## Repro

```sh
bin/simple lint src/lib/nogc_sync_mut/spec/decorators.spl
```

## Suggested owner

Compiler/lint team — `required_comment.spl`'s statement-tag arena indexing
(`_check_stmt`, `req_comment_stmt_get_tag`) likely mis-tracks arena
generation/length across a `fn(...)-> fn(text, fn())`-returning closure with a
nested-if body; decorators.spl is exactly that shape (three closures returning
closures, one nested if inside).
