# `bin/simple lint` crashes with stmt-arena OOB on `decorators.spl` (pre-existing)

- Status: CLOSED — ALREADY-FIXED, reproduced clean 2026-08-17 (see the
  verification section at the end of this file). The earlier "OPEN (P2) /
  re-verified by triage shard 02" line was a stale-doc classification, not an
  executed repro.
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

---

## Verification 2026-08-17 (compiler-lint lane) — ALREADY FIXED, reproduced-clean, and the attribution was WRONG

### Executed repro — the crash is GONE

The documented repro was re-run verbatim on the current tree:

```
$ nice -n 19 bin/simple lint src/lib/nogc_sync_mut/spec/decorators.spl
...
src/lib/nogc_sync_mut/spec/decorators.spl:48:0: error[ARG002]: Function has 13 parameters (limit: 12)
src/lib/nogc_sync_mut/spec/decorators.spl:114:0: error[ARG002]: Function has 13 parameters (limit: 12)

Found 2 error(s), 2 warning(s), 0 auto-fix(es) available

Lint failed in 1 file(s)
RC=1
```

`rc` was captured on the line **after** the command, never through a pipe. The
pass now **reaches its summary line** — which is exactly what this record says
it could not do ("crashes before printing a 'Found N error(s)' summary"). There
is no `[stmt_get_tag] OOB` line and no
`error: semantic: array index out of bounds` anywhere in the 271-line output.
`rc=1` is the normal "lint found errors" exit, not a crash; the two ARG002
errors are ordinary parameter-count findings unrelated to this bug.

### Root cause of the fix (content, not SHA)

`src/compiler/10.frontend/core/ast_stmt.spl:556-561` — `stmt_get_tag` now
carries an explicit bounds guard that returns `-1` for a stale index instead of
indexing the arena:

```
    if idx < 0 or idx >= stmt_tag.len():
        print "[stmt_get_tag] OOB idx={idx} arena_len={stmt_tag.len()} arena_gen={ast_generation()} -> -1"
        return -1
```

A contributing fix is at `src/compiler/80.driver/driver_source_pipeline_parsing.spl:52-72`,
which reorders `rt_transient_array_scope_end()` **before** `ast_reset()` so the
reset's arena allocations are not born inside a transient scope and then freed —
the `arena_len=0` flood this class produced.

### The "likely cause" attribution in this record is incorrect — do not chase it

`src/compiler/35.semantics/lint/required_comment.spl` **cannot** produce this
crash and could not have:

- Its only stale-index-sensitive accessor is `req_comment_stmt_get_tag`
  (`required_comment.spl:47`), a one-line delegation to the now-guarded
  `stmt_get_tag`.
- Its `_check_stmt` (`required_comment.spl:121-171`) dispatches on `tag` through
  an `if/elif` chain with **no else**, so a `-1` tag falls through every branch
  and returns an empty warning list. It is already fail-safe against a stale
  index.
- It never calls `stmt_get_span`, the unguarded accessor
  (`grep` for `stmt_get_span` in that file returns nothing).

**Verdict: ALREADY FIXED (stale doc). No patch applied; none was in scope.**

### Standing residual risk, filed here rather than silently dropped

The 2026-08-01 guard was applied to **exactly one of six** accessors over the
same arena. In `src/compiler/10.frontend/core/ast_stmt.spl` these remain
unguarded and will still panic on a stale index:

| accessor | line | unguarded expression |
|---|---|---|
| `stmt_get_span` | 572 | `stmt_span[idx]` |
| `stmt_get_expr` | 578 | `stmt_expr[idx]` |
| `stmt_get_name` | 583 | `stmt_name[idx]` |
| `stmt_get_type` | 590 | `stmt_type_tag[idx]` |
| `stmt_get_body` | 596 | `stmt_body[idx]` |

That is the same defect class this record described, merely on sibling
accessors. It is **not** fixed here: `10.frontend` is owned by another
concurrent lane. It needs its own row against that tree.

Not proven by this lane: that the five accessors above are reachable with a
stale index today — only that the guard which makes `stmt_get_tag` safe has no
counterpart in them.
