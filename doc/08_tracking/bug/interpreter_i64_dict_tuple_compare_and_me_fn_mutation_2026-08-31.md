# Two interpreter defects found while building the textual BM25 side-index
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-31
**Status:** OPEN — both observed in real code, neither reduced to a minimal case
**Found by:** P9 textual-DB BM25 side-index (`src/lib/nogc_sync_mut/database/fts_lexical.spl`)
**Related:** [[local_dict_list_push_silently_dropped_2026-08-31]] — a third
interpreter container/mutation defect found the same day by a sibling package.
Three in one session suggests a cluster worth investigating together rather than
three isolated workarounds.

---

## Defect 1 — `i64` from a Dict-iteration tuple compares false against an equal value

**Severity: high — silent wrong answer, not a crash.**

Raw `i64` values extracted from a dict iteration tuple:

```
for (k, v) in dict:
    ...   # v fails plain ==/!=/< against an otherwise-equal i64
```

The values **print identically** and compare **false**. There is no error and no
diagnostic — a lookup, a dedup, or a membership test simply returns the wrong
answer, and any test whose fixture doesn't happen to depend on that comparison
passes.

This is worse than a type error precisely because it is invisible: the printed
representation agrees, so eyeballing a debug dump confirms the wrong conclusion.

**Workaround in place:** `.to_text()` round-trip comparison via `_norm_i64` /
`_i64_list_contains`, documented in that module's docstrings. **This is a
workaround, not a fix** — recorded here rather than normalized silently, per
CLAUDE.md.

**Not established:** minimal reduction; whether native codegen shares it;
whether other integer widths or other tuple-producing iterations are affected;
whether it is the boxing/erasure path (cf. the "chained methods on erased
receivers" limitation in `.claude/rules/language.md`, which may be the same root
cause).

---

## Defect 2 — nested `me fn` self-call mutations do not propagate to the caller's `self`

A nested `me fn` self-call's mutations were not observed to reach the calling
method's `self`. The mutation appears to succeed and is then lost.

**Workaround in place:** `update_row` was inlined rather than delegating to a
nested `_remove_row` mutator, with a comment explaining why.

**Not established:** whether this is the documented "nested closures can READ
outer vars but not MODIFY" limitation (`.claude/rules/language.md`) surfacing
through method calls, or a distinct defect. If it is the former, the rule text
should be widened to say so explicitly, because the current wording says
*closures* and a reader will not expect it to cover `me fn` delegation.

---

## Next step

Reduce each to a minimal spec under `test/01_unit/compiler/`, establish the
interpreter/native split, and check whether all three of today's defects share a
root cause in value boxing or COW propagation. Until then the workarounds above
stand and are documented at their call sites.

## Addendum 2026-11-11 — lane interp5 verdict: SUPERSEDED

Verdict: **SUPERSEDED** — both defects no longer reproduce on the refreshed
seed; the in-tree fix family covers both shapes:

- Defect 1 (i64 from a dict-iteration tuple compares false):
  `9509a45eab80d29e451dfd66b14a757d137bd8f2` (2026-09-12, "fix(interp,jit):
  `for k, v in d.items()` destructures; `Dict.items` bound under JIT"), with
  typed-key/write-back hardening later in `015d40bfa306` /
  `bafc15f38a7d` (2026-10-31). All are ancestors of base `b364745fdbf8`.
- Defect 2 (nested `me fn` self-call mutations lost): the 2026-09-12
  interpreter in-place-kernel family `35c6d1338cb9` ("one place-aware in-place
  kernel for mutating calls through nested places") and `433641435d9f`, with
  `b190db07085b` (2026-11-03, "explicit mut struct parameter takes full
  write-back branch") later covering the same family. The sibling same-day bug
  `local_dict_list_push_silently_dropped_2026-08-31` was closed stale
  2026-11-03 on the deployed seed; this lane re-verifies the whole cluster on
  the 2026-11-11 refreshed seed.

Seed-smoke verification (2026-11-11, lane interp5, refreshed seed
`bin/simple.exe` 2026-11-11 build, `SIMPLE_LIB=src`, `SIMPLE_TIMEOUT_SECONDS=0`,
`build/review/scratch/interp5_bug6_repro.spl` — minimal reductions of both
defects):

- Interpreter (`SIMPLE_EXECUTION_MODE=interpret`): defect 1 —
  `for (k, v) in {"a": 42}` yields `v==42 -> true`, `v<43 -> true`,
  `v!=42 -> false`; defect 2 — `t.update_row(2)` delegating to nested
  `me _remove_row` leaves `rows=[1, 3]`. Both correct.
- JIT control (`SIMPLE_EXECUTION_MODE=jit`): identical correct output.

The `_norm_i64` / `_i64_list_contains` workarounds still present in
`src/lib/nogc_sync_mut/database/fts_lexical.spl:51-61,172-173,220` are now
unnecessary but harmless; simplifying them back to direct `==`/`<` comparisons
is a safe follow-up cleanup, not a correctness fix.

