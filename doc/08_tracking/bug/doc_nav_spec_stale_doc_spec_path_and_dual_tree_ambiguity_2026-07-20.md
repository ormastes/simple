# `doc_nav_spec.spl`: hardcoded dead `doc/spec/...` path + ambiguous dual doc/test tree
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-20
**Component:** `test/02_integration/app/doc_nav/doc_nav_spec.spl`
**Severity:** Medium — the doc-navigation consistency spec cannot currently
validate anything (every read returns empty), and the underlying doc/test
layout genuinely appears duplicated, not just renamed
**Found by:** whole-suite triage campaign (re-run at `timeout 180`; not a
false-positive timeout — it completes in ~120s and fails for real)

## Symptom

`doc_nav_spec.spl` reads paths like `doc/spec/math_render_spec.md`,
`doc/spec/math_blocks_spec.md`, `doc/spec/loss_nograd_blocks_spec.md` (37
occurrences of the `doc/spec/` prefix in this one file) and asserts on their
contents (feature IDs, source references, date stamps, scenario counts).
Every read returns an empty string — `doc/spec/` does not exist as a
directory at all; per `.claude/rules/structure.md`, generated specs live
under `doc/06_spec/` (`doc/06_spec/` — "Specs — generated from sspec,
mirrors test/ paths — DO NOT refactor"). This looks like a straightforward
STALE-TEST dead-path issue (missing the `06_` numbering prefix that was
added after this spec was written), **except**:

## Why this wasn't fixed as a mechanical rename

The target files exist in **two parallel locations**, and so does the
`test/` source tree that presumably generates them:

```
doc/06_spec/feature/usage/math_render_spec.md
doc/06_spec/03_system/feature/usage/math_render_spec.md   (duplicate)

test/feature/usage/math_render_spec.spl
test/03_system/feature/usage/math_render_spec.spl          (duplicate)
```

(same duplication for `math_blocks_spec` and `loss_nograd_blocks_spec`).
Both doc copies and both spec copies exist simultaneously. A mechanical
`doc/spec/` → `doc/06_spec/` substitution requires picking one of the two
roots (`doc/06_spec/feature/usage/...` vs
`doc/06_spec/03_system/feature/usage/...`) across all 37 occurrences, and
guessing wrong silently changes which content the consistency checks
validate — the opposite of what a "doc navigation consistency" spec is for.
Given the "never rewrite an assertion to force green" rule and that this
spec's entire job is to catch exactly this kind of drift, blind-guessing
the path was judged riskier than leaving it documented.

## Recommended direction (not attempted here)

Someone who owns the doc-generation pipeline should confirm: (a) which of
`test/feature/usage/*` vs `test/03_system/feature/usage/*` is the live
source (and whether the other is a stale duplicate that should be removed),
and (b) update `doc_nav_spec.spl`'s 37 `doc/spec/` references to the
correct `doc/06_spec/...` root accordingly. Until that's resolved, this
spec cannot validate anything (it reads empty strings and fails on
every content assertion).

## Note

Spec left unmodified — the assertions themselves are reasonable content
checks; only the path prefix needs correcting, and doing that safely
requires resolving the dual-tree ambiguity first.

## Resolution — 2026-11-25 (branch work/p3-docnav-20261125)

**Root cause.** Three independent staleness defects in
`test/02_integration/app/doc_nav/doc_nav_spec.spl`:

1. **Dead path prefix.** All 33 `doc/spec/<name>.md` references pointed at a
   directory that no longer exists; spipe-docgen's default output dir is now
   `doc/06_spec` (`src/app/spipe_docgen/spipe_docgen/main.spl:93`) and it
   mirrors the input test path, so `test/feature/usage/<name>_spec.spl`
   generates to `doc/06_spec/feature/usage/<name>_spec.md`. Every `read_file`
   returned empty, so no content assertion could ever pass.
2. **Dual-tree ambiguity — resolved deterministically, not by guess.**
   `doc/06_spec/feature/usage/` and `doc/06_spec/03_system/feature/usage/`
   both exist and differ, but the spec itself invokes docgen on
   `test/feature/usage/*` inputs, and docgen mirrors the input path — so the
   output the spec produces and must validate is unambiguously
   `doc/06_spec/feature/usage/`. (The `03_system` mirror is generated from the
   separate `test/03_system/feature/usage/*` sources.)
3. **Wrong INDEX.md target.** The INDEX assertions read
   `doc/02_requirements/app/INDEX.md` (a requirements index with zero
   references to the math specs). docgen generates its own index at
   `{output_dir}/INDEX.md` = `doc/06_spec/INDEX.md`
   (`generate_index_page` in `src/app/spipe_docgen/spipe_docgen/generator.spl:998`).
   Verified by running docgen, not by assumption.

**Fix.**

- All 33 `doc/spec/` references replaced with `doc/06_spec/feature/usage/`;
  the stale comment "spipe-docgen generates to doc/spec/ by default" corrected.
- INDEX.md assertions repointed at `doc/06_spec/INDEX.md`. Because docgen
  rebuilds INDEX.md from *only the spec files of the current invocation*
  (verified: a single-file run overwrites INDEX.md with a 1-entry index), the
  spec now first runs one multi-file docgen invocation over all three math
  specs, then asserts the index links each of them.

**Content reconciliations (evidence-based, no assertion deleted or weakened):**

- `loss_nograd_blocks_spec`: expected scenario count changed 38 -> 27.
  Evidence: `test/feature/usage/loss_nograd_blocks_spec.spl` contains exactly
  27 `it`/`slow_it` lines and 0 skip/pending; freshly generated
  `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` reports
  `| Total scenarios | 27 |` and contains no "38" anywhere; even the
  previously committed (HEAD) generated doc already said 27. The "38" was
  stale drift from an older revision of the test file.
- `math_render_spec` counts (129 total / 129 active / 0 skipped) and
  `math_blocks_spec` count (28) re-verified against freshly regenerated docs
  and the test runner (`SPEC FILE VERDICT: ... declared>=129 executed=129
  passed=129 failed=0`); no change needed.
- Feature IDs (#1090, #1099), categories, difficulty, status, source refs and
  2026 date stamps re-verified against regenerated docs; no change needed.

**Verification.** Environment note: the older Rust seed binary
(`D:\dev\simple\bin\simple`, 39,066,112 bytes) cannot parse this lane's
`unit X: i64` stdlib syntax ("expected As, found Newline" in
`src/lib/common/types.spl`); the newer seed already deployed in sibling
worktrees (38,403,072 bytes, copied to this worktree's gitignored
`bin/simple`) parses and runs the lane correctly.

Commands (from worktree root):

```
./bin/simple spipe-docgen test/feature/usage/math_render_spec.spl
  -> DONE Generated 1 docs (1 complete, 0 stubs)
./bin/simple spipe-docgen test/feature/usage/math_render_spec.spl \
    test/feature/usage/loss_nograd_blocks_spec.spl \
    test/feature/usage/math_blocks_spec.spl
  -> DONE Generated 3 docs (3 complete, 0 stubs); INDEX.md links all 3 specs
SIMPLE_LIB=src ./bin/simple test test/02_integration/app/doc_nav/doc_nav_spec.spl --mode=interpreter
  -> SPEC FILE VERDICT: test/02_integration/app/doc_nav/doc_nav_spec.spl outcome=OK declared>=34 executed=34 passed=34 failed=0 skipped=0 blocked=0 dropped=0
     Results: 34 total, 34 passed, 0 failed (exit 0, ~14 min in interpreter mode)
```
