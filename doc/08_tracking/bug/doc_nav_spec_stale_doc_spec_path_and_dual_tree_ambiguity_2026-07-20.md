# `doc_nav_spec.spl`: hardcoded dead `doc/spec/...` path + ambiguous dual doc/test tree

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
