# Context-pack tool expands its input; its guard is orphaned; the pair blocks every PR

**Date:** 2026-08-31
**Status:** OPEN — real product defect, currently unenforced
**Severity:** high — a compression tool that expands input, plus a required CI
check that no PR can currently satisfy

## The defect

`src/app/context/main.spl` advertises "90% reduction in LLM context tokens".
Measured on this tree by `scripts/check/check-context-pack-reduces.shs`:

```
check-context-pack-reduces: selftest 4/4 fixtures correct
  src/app/audit/ffi_analyzer.spl      raw=9338  pack=9497   reduction=-1.3%
  src/app/audit/ffi_usage.spl         raw=8601  pack=8754   reduction=-1.3%
  src/app/audit/sffi_analyzer.spl     raw=9368  pack=9529   reduction=-1.3%
  src/app/audit/sffi_usage.spl        raw=8623  pack=8778   reduction=-1.3%
  src/app/browser/render_adapter.spl  raw=17722 pack=17887  reduction=0.1%
FAIL — 5 file(s) packed, 5 below the 10% floor
```

Four of five packs are **larger than the file they pack**. The guard's own
selftest passes 4/4, so the guard is working correctly — the tool is not.

The guard's header records the original diagnosis: passing three different
target symbols changed output by under 10 bytes, so the documented "extracts
only symbols used by target" was doing nothing at all, while
`test/01_unit/app/tooling/context_generate_spec.spl` is 208 lines with **zero
`it(` blocks** and asserts only `to_contain("token_estimate:")` — a substring
check on a label. The lane was green throughout.

## Why it blocks unrelated work

`Code Idiom & Structural Ratchet Gates` (`.github/workflows/repo-hygiene.yml`)
is a **required** check under an org-level ruleset that admin merge cannot
bypass. It currently fails because `check-guard-wiring.shs` reports
`check-context-pack-reduces.shs` as orphaned — wired into no hook and no CI job.

That produces a deadlock with no in-scope escape:

| Action | Result |
|---|---|
| Leave the guard orphaned | required check fails (guard-wiring ratchet) |
| Wire the guard properly | required check fails (guard itself, on the real defect above) |
| Add an opt-out line | the guard's own text forbids exactly this: "do not add an opt-out line merely to make this pass" |
| Fix `src/app/context/main.spl` | required check goes green — but this is real work on an unrelated tool |

So every PR in the repo is blocked until the context-pack tool actually
compresses, or someone grants a ruleset bypass actor.

## Verified NOT the cause

PRs #147 and #149 introduce none of this. #147 changed zero files under
`scripts/` or `.github/`, so it cannot have orphaned a guard, and neither PR
touches `src/app/context/`. See
[[preexisting_main_gate_debt_blocking_all_prs_2026-08-31]].

## Fix direction

`src/app/context/main.spl`'s symbol extraction appears not to filter by target
at all — that is what makes output size track input size and be insensitive to
the requested symbol. Fix the extraction, confirm reduction clears the 10%
floor, then wire the guard into the ratchet job alongside its siblings. Replace
the zero-`it(`-block spec with one that asserts the size property rather than
the presence of a label.

Do not wire the guard before the tool is fixed: that trades an orphan-guard
failure for a real-defect failure and leaves the repo just as blocked.
