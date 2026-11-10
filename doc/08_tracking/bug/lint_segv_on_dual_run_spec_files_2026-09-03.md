# `simple lint` SEGVs on the dual-run spec files

- **Status:** OPEN
- **Found:** 2026-09-03, linting a new dual-run tranche spec before commit
- **Area:** `src/app/lint` / `src/compiler/90.tools/lint`
- **Engine:** `bin/simple` Rust seed `v1.0.0-rc.1`, Windows x86_64
- **Pre-existing, NOT introduced by the tranche E change** — reproduced on an
  untouched sibling spec that has been in the tree since before this session.

## Symptom

```
$ sh scripts/check/lint-cached.shs test/01_unit/lib/common/spec/dual_run_simd_lane_spec.spl
scripts/check/lint-cached.shs: line 97: 31329 Segmentation fault      "$bin" lint $opts "$f"
FAIL — 1 file(s) checked, 1 with findings
```

Identical crash on
`test/01_unit/lib/common/spec/dual_run_tranche_e_spec.spl`. The linter does not
emit a finding and does not print a verdict — it dies, and the wrapper's
fail-closed accounting reports the crash as "1 with findings", which is
misleading: there is no finding, there is no lint result at all.

## Why it matters

Two things, both bad:

1. **The pre-commit lint requirement cannot be satisfied for this file class.**
   `.claude/rules` require `bin/simple lint` on changed `.spl` files. For any
   dual-run spec that is currently impossible — the tool crashes rather than
   passing or failing.
2. **A crash is being reported as a finding.** `lint-cached.shs` maps a
   non-zero exit to `FAIL — ... 1 with findings`. A SEGV (rc 139) and a genuine
   style violation are indistinguishable in that verdict line, so a reader
   cannot tell "this file has a problem" from "the linter died". The wrapper
   should classify rc >= 128 as a CRASH, distinct from a finding — the same
   three-way classification `check-stage-binaries-runnable.shs` already uses.

The stdlib twins themselves lint clean:
`src/lib/common/simd_lane_pure.spl` and `src/lib/common/str_search_pure.spl`
both report `Lint passed: all files clean`. The crash is specific to the spec
files.

## Reproduction

```
sh scripts/check/lint-cached.shs test/01_unit/lib/common/spec/dual_run_simd_lane_spec.spl
```

Not narrowed further: the crashing construct has not been bisected out of the
spec, so "dual-run spec files" is a description of the observed population, not
a diagnosis. Likely suspects to bisect first, since they are what distinguishes
these specs from ordinary ones: `extern fn` declarations with struct-typed
parameters (`Vec4f`, `Vec16u8`, `Vec4u64`), and array-of-array literals.

## Impact on the tranche E change

The three lint runs performed were:

| file | verdict |
|---|---|
| `src/lib/common/simd_lane_pure.spl` | `PASS — 1 file(s) checked` |
| `src/lib/common/str_search_pure.spl` | `PASS — 1 file(s) checked` |
| `test/01_unit/lib/common/spec/dual_run_tranche_e_spec.spl` | SEGV (this bug) |
| `test/01_unit/lib/common/spec/dual_run_simd_lane_spec.spl` (control, untouched) | SEGV (this bug) |

The spec was NOT lint-verified, because it cannot be. Recorded here rather than
claimed as clean.

## Addendum 2026-11-11 — lane runner4: SUPERSEDED

Reproduced the repro command on release/1.0.0 tip `b364745fdbf8` with the
refreshed 2026-11-11 seed (seed-smoke, JIT lane, no execution-mode override):

- `test/01_unit/lib/common/spec/dual_run_tranche_e_spec.spl` (one of the two
  crashing files named here): `bin/simple.exe lint` completes, **rc=0** —
  no SEGV, real verdict.
- `test/01_unit/lib/common/spec/dual_run_simd_lane_spec.spl` (the other
  named file): no longer exists in the tree — deleted by merge `9e7e7a526edb`
  (PR #7597, 2026-11-07). Its successor population
  (`test/01_unit/lib/common/dual_run_jit/str_twins_jit_dual_run.spl`,
  `dual_run_tranche_[a-e]_spec.spl`, `dual_run_pairs_spec.spl`,
  `dual_run_shadow_spec.spl`) lints without crashing
  (`str_twins_jit_dual_run.spl` rc=0).

The dual-run spec lint crash no longer reproduces; the pre-commit lint
requirement is satisfiable for this file class again. The wrapper
misclassification point (a SEGV rc being reported as "1 with findings" by
`lint-cached.shs`) was a secondary observation; with the crash gone it no
longer triggers for this class, and no wrapper change was made in this
lane.

Verdict: SUPERSEDED.
