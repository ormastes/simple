# `simple lint` aborts a whole file with "string index out of bounds"

**Status:** OPEN 2026-09-19
**Area:** semantic phase reached from `src/app/cli/lint_entry.spl`
**Severity:** blocks EVERY lint rule on the affected file, not one rule
**Found by:** measuring COLL diagnostic coverage over 52 files for
  `doc/08_tracking/bug/coll020_detector_blind_to_non_identifier_guarded_value_2026-09-19.md`

## What happens

```
$ bin/simple lint test/01_unit/compiler/30.types/simd_capabilities_extern_backing_spec.spl
error: semantic: string index out of bounds: index is 7628 but length is 7628
  (preview="\"\"\"\\n## Purpose and audience\\nPurpose: prove that every `exter")
```

No diagnostic of any kind is produced for the file. This is not a COLL
problem: lint emits **nothing at all**, so every rule in the linter is
silently skipped on that file. A user running `bin/simple lint` on it gets an
error line and no findings, and nothing tells them which rules never ran.

## Affected files (4 of the 52 measured)

| file | index / length |
|---|---|
| `test/01_unit/compiler/30.types/simd_capabilities_extern_backing_spec.spl` | 7628 |
| `test/01_unit/app/sspec_maintain/scorer_loopholes_adjacent_spec.spl` | 4779 |
| `test/01_unit/compiler/common/impl_to_free_fn_zero_definition_census_spec.spl` | 13780 |
| `test/03_system/plan_acceptance/simpleos_production_master_plan_completion_status_spec.spl` | 26909 |

The sample was 52 files chosen for an unrelated reason (they contain an array
dedup loop), so 4/52 is an incidence rate in arbitrary repo source, not a
count of the affected population. A tree-wide scan has not been run.

## The signature

`index == length` in every case, and the index is within ~20 bytes of the
file size (7628 vs 7644 bytes for the first). So the reader walks one past the
end of the source buffer rather than mis-indexing in the middle. Every one of
the four opens with a `"""` docstring at line 1, and the error preview is that
docstring — consistent with a scan that starts at the leading literal and
runs off the end.

## Reduction status: NOT reduced

A three-line file with a leading `"""` docstring lints clean, and `head -60`,
`head -100` and `head -140` of the 179-line original all lint clean. Whatever
combination triggers it is in the last ~40 lines in the context of the whole
file, and bisection was not carried further. **This record is filed without a
minimal snippet deliberately** — the four real files above reproduce it every
time and are the better starting point than a guessed reduction.

## Why it matters beyond this lane

Seven of the 54 genuinely-quadratic dedup sites in the measured corpus are in
files that abort this way, so they can never be reported by any lint rule. The
same files are analysed FINE by `bin/simple fix`, which takes a parse-only
path — see
`doc/08_tracking/bug/lint_and_fix_disagree_on_analysable_files_2026-09-19.md`.
