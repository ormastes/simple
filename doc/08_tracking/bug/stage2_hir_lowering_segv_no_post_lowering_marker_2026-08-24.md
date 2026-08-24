# stage2 SEGVs DURING HIR lowering on some inputs (no `post-lowering` marker)

- **Filed:** 2026-08-24
- **Lane:** Q (slice-B compile sweep: `30.types`, `35.semantics`, `50.mir`, `60.mir_opt`, `70.backend`)
- **Status:** OPEN — recorded, not fixed
- **Binary:** `/mnt/data/worktrees/goal-main-1/build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`
  (132,945,096 bytes, sha256 prefix `d13409a6e905fe36`)

## Symptom

`simple compile <file> --format=smf -o <out>` exits **rc=139 (SIGSEGV)** having
printed `[bootstrap-error-count] source_idx=0 point=entry count=0` and the
`[build] hir 0/N step 2/6 ... <module>` line, and then **never printing any
`point=post-lowering` line at all**. Tail of a representative log
(`src/compiler/30.types/associated_types_tests_def_impl.spl`):

```
[build] parse 3/3 step 2/6 +1126ms dt=0ms complete
[build] hir 0/3 step 2/6 +1126ms dt=0ms pending
[bootstrap-error-count] source_idx=0 point=entry count=0
[build] hir 0/3 step 2/6 +1126ms dt=0ms compiler.types.associated_types_tests_def_impl
timeout: the monitored command dumped core
Segmentation fault
```

## Why this is a distinct class, not the known constant

Two other rc=139 shapes are already known on this binary and must not be
conflated with this one:

1. The **known post-emit fault**. Every `compile --format=smf` currently ends
   badly after lowering succeeds — documented as ``error: hir codec: no
   `Visibility` arm for tag -1`` (a bool passed in the `visibility` slot at 25
   `SymbolTable.define()` sites, fixed in source, redeploy pending). On this
   stage2 build it manifests as a SEGV rather than that error line. Either way
   it happens **after** `point=post-lowering count=0` has been printed, so the
   compile is diagnosable and the file is classified CLEAN.
2. A file with real lowering errors prints `point=post-lowering count=N` with
   N>0 and is diagnosable.

This class is neither: lowering itself dies, so **no error count is ever
produced for the file**. A "0" here is UNKNOWN, never a pass — which is exactly
why the sweep classifies it separately (`NOLOWER`) instead of letting a missing
error count read as clean.

## Affected files observed so far (first 40 files of slice-B)

9 of 40, i.e. ~23% of the files swept at the time of filing:

- `src/compiler/30.types/associated_types_tests_def_impl.spl`
- `src/compiler/30.types/associated_types_tests_resolve.spl`
- `src/compiler/30.types/bidirectional_checking.spl`
- `src/compiler/30.types/const_keys.spl`
- `src/compiler/30.types/higher_rank_poly_tests_quantifier.spl`
- `src/compiler/30.types/higher_rank_poly_tests_unification.spl`
- `src/compiler/30.types/macro_checker.spl`
- `src/compiler/30.types/simd.spl`
- `src/compiler/30.types/type_infer/context.spl`

The full sweep is still running; the live ledger is
`/mnt/data/goal-logs/laneq/results.tsv` (columns: path, class, rc, seconds,
`post-lowering` marker count), with the complete stderr log retained under
`/mnt/data/goal-logs/laneq/logs/` for every non-CLEAN file.

## Possible correlation, NOT yet established

Two of the nine (`const_keys.spl`, `macro_checker.spl`) crashed immediately
after the compiler emitted a `[hir-payload-origin-unresolved]` /
`[hir-callable-dep-origin-unresolved]` advisory for the symbol `Symbol` owned
by `compiler.types.const_key_type` / `compiler.types.macro_def`. Lane Q has
since fixed the underlying missing imports for `const_key_type`, so a re-run of
the non-CLEAN rows against the fixed tree will say whether the crash was
*caused* by the unresolved-origin state or merely adjacent to it. Until that
re-run lands, the correlation is recorded as a lead and nothing more — the
other seven crashed with no advisory at all.

## Not reproducible against a rebuilt compiler yet

The binary under test is a prebuilt stage2. Any source fix in `src/compiler/`
only takes effect after a bootstrap redeploy, so this record deliberately makes
no claim about whether the crash survives current `main`.
