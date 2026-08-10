# BUG: AOT/LLVM backend emits invalid IR (`void type only allowed for function results`) for struct-bearing programs

- Date: 2026-08-10
- Severity: MEDIUM (blocks AOT measurement/execution of struct value-semantics
  probes; scope beyond probes unquantified)
- Binary: fresh Rust seed `src/compiler_rust/target/release/simple`
  (59,000,784 B, built 2026-08-10 04:16, post-`9106761fe76`)

## Repro

```
bin/simple native-build probe.spl -o out
```

where `probe.spl` is the minimal struct probe from
`doc/07_guide/language/value_semantics_by_engine.md` (a `struct Flat` with
f64+i64 fields, one assignment, two prints). Deterministic failure:

```
error: AOT compile error in probe: Compile error in backend (llvm): llc failed (exit 1):
/usr/bin/llc-20: error: <tmp>.ll:64:42: error: void type only allowed for function results
```

Same failure at `:64:43` for the 6-position matrix probe. Not host
saturation — fails within seconds, reproducibly.

## Impact

- The AOT column of the struct value-semantics truth table
  (`doc/07_guide/language/value_semantics_by_engine.md`) cannot be measured.
- Any single-file `native-build` of a program constructing a struct in `main`
  likely hits the same emission path.

## Next step

Dump the temp `.ll` (`SIMPLE_KEEP_LLVM_IR` or rerun with the tmp file
preserved) and identify which MIR instruction lowers to a void-typed value
use at line 64 — plausibly the struct init/copy path added by the F1
campaign (`MirInst::AggregateCopy`, `StructInit`) in the LLVM lane, which is
exercised far less than Cranelift.

## Status 2026-08-10 (later session): NOT REPRODUCIBLE at current WC — lane measured

- Binary: deployed `bin/release/x86_64-unknown-linux-gnu/simple` (29,577,536 B,
  mtime 2026-08-09 04:50). `native-build` interprets the WC compiler `.spl`
  live, so the emission code under test is the current worktree backend.
- Minimal probe (`struct Flat{f64,i64}`, assignment, prints) BUILDS and RUNS,
  output `a.n=7 b.n=99` (copy). Full 6-position matrix also builds and runs —
  measured AOT column recorded in
  `doc/07_guide/language/value_semantics_by_engine.md`.
- The known guard for exactly this llc error lives in `translate_alloc`
  (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` ~L2015-2026,
  in-tree since 2026-08-08): void-typed spill slots from var_reassign_ssa are
  backed with `i64`. The 04:16 seed binary named above no longer exists and a
  fresh seed rebuild currently fails much earlier on unrelated WC semantic
  drift (`CompileOptions` has no field `target_opt_ctx`), so the original
  failing emission cannot be re-dumped; most plausible explanation is the
  failing run went through a stale/divergent WC state of the backend.
- Gap analysis: no spec exercises AOT (specs run interp/JIT), so this lane can
  rot invisibly. Durable gate added: `scripts/check/check-aot-smoke.shs` —
  native-builds a struct probe, RUNS it, asserts printed values (not mere
  absence of error); PASS/FAIL/ERROR verdicts, ERROR (exit 2) on
  timeout/kill so saturation is never a false verdict. Measured PASS ~2 min.
- NEW defects observed while measuring (separate from this bug):
  1. AOT list/dict element extraction ALIASES (`var e = lst[0]; e.n = 11`
     mutates `lst[0]`) where interp and post-F1 JIT copy.
  2. AOT interpolation of an `f64` struct field prints raw i64 bits
     (`f.a=4607182418800017408` for 1.0).
