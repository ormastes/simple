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

## 2026-08-17 re-verification — original defect NOT reproducible; lane RED for a different reason

Re-ran the exact probe this doc specifies (`struct Flat{f64,i64}`, copy,
`b.n = 99`, four prints) through `bin/simple native-build` against the deployed
`bin/release/x86_64-unknown-linux-gnu/simple`.

**The `void type only allowed for function results` llc error did not occur.**
Nothing in the 1,802-line build log mentions `llc`, `void type`, or a `.ll`
line/column. That failure mode stays closed — the `translate_alloc` guard in
`_MirToLlvm/core_codegen.spl` covers it and no evidence of recurrence exists.

**But the AOT lane is currently RED on an unrelated, previously unrecorded
error**, so this doc must not be closed as simply fixed:

```
$ sh scripts/check/check-aot-smoke.shs
FAIL — AOT lane broken: native-build exit 1, binary absent

$ bin/simple native-build tmp_aot_probe.spl -o tmp_aot_probe_bin   # exit 1
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
error: native-build worker exited with code 1.
```

Note the gate's own diagnostic path is weak here: it greps `-i error` from the
build log and printed nothing usable, because the real line is below the
truncation banner. The verdict line is still correct and fail-closed; the
diagnostic excerpt is not, and is worth widening.

Attribution, measured rather than assumed: this is **not** caused by the
concurrent `module_lowering.spl` fix landed in `153e331d605`. A/B in one tree
with one binary — reverting that file to its parent blob and re-running the same
`native-build` reproduces the identical exit 1 — so the break predates it. The
working copy at the time of this run carried ~13k lines of uncommitted
`src/compiler_rust/**` changes from parallel sessions, and `native-build`
interprets the working-copy compiler live, so the most likely origin is that
drift rather than any landed commit. Whoever owns those changes should re-run
the gate; `scripts/check/check-aot-smoke.shs` is the durable detector and is
doing its job.
