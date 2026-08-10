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
