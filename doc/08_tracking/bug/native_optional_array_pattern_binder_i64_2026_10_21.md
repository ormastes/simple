# Native Optional array pattern binder loses array type

Status: open; source compatibility workaround authored, runtime UNRUN.

Actual native_noop_admission failure canonical-batch81/unit2 reports native issue143: for-in source MIR type I64 at compiler/80.driver/driver_build/incremental.spl1035. SdnValue.as_array is declared [SdnValue]? (common/sdn/value.spl135). Its result is bound by `if val entries_array=arr`; iterating that bound value is rejected as scalar.

The optional-array pattern binding must retain the array and element types. Negative scalar iterator diagnostics remain required. Related nested array iteration failures are not assumed to have the same exact lowering owner.

Compatibility workaround: explicitly type the bound entries/dependencies/outputs arrays as [SdnValue] inside their existing present branches, preserving missing/wrong-type behavior, order and all cache identity checks. No cast or Any. Removal condition: a rebuilt pure-Simple producer compiles and runs the equivalent unannotated if-val iteration and actual BuildCache.load/native_noop entry without issue143; remove annotation workarounds and rerun real cache load caller checks.

## Workaround pinned only (n88_b, 2026-11-04) - real fix still open

Source repair/workaround is pinned by `bin/simple.exe test test/01_unit/compiler/80.driver/n88b_native_workaround_shapes_spec.spl` (8/8 pass on the seed).
Native repro fixture: `test/fixtures/compiler/n88b_native_producer_idioms_native.spl` (+ `.expected`); covers the BINDER_ line.

Stage3 repro (expected: no diff output, exit 0; then remove the matching `@workaround` tags):

```
bin/simple native-build --entry test/fixtures/compiler/n88b_native_producer_idioms_native.spl -o build/n88b_idioms.exe && build/n88b_idioms.exe | diff - test/fixtures/compiler/n88b_native_producer_idioms_native.spl.expected
```

## Fixed in source (bd2af2006a0) - native evidence 2026-11-09
`lower_for_iterator` peels `Optional(Array|Slice)` for the binder (#143,
`fix(mir): for-in iterates Optional-array payload binders`, bd2af2006a0; spec
`test/01_unit/compiler/50.mir/for_in_optional_array_payload_binder_spec.spl`).
Native repro on the self-hosted stage2 `C:/dev/p3new/stage2new/stage2_new4.exe`
(native-build of the fixture's `sum_binder`/`opt_array` idiom, unannotated
`if val arr = a: for x in arr:`) prints `BINDER_6_0` (expected `BINDER_6_0`).
Status fix-implemented-verification-pending; the `@workaround` annotation in
incremental.spl is removed after a stage3 producer rebuild re-runs BuildCache.load.
