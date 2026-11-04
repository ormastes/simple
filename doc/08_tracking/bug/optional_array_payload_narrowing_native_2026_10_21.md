# optional_array_payload_narrowing_native_2026_10_21

Status: open. Workaround pinned by n88b_native_workaround_shapes_spec; native repro n88b_native_producer_idioms_native.spl; real fix still needed (20.hir/50.mir type propagation or runtime class layout). Native-codegen defect (HIR/MIR); source @workaround sites: src/app/io/native_build_cache.spl, src/app/io/native_build_output_mode.spl, src/app/compiler_schema/fold_gen.spl.
The real fix is in 20.hir/50.mir type propagation (owned by phase-3 agent a508755bae341480a); not changed here.

## Workaround pinned only (n88_b, 2026-11-04) - real fix still open

Source repair/workaround is pinned by `bin/simple.exe test test/01_unit/compiler/80.driver/n88b_native_workaround_shapes_spec.spl` (8/8 pass on the seed).
Native repro fixture: `test/fixtures/compiler/n88b_native_producer_idioms_native.spl` (+ `.expected`); covers the NARROW_ line (nil guard then payload use).

Stage3 repro (expected: no diff output, exit 0; then remove the matching `@workaround` tags):

```
bin/simple native-build --entry test/fixtures/compiler/n88b_native_producer_idioms_native.spl -o build/n88b_idioms.exe && build/n88b_idioms.exe | diff - test/fixtures/compiler/n88b_native_producer_idioms_native.spl.expected
```
