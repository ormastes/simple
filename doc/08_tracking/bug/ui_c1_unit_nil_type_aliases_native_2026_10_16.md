# UI C1 native dependency type-name compatibility

Status: resolved & workaround tags retired (2026-11-25). Canonical lowercase `unit`
is the permanent Simple spelling for unit `Result<unit, E>` and `(JsValue) -> unit`
signatures (pinned by `test/01_unit/compiler/80.driver/n88b_native_workaround_shapes_spec.spl`);
HIR (`src/compiler/20.hir/hir_lowering/types.spl`) resolves lowercase `unit`/`void`
and `Nil` (per `doc/07_guide/language/robust_semantic_absence.md § Unit type`) to
`HirTypeKind.Unit`, while capital `Unit` is intentionally not aliased. All 29
`@workaround` tags across `host_taskbar_runtime.spl`, `bounded_channel.spl`,
`wm_bridge.spl`, and `src/lib/js/builtins/array.spl` have been retired while keeping
the canonical `unit` signatures intact.

The exact 0CD6 producer, compiling frozen C1, reports unresolved `Unit` and
`Nil` types in the UI closure. Its HIR type lowering recognizes lowercase
`unit` and `void` as `HirTypeKind.Unit`; uppercase names require declarations.

The affected `Unit` annotations belong to `Result<Unit, E>` signatures in
`wm_bridge.spl`, `bounded_channel.spl`, and the HostTaskbarRuntime owner.
Successful branches return `Ok(())`. Dependent modules repeat the unresolved
type diagnostic when importing these signatures. The repair uses canonical
`unit` only in those type arguments and preserves all function bodies.

The only affected `Nil` annotation is the callback return in JS `array_forEach`.
Its callback result is discarded and the function is a side-effect loop. It
does not construct or transport a `JsValue.Nil`. Canonical `unit` describes
that callback contract without introducing a runtime sentinel or nominal type.

Recovery reference: `c1f630e7a05d539852f53444231d4f90fd76d6a4`.
The source compatibility tags identify the exact changed signatures. Do not
revert them merely after fetching a compiler alias change; require an admitted
producer and actual regression evidence first.

Evidence: `phase4-ui-0cd6-c1f6-cycle2/terminal-failure-analysis` under the shared
bootstrap evidence root. The UI lane has used two of three verification
attempts. No third attempt has been launched for this repair.

## Verification pending (n88_b, 2026-11-04)

Source repair/workaround is pinned by `bin/simple.exe test test/01_unit/compiler/80.driver/n88b_native_workaround_shapes_spec.spl` (8/8 pass on the seed).
Native repro fixture: `test/fixtures/compiler/n88b_native_producer_idioms_native.spl` (+ `.expected`); covers the UNIT_OK line (Result<unit,_> with Ok(())).

Stage3 repro (expected: no diff output, exit 0; then remove the matching `@workaround` tags):

```
bin/simple native-build --entry test/fixtures/compiler/n88b_native_producer_idioms_native.spl -o build/n88b_idioms.exe && build/n88b_idioms.exe | diff - test/fixtures/compiler/n88b_native_producer_idioms_native.spl.expected
```
