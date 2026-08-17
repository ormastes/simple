# Stage 2 loses cross-module codec result field types

Status: provider workaround applied; compiler fix remains open.

Admitted compiler:

- path: `/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- SHA-256: `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`
- sanity evidence: `status=pass`

Reproduction: compiling `src/app/provider_cli/native_provider_v1.spl` through
the admitted `native-build --entry-closure --emit-archive --no-mangle` path
failed while accessing `.ok` on the result of
`encode_provider_query_result_v1`:

`hir: Unsupported feature: cannot infer field type ... struct
'ProviderQueryWireWriteV1' field 'ok'`

Explicitly annotating cross-module codec results is the safe provider-side
fix. The compiler should eventually preserve the declared return type through
cross-module calls without requiring redundant local annotations.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: reproduction requires the specific admitted compiler named in this record
(`/mnt/data/bs2/final-e73-run2/.../stage2-admitted/simple`, SHA-256
`2ec71042dd...`), which is not present on this host. The provider-side
annotation workaround is already applied, so nothing is currently broken; the
remaining item is the compiler-side improvement (preserve declared return types
through cross-module calls), which cannot be validated without that binary.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## Update 2026-08-17 — reframed: cross-module is not the discriminator

Reduced to an 8-line same-module reproducer. A struct RETURNED BY VALUE from a
function reads every field back as `1` after
`SIMPLE_BOOTSTRAP=1 bin/simple native-build --entry-closure`, while the same
struct constructed inline in the same function is correct:

```
inline len=3 tag=77returned len=1 tag=1
```

Cross-module imports are not required; return-by-value is the trigger. The
`.ok` failure recorded above is that defect wearing a diagnostic. The
provider-side annotation workaround silences the message but does not correct
the VALUE.

Root cause, controls, and gating specs:
`doc/08_tracking/bug/native_entry_closure_struct_return_by_value_fields_read_as_one_2026-08-17.md`
· `test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl`
· `test/01_unit/compiler/codegen/native_aggregate_return_transport_class_spec.spl`

Note also: without `SIMPLE_BOOTSTRAP=1` the same two-module reproducer dies
with `unresolved type: WireWriteV1` EVEN WHEN the struct is explicitly imported,
because `try_register_bootstrap_global_symbol`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:930`) returns
false outright unless that variable is set. That is a separate, still-open
defect in the same file.
