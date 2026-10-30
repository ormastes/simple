# Concrete Result declaration type is absent from bound symbols

Status: narrow repair prepared; native regression pending. The generated MC/DC source workaround is maintained separately by the generator owner.

Observed native failure: admitted attempt11 compiler source `540671a010a9cc413d8bd2aa464c01e5b02900e9` rejects `.unwrap()` at generated entry line 25, after 78 of 79 MIR modules pass. Retained log: `/tmp/simple-phase2-runner-native-attempt11-20261030/plain-run3/direct-diagnostic/build.log`. Both fatal diagnostics identify an untyped receiver, one in the synthetic main representation and one in the module initializer.

The actual retained HIR cache is `/tmp/simple-phase2-runner-native-attempt11-20261030/plain-run3/cache/hir/43b93d96749b9ab9e4d3f457707f70b5dc9e3846cc1dd43b581e965168431ed1.parser-v4.hir`, SHA256 `06b6349c9db391c3df4eff8ced12825be3e7c7934d7983f26b1a54c20263947f`. Its envelope checksum was verified. Exact records were read against the generated codec schema; this was not a whole-module decoder execution. `__simple_mcdc_manifest_result` has a `HirConst` carrying `Result<text,text>` (name at line 7365), but Const symbol 21 (line 1221) and synthetic-main Variable symbol 39 (line 1666) both have absent optional type slots. Both `.unwrap` receiver records have `has_type_=false`. The imported function symbol has a declared Function(text,i64) return of Result<text,text>.

## Repair

`lower_hir_const_decl` publishes the settled declaration type to the existing Const symbol selected by ID. It does not search for or replace another same-name binding. Local binding transport additionally recognizes a direct call's exact Function symbol and carries its settled return type into the existing symbol/Let binding pipeline. Generic declarations, explicit type arguments, unresolved callees, indirect variables and unsettled return components stay unhandled. No MIR method-name fallback is introduced.

The existing recursive settled-type predicate moves unchanged into `binding_types.spl` so constants and local calls share one rule. The native fixture `test/fixtures/compiler/declared_result_bindings/main.spl` checks global/local Result unwrap, lexical shadowing and two same-named provider functions with distinct payload types. `test/01_unit/compiler/hir/declared_call_binding_type_spec.spl` checks exact symbol selection and rejects shadow variables, missing IDs, generics, explicit instantiations and unsettled payloads.

Validation: retained-record proof and source review prepared. Native compilation/execution and independent Astra review remain required. The generated-entry workaround or a passing smaller test cannot qualify the full compiler or retire the original failure without a corrected producer exercising it.
