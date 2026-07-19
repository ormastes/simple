# Native entry closure references undeclared `call_type_args`

Status: OPEN (recorded 2026-07-19)

## Reproduction

With pure-Simple LLVM Stage3
`950f96418ae2f55d2eae1732a440e66509335c34526a603b92d31a060e16bdbc`,
native-build an entry that imports
`compiler.driver.driver_source_loading._driver_entry_import_module_paths` with
`--source src/compiler --source src/app --source src/lib --entry-closure`.
The entry may call the helper with this existing regression input:

```simple
val imports = _driver_entry_import_module_paths("use std.real\n\"\"\"\nuse fake.block\n\"\"\"\n")
val long_imports = _driver_entry_import_module_paths("x".repeat(65536) + "\nuse std.real\n")
```

The incremental LLVM build reaches compiler closure codegen, then fails:

```text
src/compiler/30.types/type_infer/inference_expr.spl: llvm codegen: semantic:
llvm global load referenced undeclared symbol `call_type_args`
```

Expected: the entry closure either declares the referenced local or does not
emit the load, then links the focused probe. Cranelift and cross-target status
are not yet measured. This is separate from the restored phase-one import scan;
`entry_closure_physical_source_dedup_spec.spl` remains its regression owner.
