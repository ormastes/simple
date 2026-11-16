# Seed native path resolves enums by bare name; two `HttpStatus` enums collide (2026-11-14)

Status: verification-pending (fix landed in PR; native verification below)

## Symptom
`SIMPLE_NATIVE_BUILD_RUST=1 simple native-build src/app/llm_caret/main.spl`:
```
llm_caret\main.spl: mir: Unsupported HIR construct: unknown variant or method 'Ok'
on enum HttpStatus (declared variants: OK, Created, Accepted, NoContent, BadRequest, ...)
```
`main.spl:47` explicitly imports `HttpStatus` from `std.nogc_sync_mut.http_server`
(variants `Ok`, `PayloadTooLarge`, `TooManyRequests`, ...). The variant list in
the error belongs to `std.nogc_sync_mut.io.http_client_types.HttpStatus`
(variant `OK`), which is also in the build closure. The build log carries
`warning[enum-bare-name-ambiguous]: enum HttpStatus is registered again with a
different variant set` (`interpreter_module/module_evaluator/evaluation_helpers.rs:1062`).

## Root cause
The seed's enum registry (interpreter side, reused by HIR/MIR lowering on the
native path) is keyed by the enum's bare name, not by `(module, name)`; the last
co-compiled module to register wins, and an explicit `use` cannot override it.

## Expected
An explicitly imported enum resolves to the imported module's definition; two
modules may each define `HttpStatus` with different variants. Renaming the
public `io.http_client_types.HttpStatus` (re-exported by `http_sffi`, 29 uses)
is not the fix.

## Repro (to be written as the red test first)
Two modules `a.spl` / `b.spl` each `enum Status:` with different variants; an
entry that `use`s `a.Status` and returns `Status.OnlyInA`; `native-build` the
entry with both modules in the closure. Expect: compiles and runs. Actual: the
MIR error above.

## Real root cause (found while fixing)
Not the flattened-lane enum owner machinery (that already resolves owners). In the
native-project lane `hir/lower/import_loader.rs` registers every imported enum into the
bare-name type registry with `update_named`, so a dependency-only load (an imported
module's own `use`) of a same-named enum from another file replaced the enum the
entry file explicitly `use`d; and a cached explicit import never re-asserted it.

## Fix
`Lowerer` tracks names explicitly requested by depth-0 `use`s (`direct_enum_wanted`) and
the file that first declares each during that import (`direct_enum_owners`); a
same-named enum from another file is refused (`claim_imported_enum_name`). Cached
explicit imports restore their enum via `enum_loads` (`reassert_cached_enums`). Names
not explicitly imported keep the old last-wins fallback.

## Evidence (2026-11-14, bootstrap-profile seed)
- RED: `hir::lower::tests::enum_import_scope_tests` 2/2 failed with
  `hir: Unsupported feature: enum 'Status' has no variant named 'OnlyInA'`.
- GREEN: 2/2 pass; `hir::` 499/499; `module_cache` 31/31.
- `native-build src/app/llm_caret/main.spl`: before `failed=1` (`unknown variant 'Ok' on enum HttpStatus`);
  after `compiled=663 failed=0`, exe links, `--help` exit 0.
- devhub native-build: `compiled=300 failed=0`, `--help` exit 0.
- `sync_query_string_decode_spec.spl` 3/3.
- Unrelated pre-existing failures seen (no enum/import involvement): mir
  `primitive_field_method_call_is_builtin_qualified`, native_project
  `native_project_fs_platform_aliases_keep_the_sync_path_owner` and
  `test_linker_fails_closed_on_undefined_runtime_symbol`, interpreter 4 (vulkan, cache_host, ...).

## #6953 follow-up (2026-11-16): discriminant = owning enum's declared index

Branch `work/enum-discriminant-order-6953-20261116`. Lowering, MIR, codegen,
the interpreter bridge and `rt_enum_discriminant` now take a variant's
discriminant from its owning enum's declaration; the process-global
name-keyed registry (`runtime/src/value/objects.rs` `positional_registry`,
read by `hash_variant_discriminant`) is only the reported fallback
(`warning[enum-discriminant-owner-unresolved]`, fatal with
`SIMPLE_ENUM_OWNER_STRICT=1`). Builtin `Ok`/`Err`/`Some`/`None` keep 0/1 only
when the owner IS `Result`/`Option` (`TraceLevel.None` = 0 is its own index).

Open, recorded rather than fixed:
- **`TypeRegistry::update_named` is last-registration-wins by bare name**
  (`compiler/src/hir/type_registry.rs` ~243), and so are the interpreter's
  `GLOBAL_ENUMS` / `INTERP_ENUMS` maps the bridge consults. Two same-named
  enums visible in one module (or one interpreter thread) resolve to whichever
  registered last; the merged-name guard (`imports.rs duplicate_enum_defs` ->
  `mark_merged_enum`) only covers the global seeded table.
- **`codegen/instr/calls.rs` `compile_known_enum_constructor_call`** stays
  name-only even when `ctx.enum_defs` holds a non-merged owner row: the
  codegen context carries no merged-name set to tell the two apart. Not hit
  in the integ4 Stage 2 build (1517 modules, 0 owner-unresolved warnings).
- Untyped `.is_ok()`/`.is_err()` in Cranelift/LLVM codegen and the
  `?`-operator `Err` checks (`hir/lower/expr/control.rs`) assume the builtin
  Result. An erased (ANY/NIL) subject with a builtin variant name now resolves
  to builtin `Result`/`Option` in `owned_or_unique_variant_discriminant`, so a
  visible user enum declaring `Err` at another index no longer hands its index
  to `r.is_err()` / `case Err` on an untyped Result. A user-enum value reaching
  an erased subject is still tested against the builtin index (wildcard enum id 0).
- **Runtime Ok/Err tests must check the Result enum id (fixed for unwrap/expect).**
  Owner-correct numbering gives a user enum's first two variants 0/1. The Rust
  `rt_unwrap_or_trap` / `rt_expect_or_trap` tested `disc == Ok/Err` with no
  enum-id check, so `_sffi_tuple_get_req<MirConstValue>` (`rt_tuple_get<T>(..)
  .unwrap()`) returned `MirConstValue.Int`'s raw payload and aborted on `.Float`
  ("called unwrap on Err"): every Stage 2 llvm native-build failed with
  `E-BACKEND-LLVM-CONST-GARBAGE` (base d63d23935b6: old seed llvm `hello 42`,
  fixed seed garbage; struct-key/transient merges not involved). Both now
  require enum id 0 or 2, matching the C twin. Still open: `rt_try_is_absent`
  with `expected_enum_id == 0` (erased `?`) and `rt_enum_check_variant` id-0
  wildcard callers match any enum at the Err/Ok index.
- **native -> interpreter enums are not bridged at all:**
  `runtime_bridge.rs` `runtime_to_value_inner` (~442) has no
  `HeapObjectType::Enum` arm, so a native enum value crossing back into the
  interpreter becomes `Value::Nil` through the unsupported-heap fallback. The
  owner-index fix covers interp -> native only.
