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
