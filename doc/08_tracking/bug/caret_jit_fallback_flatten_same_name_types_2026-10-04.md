# llm_caret main.spl de-JITs: flatten-lane same-name types + 3 source bugs (2026-10-04)

**Symptom.** `simple run src/app/llm_caret/main.spl ...` (Rust seed, macOS arm64)
dropped the whole module to the interpreter:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'HttpResponse'
field 'headers' (declared fields: status_code, status, body, error, is_ok)
```

Under that fallback every chat turn and every TUI redraw ran interpreted.

## Root causes (four, peeled one after another)

### 1. Compiler: the run/JIT lane collapses same-named types across modules (not fixed here)

`load_module_with_imports` flattens the whole import closure into one module
with one bare-name namespace. `TypeRegistry::name_to_id` is bare-keyed and the
last registration wins. The duplicate-layout sidecar that could pick the right
variant is turned off on purpose in this lane
(`src/compiler_rust/driver/src/exec_core.rs:1155`, `SIMPLE_JIT_DUP_STRUCT_FEED`,
fail-closed, see `lint_dejits_whole_program_span_struct_collision_2026-08-18.md`).
So whenever the closure holds two layouts with the same name and builds both
with named literals, the module de-JITs.

**Second defect, which made the diagnostic misleading.** The literal-field gate
`src/compiler_rust/compiler/src/hir/lower/expr/collections.rs:496-512`
(`declared_here`) is supposed to reject an unknown field only when the struct is
declared in the *same file*. In the flatten lane, however,
`hir/lower/type_registration.rs:50,173` gives every flattened declaration the
same `current_file`, the entry file. The same-file check therefore always
passes. The error names the entry file and the field list of whichever layout
registered last, which is not the literal that failed. The message pointed at
`main.spl:812`, but replacing that literal changed nothing. The literals that
really failed were inside the library modules (`http_sffi.spl`
`make_http_response` vs `http_server/types.spl` static constructors). A minimal
two-import probe reproduces the problem with the roles reversed.

Collisions in caret's closure, and how the source now avoids them:

| name | modules | fix |
|---|---|---|
| `HttpResponse`, `HttpStatus`, `HttpMethod` | `nogc_sync_mut/io/http_sffi.spl` vs `nogc_sync_mut/http_server/types.spl` | renamed the sffi side to `SffiHttpResponse`/`SffiHttpStatus`/`SffiHttpMethod`. `io/__init__.spl` and `nogc_async_mut/io/http_sffi.spl` were already exporting these names, which had been left dangling |
| `Rect` | `llm_caret/workbench/tui_layout.spl` (x,y,w,h) vs `tui/widget.spl` (x,y,width,height) | renamed the caret-local one to `WorkbenchRect` |

The enum collision matters most. The two `HttpStatus` enums differ in case
(`OK`/`Ok`) and in variant order, so once the struct collision is gone a
silently JIT-compiled discriminant could be wrong.

**Real fix (open):** module-qualified type identity in the flatten lane. The
definition and use sites need their module identity kept, and `Span` currently
has no file. Until then, give each declaration a unique bare name.

### 2. Parser: `fn f() -> i64: return 0` parses `return` as an identifier (not fixed here)

A one-line function body that starts with `return` lowers to a load of a global
named `return`. Cranelift reports `GlobalLoad: unresolved identifier 'return'`,
and the interpreter fails with `variable 'return' not found`. The expression
form `fn f() -> i64: 0` works. The inline-body entry point is
`src/compiler_rust/parser/src/parser_helpers.rs:189` (`parse_inline_or_block`
-> `parse_item`). The only 13 occurrences in the repo were the HTTP/2 frame
constants in `nogc_sync_mut/http_server/h2_server.spl`, now written in
expression form.

### 3. Source: SIMD `sqrt` called an undeclared `rt_sqrt`

`FixedVec.sqrt`/`recip_sqrt` (and the `ScalableVec` twins) in all three variants
(`nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`) called `rt_sqrt` without
declaring it, and the seed runtime does not export it. The result was
`unresolved external symbol 'rt_sqrt'`, found with `SIMPLE_JIT_SYMBOL_TRACE=1
SIMPLE_JIT_STRICT=1`. They now use `elements[i].sqrt()`.

### 4. Source: missing half on main, `pane_team.spl` imports 3 functions that never existed

`workbench/pane_team.spl` imports `multi_caret_manager_of`,
`reconcile_multi_caret_manager` and `settle_multi_caret_manager`, but
`multi_caret_manager.spl` at `origin/main` 90c6e6ed27b defines none of them.
They are now implemented by pulling the existing poll/stop status rules out into
`reconcile_`/`settle_`. `poll_`/`stop_` route through them and behave as before
(`multi_caret_manager_spec` 13/13).

## Verification

`SIMPLE_JIT_STRICT=1 simple run src/app/llm_caret/main.spl --help` exits 0. A
`--prompt "hello"` run prints no `[jit-fallback]` and no
`reason=jit-compile-error`. Only the partial `hybrid-interp-splice` for
unexported `rt_*` symbols remains.
