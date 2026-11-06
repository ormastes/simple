# Seed interpreter resolves same-named free functions process-wide

- **Id:** seed_interp_cross_module_free_fn_collision_2026_11_06
- **Found:** 2026-11-06, wiring the single-owner vector-parser lane into `src/app/simple_web_server/`.
- **Engine:** Rust seed, `SIMPLE_EXECUTION_MODE=interpret` (tree-walk interpreter).
- **Status:** FIXED 2026-11-06 (branch `work/seed-interp-batch2-20261106`) — see "Resolution".

## Symptom

`simple-web-server --single-owner` (or `--vector-provider ...`) accepted a
connection and died with

```
error: semantic: undefined field 'reason': class HttpResponse has no such field or getter
```

on the first response. `main.spl` loads both HTTP stacks: the sync
`std.nogc_sync_mut.http_server` (SimpleHttpServer, used by the lane) and the
async `std.http_server` (hosted HttpServer + SSR). Both define a free
`serialize_response`; the async one takes `HttpResponseData` (which has
`reason`). The sync writer's call `serialize_response(resp)` in
`src/lib/nogc_sync_mut/http_server/response.spl` dispatched to the async
definition. The seed already warns about this class at load time
("N function name(s) have co-compiled definitions across modules").

## Workaround (in tree)

The sync response module routes its internal callers through a uniquely
named `_serialize_sync_response`; the public `serialize_response` is a thin
wrapper. Marked `@workaround bug=seed_interp_cross_module_free_fn_collision_2026_11_06`.
`generate_error_page` (sync, 3 args) has the same collision with
`gc_async_mut/http_server/response.spl` (2 args) but is not on the lane's path.

## Fix owner

The seed interpreter should resolve free-function calls through the calling
module's import scope, as native codegen does. Remove the workaround once it
does.

## Related seed defect seen in the same session

In the seed's default JIT lane, `rt_host_dynlib_open(path: text, mode)` returns
0 for a valid DLL (the JIT passes the text value where the runtime symbol
expects `(ptr, len, mode)`), so every provider admission reports
`loader-failed`. `SIMPLE_EXECUTION_MODE=interpret` loads the same DLL and
returns level 4. Provider-admission work on the seed must use interpret mode.

## Resolution (2026-11-06)

Root cause was not name-keyed registration as such — both definitions were in
`FUNCTION_OVERLOADS` — but overload SCORING:

- `Value::matches_type` (`src/compiler_rust/compiler/src/value_impl.rs` ~779)
  matched a class name only for `Value::Object`. Reference classes are
  `Value::ClassInstance` (default since `SIMPLE_INTERP_CLASS_REF`), so every
  class-typed candidate (`HttpResponse`, `HttpResponseData`) failed to score,
  `select_overload` returned `None`, and the call fell through to Priority 5,
  the flat last-registration-wins map — the async `serialize_response`.
  It now matches `aggregate_class()` (Object or ClassInstance). The same
  Object-only match in the trait-impl fallback of `value_type_matches_name`
  (`interpreter_call/mod.rs`) was widened the same way.
- `interpreter_call/mod.rs` Priority 4: when no candidate scores (erased or
  untyped argument values), the calling module's OWN arity-compatible
  definition is now chosen before the flat-map fallback.

The workaround in `src/lib/nogc_sync_mut/http_server/response.spl`
(`_serialize_sync_response`) is removed. `generate_error_page` (3-arg sync vs
2-arg gc_async) was checked in the same probe and resolves correctly.

Evidence:
- Repro `test/fixtures/seed_interp/cross_module_fn/main.spl` (interpreter
  mode). Before (seed built from `ecb705896a4`): `error: semantic: undefined
  field 'reason': class RespA has no such field or getter`. After:
  `a_entry a:1` / `b_entry b:2!`.
- Real shape: a program importing the sync `serialize_response`,
  `bounded_response_wire`, `generate_error_page` while co-loading
  `std.nogc_async_mut.http_server.response` and
  `std.gc_async_mut.http_server.response`, with the workaround removed.
  Base seed: `error: semantic: invalid operation: cannot index value of type
  object`. Fixed seed: all three print `true`.
- Rust tests `interpreter_call::cross_module_free_fn_collision_tests::same_named_free_fn_resolves_to_the_calling_modules_definition`
  and `interpreter_call::class_typed_overload_scoring_tests::class_argument_selects_the_overload_typed_with_its_class`:
  both FAILED on the base code (`undefined field 'reason': class RespA ...`), ok after.
