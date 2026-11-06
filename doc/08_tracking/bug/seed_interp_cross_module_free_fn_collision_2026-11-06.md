# Seed interpreter resolves same-named free functions process-wide

- **Id:** seed_interp_cross_module_free_fn_collision_2026_11_06
- **Found:** 2026-11-06, wiring the single-owner vector-parser lane into `src/app/simple_web_server/`.
- **Engine:** Rust seed, `SIMPLE_EXECUTION_MODE=interpret` (tree-walk interpreter).

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
