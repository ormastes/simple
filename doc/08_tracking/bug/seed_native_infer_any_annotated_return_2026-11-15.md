# Phase-1 seed native lowering infers ANY where the type is declared

Status: open

Native build of `src/app/cli/main.spl` with the phase-1 seed failed with
`hir: Unsupported feature: cannot infer field type while lowering <fn>: struct 'ANY' field '<f>'` at:

1. `val response = http_request(...)` (declared `-> HttpResponse`) then `response.status_code`
   — `compiler/90.tools/duplicate_check/ollama_client.spl` (check_ollama_available, get_embedding).
   Likely cause: two co-compiled `http_request` (io/http_client_core vs sffi/net) with different signatures.
2. `array_sort_by(xs: [MirFunction], \a, b: a.name ...)` — lambda params not inferred from `fn(T,T)->i64`
   — `compiler/90.tools/header_gen/mod.spl`.
3. `match subject: case Err(e): e.message` with `subject: FailSafeResult<T>` — `failsafe/core.spl`.

Workaround (tagged `@workaround bug=seed_native_infer_any_annotated_return_2026-11-15`): explicit
type annotations / typed named comparators. Fix belongs in the compiler's type inference.
