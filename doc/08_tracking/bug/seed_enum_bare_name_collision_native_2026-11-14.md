# Seed native path resolves enums by bare name; two `HttpStatus` enums collide (2026-11-14)

Status: open (P1 — blocks `llm_caret` native build)

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
