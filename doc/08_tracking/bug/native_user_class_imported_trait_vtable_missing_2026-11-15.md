# Native build: no vtable for a user class implementing an imported trait

- Status: open
- Severity: P1 (silent link stub -> segfault at first dynamic dispatch)
- Found: 2026-11-15, llm_caret `messaging/mcp_worker.spl` native exe exited 139
- Builder: Rust seed `native-build` (`SIMPLE_NATIVE_BUILD_RUST=1`), seed-tip of 2026-11-14

## Symptom

A class declared `class C with T:` where `T` is a trait imported from another
module (here `std.mcp_sdk.transport.transport.Transport`), passed as a `T`
value to a function compiled in a different module (`mcp_serve(t: Transport)`),
links with:

    Generating 1 stub functions for unresolved symbols...
    Unresolved symbol preview: __vtable__<module>__C__for__Transport

and the program segfaults (rc 139) on the first trait call. The owning
module's object references the vtable (`U __vtable__...`) but never defines
it. Std's own `StdioTransport`/`BufferTransport` (declared in the trait's own
module) do get `R __vtable__...` definitions.

## Minimal repro (entry module only)

```simple
use std.mcp_sdk.transport.transport.{Transport}
use std.mcp_sdk.server.app.{mcp_serve}

class Buf with Transport:
    closed: bool
    static fn new() -> Buf:
        Buf(closed: false)
    fn read_message() -> text?:
        nil
    fn write_message(msg: text):
        print "w {msg}"
    fn close():
        print "c"

fn main() -> i64:
    mcp_serve(Buf.new())
    0
```

Result: unresolved-symbol stub for `__vtable__..._Buf__for__Transport`, rc 139.
Contrast: the same class passed to a `serve(t: Transport)` defined in the SAME
module runs correctly (call is devirtualized, no vtable needed). `fn` vs `me`
receivers make no difference.

## Suspected site (unconfirmed)

`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs` ~2285: vtable
entries are pushed from `hir.impls` only; for this class no `vtable_impls`
entry appears to be produced (neither the trait_infos branch nor the
empty-slot fallback), while `native_project/compiler.rs` ~2035 still attaches
the vtable symbol to the `StructInit`. The link-time stub generator then
masks the missing definition as a runtime segfault.

## Workaround (tagged)

`src/app/llm_caret/messaging/mcp/protocol.spl`: `serve_messaging_stdio` mirrors
`mcp_serve` over the concrete `MessagingStdioTransport` (which no longer
declares `with Transport`), tagged
`WORKAROUND(native_user_class_imported_trait_vtable_missing_2026-11-15)`.
Restore `mcp_serve` once the codegen fix lands.

## Regression spec

`test/03_system/app/devhub/messenger/native_binary_messaging_mcp_worker_spec.spl`
(`LLM_CARET_MCP_WORKER_NATIVE_BIN=<exe>`).

## Open questions

- Other app classes `with <imported std trait>` passed to cross-module trait
  parameters are likely affected; a stub line in any native build log naming
  `__vtable__` is the signal.
- Is the stub generator right to stub data symbols (vtables) at all? Failing
  the link would have surfaced this at build time.
