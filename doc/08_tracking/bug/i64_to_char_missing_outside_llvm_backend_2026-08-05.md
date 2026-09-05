# `i64.to_char()` was implemented only in the LLVM backend — FIXED

**Status:** FIXED 2026-08-05 (T-07, x25519mlkem768_acceleration campaign)
**Component:** `src/compiler_rust/compiler/src/interpreter_method/primitives.rs`
**Attribution:** Rust bootstrap seed (`bin/simple` prints the seed warning
banner in this tree), not the self-hosted binary. `i64.to_char()`/`chr()` has
no `.spl` definition anywhere in the repo — it is a seed-only builtin, so this
was never a `.spl` (pure-Simple) defect.

## Symptom

`Url.request_target()` -> `_request_target_component()`
(`src/lib/gc_async_mut/gpu/browser_engine/net/entity/url_types.spl:44-48`)
calls `(byte: i64).to_char()`. On both runnable engines this raised:

```
semantic: method `to_char` not found on type `i64` (receiver value: 47)
```

(47 is `/`.) Consequence: the browser engine's HTTP/1.1 client
(`H1Client.request`) could not serialize a request line on either engine, so
no browser-engine client could complete a real HTTP request end-to-end.
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl`
was red for exactly this: `Results: 11 total, 6 passed, 5 failed`.

`.to_char()` is not a one-off call — anchored grep found ~20 other call sites
across `src/lib/gc_async_mut/http_client/types.spl`,
`src/lib/nogc_async_mut/http_client/types.spl`,
`src/lib/gc_async_mut/web/browser_session_runtime.spl`,
`browser_session_url.spl`, `src/os/apps/shell/shell_async_file.spl`,
`src/os/compositor/host_gui_event_router.spl`, `src/os/hosted/hosted_entry.spl`,
`src/os/kernel/loader/cpio_newc.spl`, `src/os/kernel/memory/vmm_copy.spl`,
`src/os/services/vfs/vfs_service.spl`, `src/os/services/wm/wm_codec.spl` — all
of them equally broken on the interpreter/JIT before this fix, none of it
specific to the browser engine.

## Root cause

`src/compiler_rust/compiler/src/codegen/llvm/{emitter.rs,functions.rs,
functions/calls.rs}` all already special-case
`matches!(method, "chr" | "to_char")` — the LLVM native-codegen (AOT) backend
treats them as synonyms. But the tree-walk interpreter's builtin int-method
dispatch, `handle_int_methods` in
`src/compiler_rust/compiler/src/interpreter_method/primitives.rs`, only
matched `"chr"`. An unmatched method falls through to
`bail_unknown_method!` (`interpreter/error_macros.rs`), which is what produces
the `"semantic: method ... not found"` message (a `CompileError::Semantic`
variant, not a parse-time semantic-analysis failure — the "semantic:" text is
just that variant's `Display` prefix; the error fires at call time, which is
why the message includes the runtime receiver value).

This same function is what both runnable engines hit: `bin/simple test`
(`SIMPLE_EXECUTION_MODE` unset) hard-defaults to the tree-walk interpreter for
spec execution, and `bin/simple run`'s Cranelift JIT falls back to this same
interpreted method-dispatch path at runtime for method calls it does not lower
natively — which is why both engines produced the byte-identical error text
including the same runtime receiver value (47).

## Fix

One-line alias, in the existing `match` arm (no new builtin surface, no call
site changes — checked first per T-07's own guidance: since `to_char` already
has ~20 other callers repo-wide, rewriting call sites was the wrong option):

```rust
"chr" | "to_char" => { ... }   // was: "chr" => { ... }
```

This is a seed-only fix (`src/compiler_rust/...`), not a `.spl` fix, because
`to_char`/`chr` are Rust-seed interpreter builtins with no pure-Simple
definition to patch — there is no `i64.spl` or equivalent stdlib file that
declares them.

## Verification

`h1_client_request_spec.spl`: `Results: 11 total, 6 passed, 5 failed` (before)
-> `Results: 11 total, 11 passed, 0 failed` (after), same seed binary
identity (`bin/simple --version` seed-warning banner), file hashes stamped
before/after the measurement showed no concurrent edits.

`test/02_integration/app/ui.web/browser_h1_loopback_e2e_spec.spl` gained a new
real-socket example, `"completes a full request through the browser's own
H1Client"`, driving `browser_h1_get` (real `H1Client.request` over a real
loopback TCP socket, server process spawned separately) and asserting
status 200 + body content, matching the existing `socket_http_get` examples'
rigor. This discharges the TODO the spec's own header carried since it was
written.

## Second, unrelated defect uncovered by this fix

Fixing `to_char` did not turn `h1_client_request_spec.spl` fully green by
itself (`11 total, 9 passed, 2 failed` after the `to_char` fix alone, up from
`6 passed, 5 failed`). The 2 remaining failures were never `to_char` failures
— baseline already showed one of them (`"decodes bounded complete chunks and
rejects malformed chunks"`) failing with `h1: invalid or oversized chunk`,
unrelated to `to_char`; the other
(`"serializes raw request headers once and preserves the body"`) *was* a
`to_char` failure at baseline, but after the `to_char` fix it failed
differently: the built request wire was missing its body entirely
(`to_end_with("\r\n\r\nok")` failed — no `ok` at the end).

Root cause, confirmed with a minimal probe
(`extern fn rt_bytes_to_text(data: [u8]) -> text; rt_bytes_to_text([111u8,
107u8])` returned `""`, not `"ok"`): `rt_bytes_to_text_fn` in
`src/compiler_rust/compiler/src/interpreter_extern/conversion.rs` matched only
`Value::Int(i)` when converting each array element to a byte. `[u8]` array
literals (`111u8`) evaluate to `Value::UInt { value, width }`, a distinct
variant (see `src/compiler_rust/compiler/src/value.rs`) — every element was
silently filtered out, so any `[u8]`-typed array (as opposed to `[i64]`)
always converted to `""`. `parse_chunked_body_bytes` in
`src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:713` calls
`rt_bytes_to_text(raw.slice(pos, line_end)).trim()` to read a chunk-size line
out of a `[u8]` body — same bug, same silent-empty-string failure, which is
why `h1_chunk_size_value("")` returned `-1` ("invalid or oversized chunk")
even for a well-formed chunk.

Fix: use the existing `Value::as_int()` helper
(`src/compiler_rust/compiler/src/value_impl.rs`), which already handles both
`Int` and `UInt` uniformly and is the established pattern elsewhere in the
codebase, instead of a manual `Value::Int`-only match.

## Downstream unblock

This unblocks the AC-9 `e2e_handshake` benchmark leg (owned separately by the
AC-9 benchmark lane, T-05) to the extent that it depends on a completing
browser-engine HTTP/1.1 client request. It does not by itself prove a full
TLS 1.3 handshake latency benchmark — that is T-05's own deliverable and
outside this task's scope.
