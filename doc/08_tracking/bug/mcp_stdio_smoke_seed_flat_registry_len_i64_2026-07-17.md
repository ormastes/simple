# MCP stdio smoke: seed whole-program flat registry corrupts extract_id() when main_lazy_protocol.spl joins the import closure

**Date:** 2026-07-17
**Scope:** `src/app/mcp/main.spl` (`.spl` fix, DONE) + `src/compiler_rust` interpreter
(NOT fixed here — out of scope per task rules; seed-side).
**Severity:** high — blocks the MCP stdio smoke round-trip on the seed binaries
(`src/compiler_rust/target/release/simple` and `.../target/bootstrap/simple`).

## Symptom 1 (FIXED, pure Simple): `--stdio` flag rejected

`src/compiler_rust/target/release/simple run src/app/mcp/main.spl --stdio`
exited 1 with `[error] mcp: Unknown mcp option: --stdio`. `main()`'s arg
parser (`src/app/mcp/main.spl`, around line 402) only recognized `--help`,
`-h`, `help`, `--version`, `-v`, `--probe` — any other single arg (including
the common MCP-client convention flag `--stdio`) fell through to the
"Unknown mcp option" branch and returned 1. The documented, canonical
invocation (`.mcp.json`, `bin/simple_mcp_server`) always launches with zero
args — stdio framing is the server's only transport, so `--stdio` is
semantically a no-op.

**Fix:** changed the guard from `if args.len() > 0:` to
`if args.len() > 0 and args[0] != "--stdio":`, so `--stdio` now falls through
to the shared serve loop instead of erroring. Minimal, no duplicated logic.

## Symptom 2 (NOT FIXED — seed interpreter defect, out of scope): `extract_id()` corrupts to an `i64` when `main_lazy_protocol.spl` is in the closure

After the `--stdio` fix, the smoke test still exits 1, now with:

```
error: semantic: method `len` not found on type `i64` (receiver value: 4059709571969)
```

(the huge "receiver value" is a pointer-shaped number, not user data — this
is a type-tag/boxing corruption pattern, not a real integer).

Bisected with debug `_mcp_error` markers: the crash happens **inside**
`_mcp_extract_id(msg, "initialize")` — specifically inside
`extract_id`/`extract_field_raw`/`_find_json_value_start` in
`main_lazy_json.spl`, on the very first `initialize` request, before any
response is ever produced. Confirmed identical on:
- `src/compiler_rust/target/release/simple` (interpret mode, default)
- `src/compiler_rust/target/release/simple` with `SIMPLE_EXECUTION_MODE=compile`
- `src/compiler_rust/target/bootstrap/simple`

### Minimal, deterministic repro

`extract_id()` (copied verbatim from `main_lazy_json.spl`, no changes) run
standalone on the exact same message succeeds (`id=1`, exit 0) — proving the
function's own logic is correct. Adding **one unrelated, unmodified sibling
import** to the same file flips the identical call into the crash above:

```simple
use std.io_runtime.{env_get, file_exists, exit, get_args}
use std.nogc_sync_mut.io.stderr_ops.{stderr_write, stderr_flush}
use .mcp_log_options
use std.mcp_sdk.server.method_detect.{has_method}
use .main_lazy_json
use .main_lazy_protocol   # <-- adding ONLY this line flips a working call into the crash

fn main() -> i64:
    val msg = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}"
    val id = extract_id(msg)   # clean (id=1) without the line above; crashes with it
    print "id={id}"
    0
```

`main_lazy_protocol.spl` is never called (`main()` above never invokes any of
its functions) — its mere presence in the whole-program import closure is
enough to corrupt an unrelated call elsewhere. Bisecting inside
`main_lazy_protocol.spl` (halves/quarters) narrowed the trigger to
`handle_resources_read`/`get_cwd`/`make_resource_content_response` together,
but no single-function isolation reliably reproduced it outside the full
file — consistent with whole-program registry-slot corruption rather than a
localized source bug (further narrowing not pursued, per task scope: seed
interpreter internals are out of scope for this lane).

### Why this looks like the same defect class as today's Wall-2/SDNVALUE fixes

`doc/08_tracking/bug/hir_stmt_expr_payload_extraction_nil_2026-07-17.md`
(same date, different lane) already root-caused and fixed **two** instances
of a shared mechanism this session: the interpreter's `classes`/`enums`
lookups are **global/flat across the whole loaded program**, not properly
scoped per module, so a same-named class/enum/function anywhere in the
transitive closure can silently shadow or hijack resolution for a call site
that never intended to reference it (`use_bare_module_fallback` missing
`receiver_is_enum`; `handle_constructor_methods` missing an enum-variant
fallback). This repo's MCP/LSP tree has **dozens** of sibling modules
independently defining identically-named private JSON helpers (`Q`, `LB`,
`RB`, `SB_L`, `SB_R`, `jp`, `js`, `jo1`..`jo4`, `escape_json`,
`extract_field`, `extract_field_raw`, `extract_id` — confirmed via
repo-wide grep across `src/app/mcp/`, `src/app/lsp_mcp/`, `src/app/mcpgdb/`,
`src/app/jupyter_kernel/`, `src/lib/*/mcp_sdk/`, `src/lib/*/lsp/`, etc.),
each file's header comment explicitly noting these are meant to be
**module-private, zero-import inlined copies** ("Local definitions (runtime
can't re-export imported symbols)" / "JSON helpers (inlined for zero-import
startup)"). If the seed's function registry is similarly flat/global (a
function-name analog of the already-fixed class/enum-name collision), this
is a strong candidate root cause: adding `main_lazy_protocol.spl` doesn't
introduce a *new* colliding name (its helper names are already duplicated in
`main_lazy_json.spl`), but it can plausibly perturb which same-named
definition "wins" the global slot, or shift internal ID/slot numbering enough
to corrupt an unrelated already-resolved call. Not independently proven at
the Rust level here (would require `src/compiler_rust` instrumentation,
explicitly out of scope for this lane) — flagged as the most likely
mechanism for whoever picks this up next.

**Tested and disproven, 2026-07-17 (same session, standalone-compile-sweep
follow-up):** replacing `main_lazy_protocol.spl`'s implicit/flat-namespace
reliance on `main_lazy_json.spl`'s helpers with **explicit**
`use .main_lazy_json.{make_json_result, make_error, extract_field,
escape_json, top_level_item_count, shell_cmd, _slice_text}` imports (plus a
`std.io_runtime.{file_read}` import and a latent `NL`→`_PROTO_NL` typo fix —
see
`mcp_main_lazy_json_standalone_compile_process_run_tuple_ambiguity_2026-07-17.md`
for the full changeset) does **not** fix this defect: the exact same
`error: semantic: method \`len\` not found on type \`i64\`` crash reproduces
identically on the smoke test after the explicit-import change, ruling out
"bare-identifier global-fallback resolution" (the exact Wall-2 mechanism) as
this particular defect's cause. Whatever perturbs the registry/slot
numbering here is triggered by something else about `main_lazy_protocol.spl`
joining the closure — not resolved by making its cross-file references
explicit. The explicit imports were kept anyway (they independently fix
`main_lazy_protocol.spl`'s standalone-compile gap, a real, separate
improvement) but this specific runtime defect remains open.

### Impact

Blocks the MCP stdio JSON-RPC round-trip (`initialize` → result) via
`src/compiler_rust/target/release/simple run src/app/mcp/main.spl` (with or
without `--stdio`), on both the release and bootstrap seed binaries. The
`.mcp.json`-registered production path (`bin/simple_mcp_server` →
`bin/release/<triple>/simple`, the self-hosted binary) is a **different**
artifact (compiled, not the interpreter-mode seed) and is not proven to share
this exact defect — separately known-stale per the redeploy wall (not this
bug).

### Status

Not fixed. Per task scope (`src/compiler_rust` is out of scope; "do not edit
Rust"), this is reported with a minimal, deterministic repro for whoever next
works the seed's flat-registry defect class (see the referenced doc's Wall-2
and SDNVALUE fixes for the two already-fixed sibling instances of this same
mechanism). The `--stdio` symptom (Symptom 1) is fixed in `main.spl`; the
underlying round-trip still cannot be verified end-to-end against the seed
binaries until Symptom 2 is resolved in `src/compiler_rust`.
