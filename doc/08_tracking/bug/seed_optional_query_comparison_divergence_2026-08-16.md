# Seed interpreter: `.?` operator yields value-or-nil, not bool; module-private `val` imports resolve inconsistently

- **Date**: 2026-08-16
- **Status**: PARTIAL FIX (Divergence A: 2 sites fixed in h1_client.spl, 43 total sites tree-wide remain; Divergence B: constant made pub; Divergence C: open)
- **Area**: compiler_rust (seed interpreter), lib/gc_async_mut/gpu/browser_engine
- **Related**: `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl` (TLS handshake guard), `src/lib/gc_async_mut/gpu/browser_engine/net/entity/request_types.spl` (BROWSER_MAX_RESOURCE_BYTES)

## Divergence A — `.?` operator semantic mismatch with self-hosted

**Seed behavior:** The `.?` optional-query operator yields the wrapped value if present, or `nil` if absent — not a boolean. This is semantically correct for optional chaining *values*, but becomes a trap when used in boolean comparisons.

Probe output from seed interpreter:
```
nil .? => nil
nil .? == false => false
filled .? => x         (where x is the wrapped value)
filled .? == true => false
filled .? == false => false
```

Therefore `x.? == false` **never fires** regardless of whether x is nil or filled. The self-hosted compiler correctly returns a `bool` (either `true` or `nil` has no `== false` overload).

**Impact:** At `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:279`, the TLS handshake was guarded by:
```
if conn.tls_conn.? == false:
  // establish TLS
```

Under the seed, `tls_conn.? == false` never fires. The guard is always skipped, so handshakes were never established. Even with a real TLS runtime linked, every HTTPS fetch died at "missing TLS connection" fallthrough — a runtime mystery until the seed divergence was identified.

**Fixed 2026-08-16 at 2 sites in h1_client.spl:**
- Line 279: changed to `== nil`
- Second site in `get_mock_registry`: changed from `.? + .unwrap()` (which failed semantic narrowing under seed) to optional `match`

**Census — 43 total sites tree-wide using `.? == false` / `.? == true`** (as of 2026-08-16):
```
src/app/interpreter/helpers/debug_spec.spl
src/compiler/50.mir/intrinsics.spl
src/compiler/60.mir_opt/mir_opt/mod.spl
src/compiler/70.backend/linker/macho_parser.spl
src/compiler/70.backend/linker/pe_parser.spl
src/compiler/85.mdsoc/construct_checker.spl
src/compiler/85.mdsoc/layer_checker.spl
src/compiler/90.tools/lint/_LintMain/config_and_model.spl
src/compiler/99.loader/module_resolver/resolution.spl
src/lib/common/io/types.spl
src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl (2 fixed, 0 remain)
src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl
src/lib/gc_async_mut/package/installer/backend_fpm.spl (appears 2x: gc_async_mut, nogc_async_mut, nogc_sync_mut versions)
src/lib/gc_async_mut/web/browser_session_loading.spl
src/lib/gc_async_mut/web/browser_session_runtime.spl
src/lib/nogc_async_mut/debug/formats/dwarf_parser.spl
src/lib/nogc_async_mut/debug/formats/test/.spipe_matchers_*.spl (6 test files)
src/lib/nogc_async_mut/package/installer/backend_fpm.spl
src/lib/nogc_sync_mut/debug/formats/dsym_resolver.spl
src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl
src/lib/nogc_sync_mut/debug/formats/test/.spipe_matchers_*.spl (6 test files)
src/lib/nogc_sync_mut/package/installer/backend_fpm.spl
src/lib/nogc_sync_mut/tooling/easy_fix/types.spl
src/os/compositor/host_compositor_core.spl
src/os/tools/log/log_viewer.spl
src/os/tools/pkg/pkg_resolver.spl
src/os/tools/proc/kill_tool.spl
src/os/tools/proc/nice_tool.spl
```

**Recommended fix:** Add a lint rule banning `.? == false` / `.? == true` patterns (since `.?` never yields a boolean under any compiler). Convert all 43 sites to `== nil` / `!= nil` for optional tests. Every unfixed site is a latent dead-guard under the seed.

## Divergence B — Module-private `val` imports bind to a non-int sentinel

`BROWSER_MAX_RESOURCE_BYTES` in `src/lib/gc_async_mut/gpu/browser_engine/net/entity/request_types.spl` was declared as `val` (non-exported, module-private). Despite this, two files imported and used it:
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/web/browser_session.spl`

The self-hosted compiler resolves it correctly. Under the seed interpreter, the first arithmetic using the constant dies with:
```
error: semantic: type mismatch: cannot convert array to int
```

The constant binds to an opaque sentinel value (likely an array representation), not an integer. This prevents any computation using the constant, breaking chunked-transfer decoding logic.

**Fixed 2026-08-16:** Made `BROWSER_MAX_RESOURCE_BYTES` a `pub val` in request_types.spl. The constant is now exported and resolvable by both consumers.

**Downstream failure:** The chunked-decode path still fails even with the constant properly exported. Investigation ongoing on the browser lane; the cause is not yet isolated.

**Recommendation:** Search for other cross-module imports of non-pub `val`s, particularly in browser_engine and adjacent libraries. Pattern to audit:
```
use ... (path to non-pub val constant)
```
in files that are not in the same module as the constant's definition.

## Divergence D — Reassigning a `var [u8]` loop accumulator via `+` dies with "cannot convert array to int"

**Seed behavior:** inside a `while` loop, `acc = acc + other_bytes` (both `[u8]`)
throws `error: semantic: type mismatch: cannot convert array to int` on the
first non-empty right-hand side. A standalone `[u8] + [u8]` concat outside this
loop/reassignment shape is fine, and the self-hosted compiler accepts the
original code — the failure is narrowly the reassign-accumulator-via-`+` idiom.

**Impact:** three sites in `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl`
(`parse_chunked_body_bytes`, `read_tcp_response_bytes`, `read_tls_response_bytes`)
— this was the last blocker for seed-run https fetches after the TLS delegates
landed, because example.com serves chunked transfer encoding.

**Fixed 2026-08-16 (workaround):** replaced each `x = x + y` with a per-byte
`for b in y: x = x.push(b)` loop — the same `[u8]` concat idiom already used in
`debug/formats/test` codeview/pdb/macho helpers, i.e. an established seed-safe
pattern, not a novel hack. Verified: chunked fixture parses and live
`https://example.com` loads (559 bytes) under the seed.

**Underlying seed bug:** open — pinpointed while writing the pinning test:
only the packed `Value::ByteArray` representation triggers it (bytes from
runtime externs like `rt_io_tcp_read`/`rt_bytes_alloc`); a `[u8]` array
LITERAL lowers to generic `Value::Array`, which has a dedicated
`Array + Array` concat arm in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs:680-684`.
`ByteArray + ByteArray` has no such arm and falls through to numeric
coercion (`src/compiler_rust/compiler/src/value_impl.rs:137`), producing the
"cannot convert array to int" error. Fix = add a ByteArray concat arm; then
revert the per-byte `.push()` workarounds and flip the pinning test.

**Pinning tests:**
`src/compiler_rust/compiler/tests/seed_semantic_divergences.rs` (divergences
A + D, asserts CURRENT seed behavior — a failure there means the bug got
fixed) and
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl`
(6 parse cases incl. the chunked regression, compiler-agnostic).

## Divergence C — Seed reports semantic errors with no position information

Both divergences A and B presented as runtime mysteries (nil pointer dereference, type mismatch with no source location) because the seed's semantic error reporting omits file and line number information.

Error format under seed:
```
error: semantic: <error message only>
```

Error format under self-hosted:
```
<file>:<line>:<col>: error: semantic: <error message>
```

This lack of context makes seed-vs-self-hosted discrepancies hard to localize. A semantic error can be traced only by runtime behavior (where it manifests), not by its origin.

**Diagnosability gap:** The seed should report error position on all semantic failures.

**Status:** Open; no immediate fix planned. Workaround: use the self-hosted compiler for debugging semantic errors, not the seed.

## Landing note (2026-08-16)

The two h1_client.spl guard fixes landed in the browser development lane. The BROWSER_MAX_RESOURCE_BYTES `pub val` change was made but downstream chunked-decode failure was not resolved as part of this investigation — that work remains open.
