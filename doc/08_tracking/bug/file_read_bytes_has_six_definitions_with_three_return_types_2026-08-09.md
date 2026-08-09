# `file_read_bytes` has six definitions across three incompatible return types

**Status:** OPEN
**Found:** 2026-08-09 — flagged by stream P6b as a co-compiled-definition warning
during the Vulkan DBG-1 work; widened by the coordinator on inspection
**Severity:** latent misdispatch — silently returns a differently-shaped value
**Component:** `src/lib/**` (six modules, listed below)

## Defect

`file_read_bytes(path: text)` is defined **six** times, with **three mutually
incompatible return types**:

| return type | module |
|---|---|
| `[u8]` | `src/lib/nogc_sync_mut/ffi/io.spl:42` |
| `[u8]` | `src/lib/nogc_sync_mut/sffi/io.spl:42` |
| `[u8]` | `src/lib/nogc_sync_mut/io_runtime.spl:140` (the only `pub` one) |
| `[i64]` | `src/lib/nogc_sync_mut/io/file_ops.spl:145` |
| `[i64]?` | `src/lib/nogc_sync_mut/file_system/file_ops.spl:34` |
| `[i64]?` | `src/lib/nogc_async_mut/file_system/file_ops.spl:34` |

P6b originally reported this as *two* co-compiled definitions differing as
`(text)->[i64]` vs `(text)->[u8]`, because that is what the toolchain warning
surfaced for the modules its run happened to load. The real spread is wider, and
the warning shows only the pair that collided in that particular closure — so
the visible warning **understates** the problem depending on which modules are
imported.

## Why it is dangerous

The three shapes are not interchangeable:

- `[u8]` vs `[i64]` differ in element width — a consumer indexing the result gets
  different values, not a type error, once dispatch picks the other definition.
- `[i64]?` is *optional* — a caller written against `[u8]` has no `nil` case at
  all, so the absence path silently disappears.

Which definition wins depends on the import closure of the compiling module.
That makes this a whole-program property: a module can start resolving to a
different `file_read_bytes` because some *unrelated* module was added to the
closure. Nothing at the call site changes.

This is the same hazard family as the other multi-implementation divergences
found on 2026-08-09 (`rt_time_now_nanos` two epochs). Here it is worse, because
the divergence is in the *type*, not just the value.

## Observed context

P6b saw the warning during `vulkan_debug_session_conformance_spec` and
`cuda_debug_session_conformance_spec`. It did **not** affect those runs' results,
which is exactly why it is filed rather than fixed in-stream — it is latent, and
converging six definitions is not a change to make inside an unrelated feature
stream.

## Fix

Converge on ONE definition. `io_runtime.spl:140` is the only `pub` one and
returns `[u8]`, which is the correct shape for raw bytes; the others should
either re-export it or be deleted. The `[i64]?` variants encode "may fail" —
if that is genuinely needed it belongs in a differently-named function
(`file_try_read_bytes`), not in an overload distinguished only by return type.

Note the standing repo caution: deleting a reimplementation **reroutes** callers
rather than deduplicating them. Check each caller's expected element width and
nil-handling before removing any definition.

## Oracle

`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1` prints the owner path of each colliding
definition and is the tool for confirming which pair a given closure resolves.
No spec currently asserts a single definition exists — that absence is why six
accumulated.
