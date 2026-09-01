# `file_read_bytes` has six definitions across three incompatible return types

> **SIGNATURES UNIFIED 2026-08-16.** The last `[i64]` definition
> (`src/lib/nogc_sync_mut/io/file_ops.spl`) now returns `[u8]` (canonical
> signature), and its raw i64 shape survives under the unique name
> `file_read_bytes_i64` (callers migrated: 10 `src/lib/scv/*` files +
> `src/compiler/80.driver/cache/cache_validator.spl`). All remaining
> co-compiled definitions are identical `(text)->[u8]`, so the
> differing-signature ambiguous-dispatch warning no longer fires (verified:
> spec-harness run shows zero `file_read_bytes` collision warnings). Full
> convergence to ONE definition (the guard spec's red example) remains open.

> **PARTIALLY FIXED 2026-08-09 (stream G2).** Six definitions → **four**. The
> dangerous `[i64]?` shape is **gone**: both were mocks returning a hardcoded
> `"Hello"` for every path, and both had zero importers. The remaining four are
> three identical `[u8]` and one `[i64]`. Full convergence onto the single `pub`
> definition was attempted, verified working, and then **reverted** because it
> hangs the compiler — see "Why full convergence was reverted". A guard spec is
> committed and is intentionally RED on the one assertion that tracks the
> remaining work.

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

## Resolution (2026-08-09, stream G2)

### A working-copy trap worth recording

The initial sweep of this repo's working copy found a **seventh** definition at
`src/app/io/file_ops.spl:139 -> [i64]` and it was nearly reported as a miss in
this bug. It is not: at `HEAD` that file is a three-line compatibility facade
(`export use std.nogc_sync_mut.io.file_ops.*`), and the 208-line version holding
the extra definition was another session's **uncommitted** work in a shared
working copy. Verified with `git grep -n "fn file_read_bytes" HEAD`, which
returns exactly the six rows above. The edit made to that file was reverted and
is not part of this change.

Lesson for anyone re-running this census: enumerate against `HEAD`, not the
working copy, and never edit a file another session is mid-flight on.

### Caller audit (done before any deletion)

| definition | return | importers naming `file_read_bytes` | disposition |
|---|---|---|---|
| `nogc_sync_mut/io_runtime.spl:140` | `[u8]` | 36 | **KEPT — canonical** |
| `nogc_sync_mut/sffi/io.spl:42` | `[u8]` | 39 | re-export |
| `nogc_sync_mut/ffi/io.spl:42` | `[u8]` | 23 | re-export |
| `nogc_sync_mut/io/file_ops.spl:145` | `[i64]` | 15 | **left as-is** (see below) |
| `nogc_sync_mut/file_system/file_ops.spl:34` | `[i64]?` | 0 | **deleted** |
| `nogc_async_mut/file_system/file_ops.spl:34` | `[i64]?` | 0 | **deleted** |

Only the two zero-importer `[i64]?` mocks were removed, plus their
`file_system/__init__.spl` barrel exports. Nothing else changed.

### The `[i64]?` variants were MOCKS

Both returned a hardcoded `Some([72, 101, 108, 108, 111])` — `"Hello"` — for
every path, and both were re-exported by their `file_system/__init__.spl`
barrels. Had a closure resolved to one, every file read in that program would
have silently returned `"Hello"` instead of failing. No caller wanted them; no
`file_try_read_bytes` was needed, so none was added.

### Why full convergence was reverted

Full convergence WAS implemented and verified working — one definition repo-wide,
guard spec green (`executed=5 passed=5`), sabotage red (`passed=3 failed=2`).

It was then reverted because subsequent runs began failing as
`ERROR: test daemon timed out` with **no verdict line**, and I could not obtain a
trustworthy measurement to confirm the converged tree was sound. Two convergence
variants were tried (re-export from the non-canonical modules; and deleting the
`io/file_ops.spl` definition while repointing all 15 importers directly) and both
timed out.

**The cause is NOT established.** Crucially, the timeout also reproduced after
reverting every source change except the two zero-importer mock deletions — so it
is not explained by the convergence edits. The host was concurrently running
`kill_simple_monitor.shs`, `earlyoom` configured to preferentially kill `simple`
processes, and several `simple_lsp_mcp` servers, any of which can stall or kill a
compile. Details and the next step are in
`doc/08_tracking/bug/importing_io_runtime_into_io_file_ops_closure_hangs_compiler_2026-08-09.md`.

The revert is therefore a **measurement-driven pause, not a verdict on the fix**.
Retry the convergence on a quiet machine; the diff is straightforward and is
described in full above and below.

### The `[i64]` annotation is a lie, and the callers prove it

`io/file_ops.spl` declared `-> [i64]` for the *same* runtime call `io_runtime`
declares as `-> [u8]`. Downstream, `src/lib/scv/**` wrapped nearly every result
in `scv_i64_bytes_to_u8` and `cache_validator.spl` in `cache_i64_slice_to_u8` —
both of which are pure `& 0xFF` masks, i.e. **no-ops if the elements are already
bytes**. Decisively, several sites in the very same package (`store.spl`
`scv_content_id_for_file`, `parser.spl`, `parser_registry.spl`) never masked at
all and were not broken — so the elements were always bytes and `[u8]` is the
correct shape.

That cleanup (deleting the identity `scv_i64_bytes_to_u8` across 25 call sites,
and narrowing `cache_i64_slice_to_u8` to `[u8]` while keeping its offset/count
slicing and bounds check) was implemented and then reverted with the rest — it
only makes sense once `io/file_ops.spl` actually yields `[u8]`. Redo it in the
same change that lands the convergence.

### Verification

Of what landed (the two mock deletions):

- `file_read_bytes_single_definition_spec.spl` — committed as the guard. Its
  `[i64]?` assertion PASSES (that shape is gone) and its positive/negative
  scanner controls PASS. Its "exactly one definition" assertion is **RED by
  design**, tracking the four definitions that remain. Not weakened.
- The oracle was proven able to fail: while the tree was fully converged, adding
  a second `-> [i64]?` definition moved it from `passed=5 failed=0` to
  `passed=3 failed=2`. It carries a positive control (a symbol that must be
  found) and a negative control (a symbol that must not be) to close the three
  ways a symbol sweep fails open in this repo.
- `file_byte_alias_spec.spl` (high-bit `[u8]` round-trip) — `passed=2`.
- `app/io/file_ops_bytes_spec.spl` — `passed=1`.

### Two PRE-EXISTING scv failures, ruled out as regressions

Running the `scv` byte specs against this change surfaced two failures. Both
were baselined by reverting these edits to `HEAD` and re-running, and both
reproduce identically at `HEAD`, so neither is caused by this change:

1. `src/lib/scv/integrity.spl` does not parse — `val Some(db) = db_opt` (line
   464) and `val Some(table) = table_opt` (line 468) are refutable patterns in a
   `val` binding, which the parser now rejects without a diverging `else:`. The
   file is unmodified at `HEAD`. This blocks compilation of every spec whose
   closure includes it.
2. `test/01_unit/lib/scv/fast_import_format_byte_text_spec.spl` fails
   `expected commit refs/heads/main\tÿ to equal commit refs/heads/main\t?` —
   `ÿ` is `0xFF`. `executed=1 passed=0 failed=1` **both** before and after.

Failure 2 is worth noting for the record: it is a byte-width defect in the same
area, and it did NOT change when the `& 0xFF` masking was removed, which is
additional evidence that the mask was a no-op and that `[u8]` is the right
shape. Both deserve their own bugs; neither was fixed here.

### Not fixed here

The **extern** `rt_file_read_bytes` is separately re-declared **47 times across
six different return types** (`[u8]`, `[u8]?`, `[i64]`, `[i64]?`, `List<i32>`,
`i64`). That is a wider defect of the same family and is not addressed by this
change — the wrapper is now single, but modules still disagree about what the
runtime symbol returns. Worth its own stream.

The sibling `rt_time_now_nanos` epoch divergence is filed separately at
`doc/08_tracking/bug/rt_time_now_nanos_interpreter_uses_wall_clock_epoch_2026-08-09.md`
(not fixed: `runtime_native.c:9124` marks that symbol as owned by another lane).
