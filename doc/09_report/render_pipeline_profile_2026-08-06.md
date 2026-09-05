# WM/render pipeline profile — measured stage breakdown (2026-08-06)

Lane PR0. Profile first, optimize the measured #1, prove the win on the same
fixture and engine.

## Measurement identity (read this before quoting any number)

| field | value |
|---|---|
| binary | `bin/release/x86_64-unknown-linux-gnu/simple` (what `bin/simple` resolves to) |
| binary md5 | `ed53cc5f255e269ca27c4cd83b17aef9` — the **Rust bootstrap seed** |
| engine | JIT requested; **actually the tree-walk interpreter** — see below |
| driver | `test/perf/wm_showcase/profile_stages.spl` |
| fixture | `WmShowcaseSession` at 480x480, 5 windows |
| CPU guard | `SIMPLE_TIMEOUT_SECONDS=0` (the 60s `kill_simple_monitor` cap kills this run at 154s otherwise) |

**No pure-Simple AOT number appears here and none can:** this tree has no
self-hosted binary, so every figure is seed-bound. Do not compare these to C
scalar baselines as if they measured the same thing.

## Finding 0 — the whole render lane runs INTERPRETED, and the cause is a CHAIN, not a bug

The dominant cost is not in any render stage. It is that no render stage is
compiled at all. The JIT reports **one blocker at a time and stops**, so the
causes surface serially — removing one just reveals the next. Measured chain,
in the order the JIT hit them:

| # | blocker | class | status |
|---|---|---|---|
| 1 | `_sorted_timer_stats` (`src/lib/nogc_sync_mut/diag.spl:385`) | lambda comparator | **fixed** |
| 2 | `Directory.list_paths` (`src/lib/nogc_sync_mut/fs/path.spl:264`) | `_` placeholder closure | **fixed** |
| 3 | `Directory.list_paths` (`src/lib/nogc_async_mut/fs/path.spl:264`) | same, **twin file** | **fixed** |
| 4 | `rt_port_inb` | unresolved extern | **NOT fixable here** |

Blocker 3 is the instructive one: `path.spl` exists twice (sync and async
tiers) with identical bodies. Fixing only the `nogc_sync_mut` copy left the
blocker live and the JIT reported the *same function name* again — which reads
exactly like "the fix didn't work" rather than "you fixed the wrong copy".

**The chain is not exhausted, and blocker 4 ends it for now.** `rt_port_inb`
is a bare-metal x86 port-I/O extern with **no definition anywhere in the C
runtime**; it is declared in `src/os/services/wm/wm_host_2d_simpleos.spl`, a
SimpleOS-only HAL module that is being co-compiled into the *hosted* WM path.
On Linux that symbol can never resolve, so that module — and its whole callee
tree — is permanently interpreter-bound. No amount of closure removal fixes it.

So: **the three closure fixes are real and verified, but they do NOT by
themselves make the render lane JIT-compiled, and no end-to-end speedup is
claimed from them.** What they do is remove three of the four known blockers
and reduce the problem to a single, precisely-named one.

### The underlying defect is the JIT closure ABI, not these four call sites

The compiler's own message states it: *"the JIT closure ABI does not tag-box
lambda arguments or results and is incompatible with the runtime's
RuntimeClosure layout"*. Any closure in any co-compiled module poisons that
module and its callee tree. The family is large — **412 lambda sites across
106 files** under `src/lib` + `src/os`, plus a separate `_`-placeholder form
(6 further real sites) that a lambda-shaped grep does not match, which is
exactly how blocker 2 hid. Rewriting 418 sites is not the fix; implementing
the closure ABI is. That work lives in `src/compiler_rust/**`, out of scope by
policy.

### Recommended next step for blocker 4 — and a correction

My first instinct was "stop importing the SimpleOS-only HAL into the hosted
build". **That is wrong and is recorded here so nobody spends a day on it:**
there is no importer. `git grep 'use .*wm_host_2d_simpleos'` returns nothing.
The module is pulled into the compilation unit by whole-workspace
co-compilation, not by any `use`, so there is no import edge to cut.

That makes blocker 4 structural rather than local. The two credible fixes are:

1. **Build-unit scoping** — the hosted lane should not co-compile
   `src/os/services/wm/*_simpleos.spl` at all. This is the real fix and it is
   a compiler/build change, not a WM change.
2. **A hosted stub for `rt_port_inb`** — cheap, but it makes an
   x86-port-I/O symbol resolvable on a hosted target, which is exactly the
   kind of thing that later reads as "hosted supports port I/O". If taken, it
   must trap loudly rather than return a plausible value.

Option 1 is the correct one. Neither is attempted here: both reach outside
this profile's lane, and option 1 in particular is the sort of build-graph
change that turns someone else's green build red mid-flight.

## Finding 0a — the original single-lambda write-up (superseded by the chain above)

The dominant cost was not in any render stage. It was that no render stage was
compiled at all.

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
Module error: function '_sorted_timer_stats' creates a lambda/closure; the JIT
closure ABI does not tag-box lambda arguments or results and is incompatible with
the runtime's RuntimeClosure layout, so JIT would return wrong values or crash;
deferring to interpreter
```

`src/lib/nogc_sync_mut/diag.spl:385` sorted timer stats with
`array_sort_by(stats, \a, b: b.total_ms - a.total_ms)`. That lambda makes the
function a closure; Cranelift refuses the **whole module**, and per the known
caller-module rule the entire **callee tree** drops with it. `diag.spl` is
co-compiled with the compositor/render path, so a diagnostics-only helper —
inert unless `SIMPLE_DIAG` is set — was silently interpreting the entire WM
render lane at roughly 10-1000x.

This is the same class as the recorded trap "a caller-module frame triggers
silent interpreted fallback of the whole callee tree", but the trigger here is
a lambda in a *disabled diagnostics* path, which is why nothing pointed at it.

### Fix

Replaced the lambda with an explicit insertion sort (no closure), and dropped
the now-unused `use std.array.{array_sort_by}`. Descending order verified
directly — inserted small/large/medium, summary printed large(44ms) /
medium(9ms) / small(0ms) — and the `[jit-fallback]` line is **absent** after
the change.

The replacement carries a comment saying it is deliberately not a duplicate
sort implementation, so a later "clean this up into the stdlib call" reverts
the fallback knowingly rather than by accident.

## Finding 1 — `[u32]` is not a packed pixel buffer; it is tagged 8-byte words

Probed directly against this binary via `rt_array_data_ptr` +
`rt_ptr_read_i64`. For `a: [u32] = [17,18,19,20,21,22]` the backing store reads:

```
word0=136 word1=144 word2=152 word3=160 word4=168 word5=176
```

which is exactly `value << 3` at an **8-byte stride**. Writing a tagged word
back through the pointer is visible in Simple (`a[0]` became 153 after writing
1224).

Consequences, both load-bearing for the redesign plan:

1. **A zero-copy packed span over `[u32]` is impossible as the type stands.**
   The gather/scatter around the SIMD kernels is not wrapper sloppiness to be
   optimized away — it is a representation conversion between tagged words and
   packed pixels. Any `Span`/`MutSpan` design must either target a genuinely
   packed container or own the conversion explicitly.
2. `rt_memcpy` and `rt_array_data_ptr` **are** registered in this binary
   (verified positively: a 32-byte copy moved 4 tagged slots and `dst[0]`
   matched), but a straight memcpy from a packed framebuffer into a `[u32]`
   would produce garbage, because the representations differ.

The runtime does already export a packed container family —
`rt_typed_words_u32_at` / `_set` / `_push` — which is the credible basis for a
packed span rather than `[u32]`.

## Finding 2 — per-pixel FFI in the readback path

`src/lib/common/ui/window_scene_draw_ir.spl:522-536`
(`shared_wm_pixel_buffer_pixels`) issues one `rt_ptr_read_i64` **per pixel** —
230,400 boundary crossings per readback at 480x480 — and its own comment at
line 182 asserts "only write_i32/read_i64 exist", which is stale:
`rt_ptr_read_i32` is declared elsewhere in `src/lib`.

This cannot be collapsed to a bulk copy today, for the reason in Finding 1: the
destination `[u32]` is tagged-word-encoded, so the copy needs a converting
runtime helper that does not exist. Adding one means a new C extern, which
needs a bootstrap rebuild the tree cannot currently perform. **Filed, not
fixed** — the honest blocker is the missing pure-Simple binary, not the C.

## Before / after — and why no win is claimed

Same driver, same fixture, same binary, runs serialised (nothing else of mine
on the CPU; the two persistent `simple_lsp_mcp` servers were present for both).

| stage | before (chain intact) | after (blockers 1-3 fixed) | delta |
|---|---|---|---|
| `session_start` | 378 ms | 351 ms | -7% |
| `open_index_0` (GUI window) | 107,657 ms | 99,189 ms | **-7.9%** |
| closure blockers reported | 1 (then next) | **0** | — |
| interpreter fallback | yes | **yes — `rt_port_inb`** | unchanged |

**The -7.9% is not claimed as a win.** n=1 per side, and both sides are still
interpreter-bound because blocker 4 survives, so the two runs differ only in
which modules got as far as attempting compilation. A single-run 8% delta on a
~100-second interpreted stage is not separable from run-to-run variance. The
result that *is* solid is the categorical one: **closure blockers went 1 -> 0
and stayed 0**, verified by grepping the compiler's own
`creates a lambda/closure` line across the full run.

The real prize is unclaimed and stays unclaimed: the ~10-1000x the compiler
itself predicts for escaping the interpreter is only available once blocker 4
goes too.

## Stage table

Numbers below are from the driver run; see the identity table above. The
`open_index_*` stages are single window opens.

| stage | ms | note |
|---|---|---|
| session_start | 351-672 | compositor construction |
| open_index_0 (GUI window) | 99,189 - 119,018 | **one window**, interpreted |
| open_index_2 (browser window) | **> 20 min, never completed** | see below |

The headline is the shape, not the digits: **a single window open dominates the
entire session by three orders of magnitude over every other stage.** Nothing
downstream — readback, checksum, distinct-colour counting, taskbar projection —
was reachable in any run, because the opens never finished.

`open_index_2` (the browser window) is worse than the GUI window by an unknown
factor: across three separate runs it never completed, the longest exceeding
20 minutes of wall clock. It is therefore the true #1 cost centre and is
**unmeasured**, not "slow" — I will not put a number on a stage I never saw
finish.

This is why the readback and per-pixel findings below, though real, are filed
rather than fixed: optimising a stage that has never once been reached in a
profiling run would be optimising by faith.

## Harness constraints discovered while building the driver

Recorded because each one silently produces a wrong or absent number:

- **Any field read on an imported struct inside the driver module** fails JIT
  type inference (`cannot infer field type while lowering main: struct
  'WmShowcaseWindowSpec' field 'kind'`), which drops the driver *and its callee
  tree* to the interpreter. The driver therefore iterates specs **by index with
  zero field reads**, and derives per-entry costs from whole-call timings.
- Under that interpreted fallback the run additionally died with `method
  '_flush_pending_compute' not found on type 'VulkanBackend'` — a **phantom**
  error: the method exists at
  `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:177` and is
  called from `backend_vulkan.spl`. The cross-file impl is not merged on that
  path. Worth its own bug if it recurs outside the fallback.
- Piping the driver through `grep | head` block-buffers stdout, so a long run
  shows nothing until exit; use `stdbuf -oL` when watching progress.
- The web window (spec index 1) is ordered **last** in the driver so the other
  stages are already on stdout before it risks exhausting the time budget.

## What was NOT done, and why

- **The measured #1 cost centre (`open_index_2`, browser window open) was not
  optimised.** It never completed in any profiling run, so there is no
  before-number to improve on and no way to prove an after-number. Naming it as
  the top bottleneck is the deliverable; guessing at a fix is not.
- **The per-pixel readback (Finding 2) was not fixed.** The bulk-copy route is
  closed by Finding 1 (tagged-word representation) and would need a new C
  extern, which needs a bootstrap rebuild this tree cannot do.
- **No SIMD, damage, or backing-store work.** All of it is downstream of stages
  that never execute.

## Verification

| claim | evidence |
|---|---|
| insertion sort still orders descending | `diag_spec.spl`: `Results: 15 total, 15 passed, 0 failed` |
| that example is not vacuous | sabotage (`while j >= 0 and false`) → `✗ orders summary lines by total_ms descending`, `15 total, 14 passed, 1 failed` — exactly one, no collateral |
| closure blockers eliminated | `creates a lambda/closure` count across the full run: 1 → **0** |
| lane still interpreted | `[jit-fallback] unresolved external symbol 'rt_port_inb'` still present |

The pre-existing spec at `diag_spec.spl:167` ("sorted-by-total path") asserted
only that both labels *appear*, so it stayed green with the sort deleted
outright. The added example pins the order and inserts the labels in the
opposite order to the expected output, so a no-op sort fails it.

## Files

- `test/perf/wm_showcase/profile_stages.spl` — the stage driver (new)
- `src/lib/nogc_sync_mut/diag.spl` — closure removed from `_sorted_timer_stats`
- `src/lib/nogc_sync_mut/fs/path.spl` — closure removed from `Directory.list_paths`
- `src/lib/nogc_async_mut/fs/path.spl` — same fix, twin file
- `test/01_unit/lib/nogc_sync_mut/diag_spec.spl` — order assertion + anti-vacuity guard
