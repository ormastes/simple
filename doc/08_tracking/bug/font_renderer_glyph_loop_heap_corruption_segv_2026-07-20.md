# font_renderer: SIGSEGV in simple_runtime::value::heap after glyph layout, on the Rust seed's `run` evaluator

**Status:** OPEN 2026-07-20 — found while root-fixing the mutex crash in
`font_renderer_resolve_metrics_nil_receiver_seed_2026-07-20.md` (that mutex
bug's hard-crash half is mitigated on `bin/simple run`; this SIGSEGV is what
surfaced immediately behind it on that same `run`-based standalone repro).
**IMPORTANT SCOPE NOTE:** this bug was found and is reproducible **only via
`bin/simple run`** on a standalone script. It is **not confirmed** to be what
blocks the real `font_renderer_spec` under `bin/simple test` — that harness
uses a different evaluator and, per probe evidence in the sibling doc, dies
at an earlier and different call site (`validate_selected_font_asset`, not
the glyph layout loop this doc covers). Do not treat fixing this SIGSEGV as
sufficient to turn `font_renderer_spec` green; see
`font_renderer_resolve_metrics_nil_receiver_seed_2026-07-20.md` for the
actual `test`-path blocker.
**Severity:** Confirmed real Rust-seed runtime heap corruption (gdb-verified),
but its relevance to unblocking the tracked spec is unconfirmed pending the
above.
**Affected surface:** Rust seed only (`bin/simple` built from
`src/compiler_rust`, self-labeled "bootstrap seed only"), via `bin/simple run`.
Not yet evaluated on the pure-Simple self-hosted binary (none was deployed in
this worktree — see "Self-hosted timeout" below).
**Path:** `bug` track.

## Symptom

Minimal repro (seed `bin/simple run`, repo root):

```
use common.text_layout.font_renderer.{FontRenderer}
use std.nogc_sync_mut.sffi.io.{file_read_bytes}

fn main():
    val path = "assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf"
    val bytes = file_read_bytes(path)
    var renderer = FontRenderer.new()
    val ok = renderer.try_load_selected_bytes(path, bytes)   # ok = true
    val batch = renderer.prepare_text("A", 0xffffffffu32, 32)  # <-- SIGSEGV
```

`try_load_selected_bytes` succeeds (real 1.7MB NotoSansMono TTF, loads fine).
`prepare_text("A", ...)` — i.e. any call that reaches the glyph
layout/rasterize loop in `_prepare_text_active`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`) — crashes the process
with a raw SIGSEGV (exit 139), not a Simple-level runtime error.

`gdb -batch -ex run -ex bt` on the same repro:

```
Thread 2 "simple-main" received signal SIGSEGV, Segmentation fault.
...
#10 simple_runtime::value::heap::validate_heap_obj ()
#11 simple_runtime::value::heap::get_typed_ptr_mut ()
...
#22 rt_native_neq ()
...
#28 simple_runtime::value::heap::HEAP_ALLOCATION_REGISTRY ()
...
#35 __libc_calloc (...) at ./malloc/malloc.c:3754
```

Reached from a `!=`/`==` comparison (`rt_native_neq`) somewhere in the glyph
layout/rasterize path, hitting a heap object whose validation
(`validate_heap_obj`) faults — genuine heap corruption inside the Rust
runtime's value/heap subsystem, not a Simple-source nil check.

Identical backtrace signature (same functions, same call order) reproduces
whether or not `prepare_text("", ...)` (empty content, which returns before
the glyph loop) is called first — i.e. the corruption is not caused by the
now-fixed mutex bug and is not avoided by working around it.

## What it is not

- Not the mutex nil-receiver crash from
  `font_renderer_resolve_metrics_nil_receiver_seed_2026-07-20.md` (that one
  faulted at `Mutex.lock()`/`self._handle`, a clean Simple-level "field access
  on nil receiver" panic, immediately on the first call — fixed in this pass,
  see below). This SIGSEGV happens strictly *after* that call chain completes,
  deeper in `_prepare_text_active`'s layout/quad loop.
- Not the sibling `struct-in-array i64 field corruption` fix landed at
  `55cdbc5571397fd4d52bdf3ae0982bef7bc4d4cc` /
  `8699cca54b6...` (`fix(compiler): struct-in-array i64 fields shredded when
  array built via empty-[] literal + push`) — checked before filing this as a
  duplicate. That fix is in the **self-hosted compiler's** MIR lowering
  (`expr_dispatch.spl`/`mir_lowering_types.spl`), gated to the **native-build**
  backend, and is not an ancestor of this worktree's pinned commit
  (`git merge-base --is-ancestor 55cdbc55713 HEAD` = no). It cannot affect the
  **Rust seed's** own interpreter/runtime (`simple_runtime::value::heap`,
  `rt_native_neq`), which is a different, hand-written Rust implementation
  entirely. This bug reproduces purely on the Rust seed via `bin/simple run`,
  so that fix is out of scope here, not a duplicate.
- Not module-init-time eager `Mutex` allocation. Changing the three facade
  lock module vars in font_renderer.spl from eager `= mutex_new(0)` to lazy
  `= nil` (kept in this pass as a correctness improvement matching the
  file's own documented freestanding-init intent) does **not** change the
  SIGSEGV's presence or its backtrace signature — tried and gdb-confirmed
  identical before/after.

## Investigation notes (for whoever picks this up)

- An earlier draft of this doc hypothesized the trigger scales with overall
  loaded-module footprint, based on `prepare_text("", ...)` (skips this
  bug's glyph loop) crashing only when embedded in the full `std.spec`-based
  test-runner harness but not standalone. That observation is better
  explained by the sibling doc's finding: under `bin/simple test`, the
  process actually dies earlier and elsewhere (inside
  `validate_selected_font_asset`, before font loading even completes) —
  so the harness-embedded `prepare_text("", ...)` crash was never reaching
  this SIGSEGV's code path at all; it hit the *other* bug first. Treat the
  footprint-scaling idea as retracted, not confirmed.
- `rt_native_neq` is a generic native `!=` comparison hook, not
  font-specific; whatever value flows into it here is the actual corrupt
  object. Worth instrumenting `_prepare_text_active`'s loop
  (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:~1150+`) with
  narrow, single-field-read prints (see the file's own GLYPH-FIX-3/4/5
  comments for the established "read every field exactly once into a local,
  never re-read after an intervening call" idiom already used to fight this
  bug class) to find which specific `!=`/`==` comparison lands on the
  corrupt object.

## Self-hosted timeout (unverified in this pass)

The mission also names a self-hosted-binary 120s timeout on this spec. No
pure-Simple self-hosted `bin/simple` binary was available in this worktree
(only the Rust seed was deployed/copied in), so that failure mode was **not**
characterized here — scoping this bug doc to the seed SIGSEGV, the more
tractable and now-precisely-characterized half. Whoever has a self-hosted
binary deployed should check separately whether the self-hosted "hang" is
this same heap corruption manifesting as a stall instead of a fault, or an
unrelated superlinear-parse-class issue (a sibling lane already found one such
case unrelated to fonts — do not assume this is that same defect without
checking).

## Blocked tests

- `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`: only its first
  example ("rejects nil or stale rasterizers through is_current") reliably
  passes when run through the real `bin/simple test` harness; it prints `✓`
  and the run then aborts (0 passed / 1 failed at the file level) with no
  further `✓`/`✗` markers. **Correction (superseding an earlier draft of this
  doc):** probe-localized evidence in the sibling doc
  (`font_renderer_resolve_metrics_nil_receiver_seed_2026-07-20.md`, "Actual
  `bin/simple test` blocker" section) shows the real `test`-path crash is
  NOT this glyph-loop SIGSEGV — it happens earlier, inside
  `validate_selected_font_asset`, before `_prepare_text_active` (where this
  SIGSEGV lives) is ever reached. A regression example added and then
  removed during this pass proved its own body never executed under
  `bin/simple test` (crashed at font *loading*, one step before its first
  real assertion) — it provided no verification value and was reverted
  rather than left in with a misleading claim. The pre-existing "renders a
  selected face from owned bytes..." example (real glyph rasterize + sha256
  pixel check) is blocked by whichever of these two bugs is reached first on
  a given evaluator; on `bin/simple test` specifically, that is the
  `validate_selected_font_asset` crash, not this one.
