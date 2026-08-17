# `me`-method mutation through an OPTION-typed binding is silently discarded

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

**Date:** 2026-08-04
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
destructuring; the workaround is applied in `engine2d/engine.spl`.
**Severity:** High — silent, exit 0, no warning from the compiler or runtime.
Every state change a mutating method makes is thrown away. Since 2026-08-04 a
lint rule (`OPTME001`, WARNING) flags the shape at authoring time; the
language/runtime defect itself is unchanged and still OPEN.

## Symptom

Calling a `me` (mutating) method on a binding whose static type is `T?` mutates a
temporary unwrap that is then discarded. The binding — and anything re-wrapped
from it — keeps the pre-call value. Calling the *same* method on a binding
produced by `if val Some(x) = opt:` writes back correctly.

## Minimal reproducer

`optwb_probe.spl` (scratchpad), `SIMPLE_EXECUTION_MODE=interpreter bin/simple run`:

```
class Counter:
    var n: i64 = 0
    me bump():
        self.n = self.n + 1

# Arm A -- optional-typed binding
var oa: Counter? = Some(Counter(n: 0))
val a = oa
if a == nil:
    print("A nil")
else:
    val ca = a          # ca : Counter?  <-- the defect
    ca.bump()
    ca.bump()
    oa = Some(ca)

# Arm B -- destructured Some binding
var ob: Counter? = Some(Counter(n: 0))
if val Some(cb) = ob:
    cb.bump()
    cb.bump()
    ob = Some(cb)
```

Observed:

```
A n=0     <-- both mutations lost
B n=2
C n=2     (C = same as B with a nested `me` call; nesting is fine)
```

Expected `A n=2`. The call is accepted by the compiler with no error and no
warning. (`lint` flagged nothing either until `OPTME001` landed on 2026-08-04 —
see the lint-backstop section below.)

## Why it matters

This is not a toy. It silently broke the Vulkan engine2d run lane for weeks —
see `run_lane_render_truncation_divergence_2026-08-02.md`. The font route was
written as

```
val active = self.vulkan_backend        # VulkanBackend?
if active == nil: ...
else:
    val vulkan = active                 # still VulkanBackend?
    var evidence = vulkan.composite_font_batch(x, y, batch)
    self.vulkan_backend = Some(vulkan)  # re-wraps the UNMUTATED value
```

so the entry flush inside `composite_font_batch` — which submits and clears the
pending compute batch — never reached the backend the engine kept. The stored
backend went on re-submitting an already-consumed command buffer, returning
`rc=-1` for every later flush and primitive dispatch, and the failure flags set
on the discarded copy never reached the readback, which published a truncated
frame as a proven `device_readback`.

## The two idioms are visually near-identical

`val x = <optional>` and `if val Some(x) = <optional>` differ by six characters
and read the same; only the second writes back. In `engine2d/engine.spl` both
appeared in the same `for target in plan:` loop, one per backend.

## Which idioms lose the write-back (measured, not assumed)

Probed with `SIMPLE_EXECUTION_MODE=interpreter bin/simple run` on
`optwb_probe{2,3,4}.spl` (scratchpad). A `Counter?` is bumped twice; `n=2` is
correct, `n=0` means both mutations were discarded.

| arm | idiom | n | verdict |
|-----|-------|---|---------|
| A | `val x = <T? expr>` then `x.bump()` | **0** | **BROKEN** |
| G | `var x = <T? expr>` then `x.bump()` | **0** | **BROKEN** (`var` is no safer) |
| H | as A, and never re-stored | **0** | **BROKEN** — the loss is total, not just the re-wrap |
| K | `if o.?:` then `o.bump()` directly | **0** | **BROKEN** |
| L | `if o != nil:` then `o.bump()` directly | **0** | **BROKEN** |
| M | alias + mutate + re-store through a `me` setter | **0** | **BROKEN** |
| B | `if val Some(x) = o:` | 2 | OK |
| I | `if val Some(x) = obj.field:` | 2 | OK |
| D/E | `var x = o.?` / `val x = o.?` | 2 | **OK — explicit unwrap is safe** |
| F | `var x = self.fld.?` | 2 | OK |
| J | `var x = f()?` (try-operator on a `T?`-returning call) | 2 | **OK — safe** |
| N | `self.<non-optional field>.me_method()` | 2 | OK — defect is specific to OPTION receivers |

Two consequences that change the earlier triage in this file:

1. **`.?` and `?` unwraps are safe.** The `engine3d/engine.spl` rows previously
   listed as OPEN at lines 190/207/215/414 all read
   `var vulkan = active.?` — those are **not** defective. This file previously
   over-claimed them.
2. **Re-storing does not rescue the mutation** (arm H/M). The write-back is lost
   at the call, so "it re-stores afterwards" is not a reason to call a site benign.

## Repo-wide enumeration (2026-08-04)

Method: a scratchpad static scan of all 14,034 owned `.spl` files (vendored
paths excluded). It resolves the *declared class* of every option-typed field
(`fld: C?`, both the `var fld: C?` and the bare `fld: C?` forms) and of
`T?`-returning functions, tracks locals bound to those (including alias chains
and `.?`/`?` unwraps), and reports a call `local.m(...)` only when `m` is
declared `me` **on that same class `C`**. Class scope includes `class`/`struct`/
`actor`/`object` **and** `impl C:` / `impl Trait for C:` blocks.

Resolving the method against the field's declared class is what makes the count
defensible — it removes the name-collision false positives that a bare
`grep 'me <name>'` would produce.

**69 candidate sites / 16 files.** Triage:

| class | count | meaning |
|-------|-------|---------|
| (a) broken | **24** | option-typed binding + genuinely mutating `me` call |
| (b) benign | **35** | safe `.?`/`?` unwrap (26), safe try-operator in `database/bug.spl` (6), read-only or discarded-copy (3) |
| (c) uncertain | **10** | `me`-declared but no observed self-write (`display_service` gpu cmd_*, `wm_access_cli` UiAccessStore) |

### Class (a) — fixed and verified in this sweep (10)

| file:line | binding | mutating call |
|-----------|---------|---------------|
| `src/lib/nogc_sync_mut/database/vector/store.spl:172` | `entries_table` (`SdnTable?`) | `mark_deleted` — **silent data loss, no write-back at all** |
| `src/lib/nogc_async_mut/http_server/server.spl:235` | `w` ← `last_worker` | `Worker.run` |
| `src/os/services/display/display_service.spl:206` | `fb_ref` ← `self.fb` | `FramebufferDriver.swap_buffers` |
| `src/app/play/wm_daemon.spl:223` | `handle` (`HostWmHandle?`) | `run_once` (in the frame loop) |
| `src/app/ui.tui/async_app.spl:60` | `handle` | `tick_forever` |
| `src/app/ui.tui_web/app.spl:40` | `handle` | `tick_forever` |
| `src/app/ui.electron/async_app.spl:51` | `handle` | `tick_forever` |
| `src/app/ui.tauri/async_app.spl:52` | `handle` | `tick_forever` |
| `src/app/ui.browser/app.spl:355` | `handle` | `tick_forever` |
| `src/lib/gc_async_mut/gpu/engine3d/engine.spl:357` | `fonts` ← `self._font_renderer` | `FontRenderer.clear_ttf` |

The `store.spl` row is the one with a proven user-visible consequence:
`VectorDatabase.delete()` never marked the metadata row deleted. Measured
before/after with the real API (`vecdel_probe.spl`):

```
pre-fix :  after delete valid=Option::Some(1)       <-- soft delete LOST
post-fix:  after delete valid=Option::Some(false)
```

Regression test added: `test/01_unit/lib/database/vector_delete_writeback_spec.spl`.

### Class (a) — left for the backend owners (14, all `engine2d/engine.spl`)

Not edited here: none of these backends initialize on this host, so an edit
could not be verified, and an unverified change to a GPU dispatch path is worse
than a filed defect. Each is `val active = self.<X>_backend` → `val <x> = active`
→ mutating call.

| line | binding | class | mutating call |
|------|---------|-------|---------------|
| 296  | `cuda`   | `CudaBackend`   | `install_font_atlas_ptx` |
| 1426 | `cuda`   | `CudaBackend`   | `draw_font_batch` |
| 1439 | `metal`  | `MetalBackend`  | `draw_font_batch` |
| 1450 | `opencl` | `OpenClBackend` | `draw_font_batch` |
| 1500 | `rocm`   | `RocmBackend`   | `draw_font_batch` |
| 1689 | `cuda`   | `CudaBackend`   | `invalidate_font_atlas` |
| 1694 | `opencl` | `OpenClBackend` | `invalidate_font_atlas` |
| 1699 | `metal`  | `MetalBackend`  | `invalidate_font_atlas` |
| 1704 | `rocm`   | `RocmBackend`   | `invalidate_font_atlas` |
| 1754 | `cuda`   | `CudaBackend`   | `invalidate_font_atlas` |
| 1759 | `opencl` | `OpenClBackend` | `invalidate_font_atlas` |
| 1764 | `metal`  | `MetalBackend`  | `invalidate_font_atlas` |
| 1769 | `rocm`   | `RocmBackend`   | `invalidate_font_atlas` |
| 2374 | `metal`  | `MetalBackend`  | `draw_image_blend_checked` |

Fix shape for each (already applied to the vulkan rows):
`if val Some(<x>) = self.<X>_backend:` … `self.<X>_backend = Some(<x>)`.

### Class (c) — uncertain, needs an owner call (10)

`me`-declared but the scan saw no direct `self.<f> = …` write, so it could not
prove a lost mutation. Left alone rather than blind-edited.

- `src/os/services/display/display_service.spl:126,133,172,178,201,222` —
  `gpu_ref` ← `self.gpu` (`VirtioGpuDriver?`), `cmd_resource_create_2d`,
  `cmd_resource_attach_backing`, `cmd_resource_detach_backing`,
  `cmd_resource_unref`, `flush_rect`, `cmd_set_scanout`. These forward to
  `virtio_gpu_*` free functions taking `self`; whether they mutate driver state
  (fence/ring cursors) needs a virtio owner. If they do, all six are class (a).
- `src/app/play/wm_access_cli.spl:251,254,262,265` — `store` (`UiAccessStore?`),
  `close` / `insert_event`.

### Scan error modes (stated honestly)

- **False negatives.** Option-typedness reached through a generic, a trait
  return, a tuple/`match` destructure, a multi-line binding, or a field whose
  type is a type alias is not resolved. Cross-file `T?`-returning functions are
  only used when the name resolves to exactly one return type repo-wide.
  Two real false-negative classes were found and fixed during this sweep (bare
  `fld: C?` field declarations, and `impl C:` method blocks); a third class may
  well remain.
- **False positives.** `mutates` is a heuristic (`self.x =`, indexed store,
  nested `me` call on self, or a mutating call on an own field). It under-reports
  — `wm_daemon`'s `run_once` mutates only via `self.compositor.render_frame()`
  and was scored `False`; it was reclassified to (a) by hand. So class (c) is
  "unproven", not "safe".
- Every class (a) row above was read in source and hand-confirmed; the counts
  are not raw scanner output.

## Superseded triage below (kept for history)

## Remaining occurrences of the losing idiom

`val active = self.<optional>` followed by `val y = active` and a mutating call:

| file:line | binding | mutating call | status |
|-----------|---------|---------------|--------|
| engine2d/engine.spl:282 | vulkan | `install_font_atlas_pipeline` | FIXED 2026-08-04 |
| engine2d/engine.spl:~1455 | vulkan | `composite_font_batch` | FIXED 2026-08-04 |
| engine2d/engine.spl:~2353 | vulkan | `draw_image_blend_checked` | FIXED 2026-08-04 |
| engine2d/engine.spl:292 | cuda | `install_font_atlas_ptx` | OPEN |
| engine2d/engine.spl:527 | metal | (font install) | OPEN |
| engine2d/engine.spl:~1421/1434/1445/1488 | cuda/metal/opencl/rocm | `draw_font_batch` | OPEN |
| engine2d/engine.spl:~2363 | metal | `draw_image_blend_checked` | OPEN |
| engine3d/engine.spl:91,190,207,215,355,414 | `_font_renderer` / `_vulkan_font` | various | OPEN |

`engine2d/engine.spl:498` uses the same idiom but only *reads*
(`parent.owns_session`), so it is unaffected.

The non-vulkan rows are left open deliberately: none of those backends
initialize on this host, so a change to them could not be verified here, and an
unverified edit to a GPU dispatch path is worse than a filed defect.

## Fix direction

1. **Language/compiler (real fix).** Either reject a `me`-method call on an
   optional-typed receiver at type-check time (forcing `.?` or a destructure),
   or make the implicit unwrap write the mutated value back through the
   binding. Silent acceptance is the defect.
2. **Lint backstop (cheap, do this regardless).** DONE — landed as `OPTME001`,
   see the section above. A rule that flags a mutating
   method call whose receiver's static type is `T?` would have caught every row
   in the table above at authoring time.

## Lint backstop — LANDED as OPTME001 (2026-08-04)

**This class is now guarded by a lint rule.** The language/runtime defect itself
is still OPEN (fix direction 1 below is unchanged); what closed is the "silent,
no lint" half of the severity line — an author who writes the losing idiom now
gets a warning at the call site.

| | |
|---|---|
| rule id | `OPTME001` (WARNING, category Correctness) |
| rule | `src/compiler/35.semantics/lint/option_me_call.spl` |
| spec | `test/01_unit/compiler/lint/option_me_call_spec.spl` — `Results: 15 total, 15 passed, 0 failed` |
| per-file lint | wired into `lint_cli_source`, so `bin/simple lint <file>` emits it |
| repo-wide census | `src/app/optme_lint/optme_scan.spl` (same rule fn, cross-file index) |

Message: ``` `<m>` is a `me` (mutating) method but `<recv>` is `<C>?`; the
mutation is applied to a discarded temporary and is lost ``` — hint spells out
the destructure, and states that a plain alias, a `!= nil` test and a `.?`
existence test are NOT unwraps.

WARNING and not DENY on purpose: the 14 engine2d backend sites below are
deliberately unfixed, so a deny-level rule would fail the build on day one.

### What the rule needed, and what `lint` actually had

The recommendation below assumed `lint` knows the receiver's static type. **It
does not, for this type shape.** The arena AST's flat type-tag lane cannot
represent `Optional<NamedClass>`: `parser_absorb_optional_suffix`
(`src/compiler/10.frontend/core/parser.spl`) collapses `CudaBackend?` to bare
`TYPE_OPTION` (14) and there is no `TYPE_OPTION_<named>` encoding, so
`decl_get_field_types` can say *optional* but never *optional of what* — which
is the half the rule turns on. The other half **is** in the AST
(`decl_get_is_async` doubles as the method mode: 0=fn, 1=static, 2=me), but the
`me` method is usually declared in a DIFFERENT file from the call and `lint` is
single-file. So the rule reads the declaration TEXT (which spells the class out)
and takes its index as a parameter. No type-inference pass was added; the rule
is still one call site, one receiver type, one declaration lookup.

### Measured yield: 36 warnings / 8 files

Repo-wide run over 14,027 owned `.spl` files (16,214 `me` methods and 297
option-typed fields indexed):

| count | file |
|-------|------|
| 14 | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` |
| 6 | `src/os/services/display/display_service.spl` |
| 5 | `src/os/services/vfs/vfs_service.spl` |
| 4 | `src/app/play/wm_access_cli.spl` |
| 2 | `src/compiler/40.mono/monomorphize/hot_reload.spl` |
| 2 | `src/lib/nogc_sync_mut/database/test_extended/runs.spl` |
| 2 | `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` |
| 1 | `src/lib/gc_async_mut/gpu/browser_engine/js/interpreter.spl` |

Reconciled against the enumeration above: the **10** class-(a) rows this sweep
already fixed are correctly ABSENT (they now read `if val Some(x) =`); all
**14** class-(a) rows left for the backend owners are present; all **10**
class-(c) rows are present (`display_service` line 222 in the table above is the
binding — the rule reports the call, at 225). The remaining **12** are sites the
scratchpad scanner MISSED: `vfs_service` ×5, `hot_reload` ×2, `runs.spl` ×2,
`font_renderer` ×2, `browser_engine/js/interpreter` ×1. 14 + 10 + 12 = 36.

None of the 36 were fixed by this change — the rule reports, it does not edit.

### Known gaps in the rule (stated, not hidden)

- Multi-line bindings, tuple/`match` destructures, generic and trait-returning
  receivers, and type-alias fields are not resolved (false negatives).
- A direct `self.<optional field>.mutate()` with no intermediate local is not
  flagged; only bindings are tracked.
- `OPTME001` is not registered in `all_lint_names()`, so it is not suppressible
  from `simple.sdn` (unknown codes are kept and default to Warn).

## Lint recommendation (evidence-backed, written before the rule landed)

**Recommendation: yes, add a rule — and it is cheap.** The scratchpad scanner
that produced the enumeration above is the detector, and it needed only three
facts, all already available to `lint` (which resolves types far better than a
regex scan):

1. the static type of the receiver binding is `T?`;
2. the called method is declared `me` on `T`;
3. the binding was *not* produced by `if val Some(x) =`, `.?`, or `?`.

Rule sketch — `SPL_OPT_ME_CALL`, warn (not error, to avoid blocking on the
class-(c) unknowns):

```
for each method call `recv.m(...)`:
    t = static_type(recv)
    if t is Optional(C) and m is declared `me` on C:
        emit warn at recv:
          "`{m}` is a `me` (mutating) method but `{recv}` is `{C}?`; the
           mutation is applied to a discarded temporary. Use
           `if val Some(x) = {recv}:` (or `{recv}.?`) and write the value back."
```

Precision evidence from the scan: over 14,034 files it produced **69**
candidates, of which 24 are true positives — and the entire false-positive
population came from the scanner's *lack* of a type checker (it could not see
that `.?`/`?` had already unwrapped, and it guessed at `mutates`). A rule inside
`lint`, which knows the real static type, would drop the `.?`/`?` false
positives outright and needs no `mutates` heuristic at all — `me` in the
declaration *is* the mutation signal. Expected output: on the order of 25-40
warnings repo-wide, i.e. a reviewable one-time cleanup, not a flood.

Cost is low and bounded: it is one predicate in the existing method-call
type-check path, not a new framework. Precedent for an in-repo targeted scanner
already exists at `src/app/gpu_lint/gpu_runnable_scan.spl`, so a standalone
scanner is also viable if wiring into `lint` proper is awkward — but `lint` is
the better home because only it has the receiver's static type, which is the
whole signal.

**Do not build this as a general dataflow framework.** The rule is purely local:
one call site, one receiver type, one declaration lookup.

## Re-verification 2026-08-09

Status confirmed **ARCHITECTURAL-OPEN** (compiler/language defect; the
`OPTME001` lint backstop is the shippable mitigation already landed).

Spot-checked the class-(c) "uncertain" rows this pass, since they looked like
the cheapest remaining win:

- `src/os/services/display/display_service.spl:124-225` (`gpu_ref` ←
  `self.gpu`, calls like `cmd_resource_create_2d`/`flush_rect`/etc.): these
  resolve via UFCS to **free functions** in
  `src/os/drivers/virtio/virtio_gpu_ops.spl` (`fn virtio_gpu_cmd_resource_create_2d(drv: VirtioGpuDriver, ...)`),
  not `me` methods — `OPTME001`'s scan correctly can't classify them as (a),
  because they aren't the shape either the rule or this defect targets.
  Whether mutation is lost here depends on whether `VirtioGpuDriver` (`struct
  VirtioGpuDriver` in `virtio_gpu.spl:154`) is value or reference under
  UFCS-through-`Option`, which is a *different* open question from the
  `me`-on-`T?` defect this doc tracks — conflating the two would be a guess,
  not a fix, so left alone per the doc's own no-blind-edit rule.
- No safe, verifiable subset of the remaining class (a)/(c) rows was found
  this pass: all require either GPU hardware this host lacks, or an owner
  call on driver-mutation semantics. The real fix — reject/auto-writeback
  `me` calls on `T?` receivers at type-check time — is a compiler front-end
  change with no scoped, low-risk slice smaller than the whole feature; it
  also risks the forbidden MIR/HIR lowering files listed for this pass.

No code changed by this re-verification pass; doc left OPEN/architectural.

## Provenance of these measurements

Measured in the shared working copy, which was **~64 commits behind
`main@origin`** at the time of the sweep (local tip `9dcd16644b8`). Origin tip
does **not** compile — unrelated `translate_call` trait break, see
`mir_to_llvm_translate_call_trait_break_2026-08-04.md` — so verification against
origin tip was not possible and is **not** claimed. All probe and spec runs used
the pure-Simple self-hosted `bin/simple` in this working copy, interpreter mode
for the language probes and the default runner for the spec.
