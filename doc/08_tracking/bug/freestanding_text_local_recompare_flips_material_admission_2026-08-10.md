# Freestanding x86_64: WM material provenance loss chain — three stacked codegen corruptions

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
layer 3 (page faults in the CPU glass composite) OPEN and now the rung-(d) blocker
**SUPERSEDED 2026-08-10 (see addendum at end of file):** the layer-3 page fault
was never the rung-(d) blocker — it self-recovers (`*** END FRAME (recovering)
***`) and appears in only 2 of 13 archived runs. The actual rung-(d) blocker,
per this file's own Layer 5 below plus the fix that landed after it, was
`render_baremetal_first_frame` never returning — a TIMEOUT the gate
misclassified as `reason=guest-render-fault` — caused by the font-atlas 8 MiB
buffer being reallocated on every reset and exhausting the 1 GiB bump heap
(`_reset_font_atlas`, `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`).
Fixed in commit `4e1d05ba67a4` ("fix(simpleos): reuse font atlas buffer in
place instead of leaking 8MiB per reset").
**Date:** 2026-08-10
**Lane:** SimpleOS WM fullscreen evidence (`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`)
**File:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl` (`compute_styles_with_material`)

## Symptom
Rung-(d) blocker: every WM window degraded with
`[wm-frame] content-provenance-rejected ... fallback=none material=` and
`window-degraded reason=unresolved-or-duplicate-content`; `scanout_capture_size=0`,
all 4 PPMs missing.

## Actual field values feeding the decision (archived run 20260810T072511Z)
```
[web-style-producer] contract-attr index=4 ... raw_match=1 final_match=1
[web-style-producer] entry-rejected index=4 mode=engine2d-cpu-composited-material-v1
  bg=3424591649 gf=4294967295 gt=4294967295 layers_len=0 backdrop_len=25 animation=none
```
bg=0xCC1F1F21 (rgba(31,31,33,0.80) — translucent, correct), backdrop 25 chars =
`blur(30px) saturate(170%)` (admissible), layers empty, static. Every admission
conjunct is TRUE from these values — yet the entry was rejected.

## Root cause (plumbing, not renderer)
The material IS realized. The admission code compared the text locals
`wm_fallback` / `wm_material_mode` again ~120 lines after extraction (past the
font resolver and cascade calls). On the freestanding x86_64 lane the SAME
iteration printed `final_match=1` at extraction depth and then, in the next
build, took NEITHER the admitted NOR the rejected branch — the late `==`
evaluated false both times. Same defect class as the documented
`attr_value(...).trim().lower()` chained-dispatch corruption at the top of the
function; which comparison flips is build-layout dependent.

## Fix
Bind `wm_fallback_is_solid` / `wm_mode_is_cpu` / `wm_mode_is_empty` ONCE
immediately after attribute extraction and use the booleans in
`cpu_admitted` / `solid_admitted` / the rejection guard. Admission semantics
unchanged; the provenance validator
(`wm_content_frame_web_provenance_valid`, `src/lib/common/ui/window_scene.spl`)
was NOT touched. Verified: post-fix runs emit
`[web-style-producer] cpu-entries-ready count=1` and zero
`content-provenance-rejected` lines.

Also added a bounded `entry-rejected-detail` receipt printing every admission
conjunct, so a future rejection names its failing clause instead of forcing
inference.

## Layer 2 (fixed 2026-08-10): corrupt Engine2D dimension re-reads deep in the executor
With the admission witness restored, frames still carried `fallback=none`.
New receipts named the loss precisely (run 20260810T082051Z):
```
[web-material-provenance] witness-unconverted cpu_witness=1 cpu_executed=0 metal_executed=0 sha_len=64
[engine2d-glass] not-composited reason=bounds x=0 y=0 w=392 h=204 fb_w=49 fb_h=204
[engine2d-glass] not-composited reason=bounds x=0 y=0 w=452 h=264 fb_w=452 fb_h=33
```
`eng.width()`/`eng.height()` re-read inside
`_engine2d_draw_ir_render_glass_material` returned one garbage field per call
(49 for a 392px surface; 33 for a 264px one — the struct field-index-collision
class), so every correctly-sized full-surface material rect failed the bounds
check and `cpu_composited_material_count` stayed 0. Fixed by reading the
surface dimensions ONCE at `_engine2d_draw_ir_render_commands` entry and
threading them through `_engine2d_draw_ir_render_box` into the glass check
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`).

## Layer 3 (OPEN — current rung-(d) blocker): CPU glass composite page-faults
Run 20260810T083128Z (first run in which the composite actually executes):
8 recovering `[fault] *** EXCEPTION FRAME ***` at rip 0x8004bc0/0x8004bc2
(`rt_string_concat`) and 0x800434e/0x8004350 (`memcpy`), cr2 wild
(0x37b49f258, 0xffffffffffffff8c). The frame aborts; witness-unconverted with
`readback=` empty. Zero exception frames in every prior archived run — the
bounds corruption of layer 2 was masking this path entirely. This is a
freestanding codegen memory-corruption defect inside
`engine2d_draw_ir_glass_material_pixels` / its callers, not an evidence or
provenance issue. Needs its own reduction. **CONFIRMED STILL OPEN as of run
`20260810T112327Z`** (identical `rip=`/`cr2=` signature) — an earlier same-night
report that this was resolved was WRONG (that run had failed earlier, for a
different reason, and looked clean only because it never reached this path).

### Track W1 workaround attempted (2026-08-10, run `20260810T123139Z`) — FAILED, not a false lead but a wrong dependency assumption
Per `doc/03_plan/sys_test/simpleos_qemu_wm_real_screen.md` § "2026-08-10
rung-(d) minimum-path execution plan": added `_WM_CONTENT_FRAMES_ENABLED: bool
= false` (`src/os/desktop/shell.spl:99`) and gated
`self.runtime_content_frames(scene_revision)` in `render_baremetal_frame`
(`shell.spl:990-993`) to return `[]` when the flag is off, intending a
chrome-only first frame that skips the crashing paint entirely. Also flipped
`_WM_TRACE` to `true` for step localisation. Origin-sync precondition verified
first: fetched tip `a3b9ef4ec40`, confirmed `e99a5b76d11` (the
`closures_structs.rs` deep-field-copy fix) is an ancestor before building.

Gate run (`check-simpleos-wm-fullscreen-evidence.shs`) result:
`simpleos_wm_fullscreen_status=fail reason=guest-render-fault`,
`scanout_capture_size=0`, all four PPMs `missing` — did NOT reach rung (d).
Archived serial log (`build/simpleos_wm_fullscreen_evidence/runs/20260810T123139Z-fail/serial.log`,
297 lines, truncated with no fault frame and no `[wm-render-step]` trace lines
at all despite `_WM_TRACE=true`) shows the SAME
`web-style-producer`/`rfm`/`web-material-provenance witness-unconverted` →
5x `0x1dc020`-byte heap-alloc sequence that precedes the fault in the prior
`20260810T112327Z` run (compare lines 267-276 there), occurring during
`[desktop-gui] process-owned-surfaces-ready` / window materialize — i.e.
**before `render_baremetal_frame` is ever reached**. This falsifies the plan's
dependency note ("this track needs NO paint output at all... every window
takes the already-tolerated degraded branch"): the crash-triggering content
paint is NOT confined to the `runtime_content_frames` call gated by the new
flag — it also fires eagerly during window/surface materialization, on a path
this change does not touch. The flag and guard are implemented correctly per
the plan's steps 1-2 (lint-clean, default off, `runtime_content_frames` itself
untouched) but do not achieve the intended chrome-only degradation because the
paint call site assumed to be the only trigger is not the only trigger.
No check was weakened; `wm_content_frame_web_provenance_valid` and the gate
script are untouched. Root-causing the materialize-time paint trigger belongs
to Track W2 (root-cause, out of scope here) — this remains a DIAGNOSTIC run,
not a gate pass.

## Gap analysis — why nothing caught it
- AOT/freestanding-lane defects are invisible to the host spec corpus (known
  trap: host specs run interpreter/JIT, not the freestanding backend).
- The rejection path printed an aggregate line whose fields all looked valid —
  the receipt did not name the failing conjunct (now fixed).
- No enumeration was done for the family: any long function on the
  freestanding lane that re-compares a text local after many intervening calls
  is at risk. The compiler-level defect (text locals corrupted across call-rich
  regions / spill paths) needs its own reduction and fix; this doc is the
  tracking anchor.

## Track W2 — page-fault root-cause trace (2026-08-10)

Budget-boxed 45min trace. No fix landed; the fault is now precisely localised
and two whole hypothesis families are RULED OUT. Evidence is archived-per-run
only (`build/simpleos_wm_fullscreen_evidence/runs/<ts>/serial.log`); the
canonical `serial.log` was not used.

### The fault is 4 RECOVERED PAIRS, not one crash

Only 2 of 13 archived runs contain any `[fault]` at all
(`20260810T083128Z-fail`, `20260810T112327Z-fail`); both contain exactly 8
frames, and every frame ends `*** END FRAME (recovering) ***` — execution
continues afterwards (`[rfm] at=default-font` resumes). The 8 frames are 4
PAIRS, and the pairing is the whole story:

| pair | rip | cr2 run A | cr2 run B | role |
|---|---|---|---|---|
| 1 | `0x8004bc0` / `0x8004bc2` | `0x2bfd659d8` / `0xff..ff8c` | `0x37b49f258` / `0xff..ff8c` | load src / store dst |
| 2 | `0x800434e` / `0x8004350` | `0x2bfd659e0` / `0xff..ff8e` | `0x37b49f260` / `0xff..ff8e` | load / store |
| 3 | same | `...9e1` / `ff8e` | `...261` / `ff8e` | load / store |
| 4 | same | `...9e2` / `ff8e` | `...262` / `ff8e` | load / store |

The **source** address increments `+8, +1, +1` (one qword then bytes — a
memcpy tail) and **differs between runs**. The **destination** address is a
small negative that does NOT advance (each store faults and is skipped by the
recovering handler, so `rdi` never commits).

### `cr2 = 0xffffffffffffff8e` — hypothesis CONFIRMED and made concrete

It is not a wild address and not "null plus an offset". In
`rt_string_concat` (`src/runtime/runtime_native.c:2670-2699`):

```c
uint64_t len = a->len + b->len;
RtCoreString* out = malloc(sizeof(RtCoreString) + (size_t)len + 1);
...
if (a->len > 0) memcpy(out->data, a->data, (size_t)a->len);
if (b->len > 0) memcpy(out->data + a->len, b->data, (size_t)b->len);
```

`0xff..ff8e` is `out->data + a->len` **wrapping** — i.e. `a->len` is a huge /
negative-as-signed value. `len = a->len + b->len` is **unsigned and
unchecked**, so it wraps to a small number, `malloc` SUCCEEDS (so the `!out`
guard never fires), and the subsequent `memcpy` is then handed the *un-wrapped*
`a->len`. That is the wild walk. The paired source address is `a->data`, also
garbage (~11-15 GB, well past guest RAM; heap bump offsets at fault time are
only ~`0x1c74_5690` ≈ 475 MB).

### Ruled OUT

- **Shallow-copy aliasing / struct copy.** Already ruled out by `4f755fdeb930`
  and `2009e71905e4` leaving the signature identical; this trace agrees —
  nothing here is a copied struct.
- **Untagged integer aliasing `RT_VALUE_TAG_HEAP`** (the classic family
  documented at `rt_core_register_enum`). `rt_core_as_string`
  (`runtime_native.c:1659-1667`) is fully fenced: it rejects `raw < 4096`,
  checks the tag, then does a **pure pointer-membership test**
  (`rt_core_is_registered_string` -> `rt_core_is_registered_immortal_ptr`)
  BEFORE touching `->kind`. So `a` is a genuinely registered, runtime-allocated
  `RtCoreString`. Its **header fields (`len`, `data`) are corrupted in place** —
  this is heap-header corruption, not a bogus handle.

This *refines* the existing "text local corrupted across call-rich regions"
finding above: the local is fine, the **string object header is overwritten**.

### Localised to one statement region

Both faulting runs fault immediately after
`[web-style-producer] cpu-entries-ready count=1 len=368`, emitted at
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:3166`
(end of `compute_styles`). `material_entries[0]` is built by repeated `+`
interpolated concatenation (lines 3110-3137). Contradiction worth chasing: the
string is only **368 bytes**, yet the immediately preceding log lines are
repeated `[array-repeat] big count=0x100000` / `[heap] alloc sz=0x800020`
(1,048,576 elements, 8 MB per allocation, several in a row, `caller=0x83d265e`
in run A and `0x83d27fe` in run B — different builds, same shape).

### Strongest remaining lead (in priority order)

1. **Find who writes the 8 MB / 1M-element `array-repeat` allocations during
   style computation.** A 368-byte result should never need them. If that
   count is itself a corrupted length, the same corrupt value plausibly
   explains `a->len`. Start at the `[array-repeat] big` probe and resolve
   `caller=0x83d265e` against the run's map file.
2. **Determine whether the baremetal `malloc` bump allocator bounds-checks its
   arena.** Heap is at ~475 MB and each array-repeat burns 8 MB; if the arena
   is overrun and a non-NULL out-of-arena pointer is returned, subsequent
   `RtCoreString` header writes land on foreign memory — which is exactly the
   observed in-place header corruption.
3. **Harden `rt_string_concat` regardless of root cause.** It has no length
   sanity check and its `a->len + b->len` unsigned overflow converts a corrupt
   header into a wild `memcpy` instead of a detectable error. A guard there
   (reject `a->len`/`b->len` beyond a sane bound, and reject the addition
   overflow) would turn this silent corruption into a diagnosable failure and
   very likely move the gate past this point. This is hardening, not a fix, and
   was deliberately NOT landed here so the underlying corruptor is not masked
   before lead 1 is chased.

No check was weakened; `wm_content_frame_web_provenance_valid` untouched; no
composite stubbed; no gate run was performed for this trace (analysis only).

## Layer 4 (2026-08-10, opus): the real rung-(d) blocker — `render_baremetal_first_frame` NEVER RETURNS

Evidence base: archived per-run logs only (canonical `serial.log` is racy).
Furthest-reaching run `build/simpleos_wm_fullscreen_evidence/runs/20260810T083128Z-fail/`
(421 lines; next `20260810T112327Z-fail`, 415). Kernel
sha256 `cfa3c112...b901bcdb`, builder `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
sha256 `bed40ba3...490710d9`.

### Classification: READINESS NEVER SATISFIED (not "capture fails")
`[production-readiness]` appears in **0 of 8** archived runs. It is emitted at
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:626` — NOT in
`src/os/**`, which is why prior repo-wide `src/` greps found only the *expected*
copy in `src/os/desktop_qemu_contract.spl:118`. The gate entry is
`ENTRY="examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl"`
(`scripts/check/check-simpleos-wm-fullscreen-evidence.shs:886`).

### Exact stop point
The guest reaches, in order (log lines 234-236):
- `:566` `[desktop-gui] process-owned-surfaces-ready count=3`
- `:569` `[desktop-gui] launcher apps=15`
- `:581` `Engine2dWmFrameExecutor.create_host_gpu(...)` -> `[wm-frame] host-gpu-fallback`

then enters `:587 shell.render_baremetal_first_frame(wm_frame_executor)` **and
never leaves it**. Proof: none of the four unconditional prints that follow the
call ever appear in ANY run — `[engine2d-simd] arch=x86_64 ...` (`:601`),
`[font-evidence*]` (`:620/622/624`), `[desktop-gui] desktop-ready` (`:625`),
`[production-readiness]` (`:626`). Nor does the failure branch `:590`
`[production-readiness-failed] reason=simple2d-or-simple-web-frame-invalid`.
Neither success nor failure is emitted => the call did not return.

`qemu.out` ends `terminating on signal 15 from pid ... (sh)` — the wrapper
SIGTERMed a still-running QEMU. The guest was alive and rendering when killed;
this is a **non-termination/timeout**, not a crash and not the page fault.
`reason=guest-render-fault` is a misclassification by
`check-simpleos-wm-fullscreen-evidence.shs:1317` keying off the (self-recovering)
fault frames that happen to be present.

### What the frame is doing when time runs out
Tail of the log is an unbounded repeat of first-frame paint work:
- `[rfm]` measure/cache cycles per glyph run,
- `[array-repeat] big count=0x100000` (1,048,576 elems) x6, each followed by
  `[heap] alloc sz=0x800020` (8 MiB), heap offset climbing 0x194->0x1c7 (~475 MiB),
- `[engine2d-glass] not-composited reason=bounds x=0 y=0 w=392 h=204 **fb_w=49** fb_h=204`
  and `... w=452 h=264 fb_w=452 **fb_h=33**` -> both glass composites rejected on
  bogus framebuffer extents (real fb is 3840x2160), falling into
  `uncounted-contract-rect ... reason=glass-material-fallback-painted`,
- `[web-material-provenance] witness-unconverted cpu_witness=1 cpu_executed=0`.

So the first frame at 4K is repeatedly re-allocating 8 MiB scratch buffers on the
glass **fallback** path (taken because `fb_w`/`fb_h` arrive corrupt), and does not
converge before the wrapper's timeout.

### Consequence for Track W1
The `runtime_content_frames` flag gating cannot help: the non-termination is in
`render_baremetal_first_frame`, upstream of and independent from the degraded
content-frame paint. That is why W1 still reported `reason=guest-render-fault`.

### Next lead (NOT contained; no fix landed)
Chase the corrupt `fb_w=49` / `fb_h=33` reaching the glass bounds check — one
truncated extent per rect, each wrong on a different axis, smells like the same
class as the already-filed
`native_trailing_default_param_reads_uninitialized_2026-08-09.md` defect that bit
`create_host_gpu`'s `backend_required` two lines earlier (`:573-581`). Fixing the
extents should take both glass rects off the allocating fallback path.

No check was weakened; `wm_content_frame_web_provenance_valid` untouched; no
composite stubbed; no readiness marker faked; OVMF pflash unchanged.

## Layer 4 (2026-08-10, ~13:20Z): trailing-default-param lead REFUTED; fb_w/fb_h already fixed; blocker MOVED

### The lead is refuted, on two independent grounds
1. `native_trailing_default_param_reads_uninitialized_2026-08-09.md` is status
   **FIXED** (MIR call-lowering pad landed; fence in `check-aot-lane-fences.shs`).
   It cannot be the live cause of anything today.
2. The corrupt extents were never a default-param bind at all. The sole producer
   is `_engine2d_draw_ir_render_glass_material`
   (`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:508`, log at `:542`), whose
   `fb_w`/`fb_h` are **explicit positional args** at its one call site (`:699`),
   threaded from `_engine2d_draw_ir_render_commands` (`:1420`). No omitted
   trailing default exists anywhere in that chain.

### The fb_w/fb_h corruption was ALREADY FIXED before this pass
Commit **`439d64e2b3e`** ("fix(simpleos): restore WM material provenance witness
on freestanding lane", 2026-08-10 09:01Z, ancestor of HEAD) hoisted the surface
dimension read to loop entry (`val surface_fb_w = eng.width()` at `:1426`) and
threads it down, precisely because deep `eng.width()`/`eng.height()` re-reads
returned garbage on the freestanding lane. The in-source comment at `:528-535`
records the same `fb_w=49` / `fb_h=33` measurements this chain chased. Attributed
there to the **struct field-index-collision** class, not the default-param class.

### Gate evidence: the fix worked, and the blocker moved
Archived runs (`build/simpleos_wm_fullscreen_evidence/runs/`), all still `fail`:

| run | `reason=bounds` | `[GUI] fb_w` | `array-repeat` | ending |
|---|---|---|---|---|
| `20260810T083128Z` (pre-fix) | **present**, `fb_w=452 fb_h=33` | `0xf00` (3840) | 6 | truncated mid-stream (timeout) |
| `20260810T112327Z` (post-fix) | **none** | `0xf00` | 6 | truncated mid-stream |
| `20260810T123139Z` (post-fix) | **none** | `0xf00` | 3 | clean `[PANIC] heap exhausted` |

So the extent corruption is genuinely gone, and the failure mode changed from
non-termination to a **terminating, diagnosable panic**:
`[PANIC] heap_off=0x3fffa5e0 req=0xb4d0 limit=0x40000000` — the 1 GiB baremetal
bump heap is exhausted by never-freed `sz=0x800020` (8 MiB) `array-repeat
count=0x100000 caller=0x83d477e` buffers plus `sz=0x1dc020` (~1.9 MiB) runs.

### The real remaining blocker (unchanged by the fb_w fix)
`[web-material-provenance] witness-unconverted cpu_witness=1 **cpu_executed=0**
metal_executed=0 sha_len=64` is present in **all three** runs, including the two
where the bounds check no longer rejects anything. The bounds rejection was
therefore **not** the cause of `cpu_executed=0`; removing it did not convert a
single witness. Rung (d) is blocked on the CPU material composite never
executing, plus 1 GiB heap exhaustion on the first 4K frame.

### Next concrete step
Two separable items, in order:
1. Find why `cpu_executed` stays 0 with a bounds-admitted, contract-length-
   capability glass rect — instrument the arms after the bounds check in
   `_engine2d_draw_ir_render_glass_material` (`realized-props-missing`,
   `device-glass-state-unknown`, `cpu-glass-pixels`); none of those receipts
   appear in the post-fix logs either, so the rect may not be reaching this
   function at all post-`typed_nonuniform` (`:690`).
2. The 8 MiB `array-repeat count=0x100000` at `caller=0x83d477e` is allocated
   per attempt and never freed; at 1 GiB it caps the first frame regardless.
   1,048,576 elems is not a 3840x2160 surface (8,294,400) — identify the buffer.

No check was weakened; `wm_content_frame_web_provenance_valid` untouched; no
composite stubbed; no bounds check relaxed; OVMF pflash unchanged. No code
changed in this pass — findings only.

## Layer 5 (2026-08-10, ~14:00Z): `cpu_executed=0` trace — Layer 4's conclusion is REFUTED; the post-fix experiment never ran

### Exact emission sites (both ends of the gap)
- **Receipt:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:601`,
  inside `simple_web_layout_material_provenance_after_backend_execution` (`:568`).
  `cpu_witness` = `witness.cpu_composited_count` (style-pass sidecar);
  `cpu_executed` = the `executed_cpu_material_count` **parameter**. This function
  computes nothing — it only reports what a caller handed it.
- **Callers (all three pass `render.cpu_composited_material_count`):**
  `simple_web_layout_engine2d_fast.spl:230`, `src/os/compositor/simple_web_window_renderer.spl:436`
  and `:553`.
- **Sole producer:** `draw_ir_adv.spl:1476` —
  `if box.glass_execution.execution_target == "cpu-scalar-glass-v1": cpu_composited_material_count + 1`,
  where `box` comes from `_engine2d_draw_ir_render_box` (`:642`), which reaches the
  composite only via `_engine2d_draw_ir_render_glass_material` (`:508`) and skips it
  entirely when `typed_nonuniform` (`:690`).

So `cpu_executed=1` requires exactly one thing: the glass rect reaching `:508`
and passing capability (`:523`) + bounds (`:538`).

### The decisive measurement: ZERO `[engine2d-glass]` receipts in the post-fix runs
Archived logs, token census over the whole file:

| run | any `[engine2d-glass]` line | `witness-unconverted` | its `readback=` field | ending |
|---|---|---|---|---|
| `20260810T083128Z` (pre-fb-fix) | **4** (`reason=bounds` x2, `uncounted-contract-rect` x2) | 4 | 2x empty, 2x `cpu_fallback` | timeout |
| `20260810T112327Z` (post-fix) | **0** | 2 | **both empty** | timeout |
| `20260810T123139Z` (post-fix) | **0** | 1 | **empty** | `[PANIC] heap exhausted` |

The `[engine2d-glass]` receipts are **length-gated, not equality-gated** (`:517`,
`cap_is_contract_len`) precisely so they fire even under text-compare corruption.
Their total absence therefore proves `_engine2d_draw_ir_render_glass_material` was
**never entered** in either post-fix run — not that it entered and passed bounds.

### What that means for Layer 4's claim
Layer 4 read "`reason=bounds` none in post-fix runs" as *the bounds check no longer
rejects anything*, and concluded "removing the bounds rejection converted no
witness, so the composite is independently broken". Both post-fix runs simply
**died before the render loop reached the glass command** (`123139Z` panics in
`css-props-stage3`; `112327Z` is truncated mid style pass). The experiment was
never performed.

### The surviving `witness-unconverted` lines are the PRE-execution decision
In the pre-fix run the two receipts per window are distinguishable by their
`readback=` field: the first (`:267`, `target= readback=`) is emitted **before**
any `[engine2d-glass]` line, the second (`:291`, `readback=cpu_fallback`) after.
The post-fix runs contain **only the empty-`readback` variety**. A provenance
decision taken on a render whose `readback_source` is still empty is one taken
before the backend executed — `cpu_executed=0` there is structurally expected,
not a defect. There is no evidence of a witness that formed, reached an executed
composite, and failed to convert.

### Conclusion: `cpu_executed=0` is a DOWNSTREAM SYMPTOM, not the blocker
The rung-(d) blocker is the item Layer 4 filed second: the never-freed
`[array-repeat] big count=0x100000` / `[heap] alloc sz=0x800020` (8 MiB) buffers
at `caller=0x83d477e`/`0x83d27fe` exhausting the 1 GiB baremetal bump heap
(`heap_off=0x3fffa5e0 limit=0x40000000`) during the style pass, before the draw-IR
render loop runs. Until that is fixed no run can reach `:508`, and any statement
about the composite's behaviour is unfalsifiable.

### Strongest remaining lead (unchanged in substance, now unambiguously first)
Resolve `caller=0x83d477e` against the run's map file and identify the
1,048,576-element buffer (**not** a 3840x2160 surface = 8,294,400). It is
allocated repeatedly per style-pass attempt and never freed. Fixing or bounding
it is the prerequisite for every further rung-(d) measurement; only after a run
reaches the render loop can `cpu_executed` be re-measured.

No fix landed in this pass. No check weakened; `wm_content_frame_web_provenance_valid`
untouched; no composite stubbed; no bounds check relaxed; OVMF pflash unchanged;
no gate run performed (the finding is derived entirely from archived per-run logs).

## 2026-08-10 addendum — blocker resolved, page-fault framing corrected

This file's own Layer 5 (above) already concluded `cpu_executed=0` is a
downstream symptom of heap exhaustion during the style pass, not an
independent second defect, and identified the never-freed `[array-repeat]`
8 MiB buffers as the prerequisite blocker. That diagnosis is confirmed and the
fix has since landed: `_reset_font_atlas`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`) reallocated an 8 MiB
buffer on every atlas reset instead of reusing it in place, exhausting the
1 GiB baremetal bump heap and causing `render_baremetal_first_frame` to never
return. The gate's 300 s readiness timeout then misclassified that
non-termination as `reason=guest-render-fault`. Fixed by commit
`4e1d05ba67a4` ("fix(simpleos): reuse font atlas buffer in place instead of
leaking 8MiB per reset"), verified: post-fix runs show zero
`[engine2d-glass]` receipts (the composite is never reached at all), matching
this document's own evidence table above — not two separable blockers.

The "layer 3 (page faults ... OPEN)" status line at the top of this document,
and the classification of the `memcpy`/`rt_string_concat` page fault as *the*
rung-(d) blocker, is **SUPERSEDED**: that fault self-recovers
(`*** END FRAME (recovering) ***` in the serial log) and is present in only 2
of 13 archived runs. It was never the blocking condition — the heap
exhaustion documented in this file's own Layer 5 was. The hypothesis is kept
here, marked superseded, rather than deleted.

The pre-existing `fb_w=49`/`fb_h=33` framebuffer-extent corruption discussed
above (§ Layer 4) was **already fixed before this document's session**, by
commit `439d64e2b3e` ("fix(simpleos): restore WM material provenance witness
on freestanding lane"). This document's Layer 4 correctly identified it as
already-fixed and did not claim to have newly fixed it — no correction needed
on that point, restated here only for cross-reference with the other docs in
this campaign.

## 2026-08-11 — rung-(d) verification: fix IS landed on origin/main; NO post-fix gate run exists

**Correction to an earlier draft of this addendum (self-corrected before
push):** a first pass here wrongly concluded `4e1d05ba67a4` was not on
`main`, because it was checked against a **stale local `main`/HEAD**
(`a4b037eff19`) that had never been fetched from origin — exactly the
documented repo trap "FETCH before asserting a commit is at origin; a stale
tracking ref fakes 'missing'". Re-verified against a fresh fetch:

```
git fetch https://github.com/ormastes/simple.git main:refs/tmp/origin_main_check
git rev-parse refs/tmp/origin_main_check
  -> 301aa18ee138fb190041292d2b559fe50919ee6f
git merge-base --is-ancestor 4e1d05ba67a4 refs/tmp/origin_main_check
  -> IS ANCESTOR of origin/main
git rev-parse refs/tmp/origin_main_check:src/lib/nogc_sync_mut/text_layout/font_renderer.spl
  -> bba48aa8a09e1033d325db1c42700720d2041dd0
git rev-parse 4e1d05ba67a4:src/lib/nogc_sync_mut/text_layout/font_renderer.spl
  -> bba48aa8a09e1033d325db1c42700720d2041dd0   (identical blob)
```

So the font-atlas fix **is landed on `origin/main`** at `301aa18ee138`, and
the local checkout used for this verification session was simply behind
origin at the time — not a real gap in the fix's landing. The earlier
"NOT YET COMMITTED to main" conclusion in this section is retracted.

**No archived run postdates the fix.** Checked every `runs/<timestamp>/`
directory under all four evidence roots
(`build/simpleos_wm_fullscreen_evidence{,2,3}/`,
`.../simpleos_wm_fullscreen_evidence_provlane/`); only the first and
`_provlane` have any archived runs, and the newest overall is
`build/simpleos_wm_fullscreen_evidence/runs/20260810T140559Z-fail`
(archived 14:05:59Z, 2 minutes after the fix commit's 14:03:44Z timestamp —
too soon for a real rebuild+boot+render cycle, which this campaign has
independently measured at 15-40 min; its kernel almost certainly predates
the fix).

**That newest run's actual outcome** (read `serial.log` — 313 lines — to its
true end, per the constraint):
- `evidence.env`: `simpleos_wm_fullscreen_status=fail`,
  `simpleos_wm_fullscreen_reason=guest-render-fault`. This stored reason
  does **not** match the log content — see below.
- `[PANIC] heap exhausted` — **absent**. No PANIC of any kind appears in
  this run's serial log.
- `[engine2d-glass]` — **absent** (grep for `heap exhausted|engine2d-glass|
  PANIC|render_baremetal_first_frame` over the full log returns zero
  matches).
- The log instead runs cleanly through composite and shutdown: `[wm-frame]
  frame-degraded ... rendered=12`, `[wm-render-step] at=done`,
  `[desktop-gui] first-frame-rendered scene_revision=1479773126`,
  `[production-readiness] wm=live simple_gui=object-tree
  simple_web=content-frame renderer=engine2d process_owned_surfaces=3
  scanout_generation=1`, `[desktop-gui] desktop-ready`, then `[INFO]
  [desktop] [shell] entering baremetal event loop...` and
  `[wm-loop] polling-active` as the final line. `qemu.out`'s only content is
  `qemu-system-x86_64: terminating on signal 15 from pid ... (sh)` — a
  SIGTERM from the harness's own CPU-time monitor, not a guest fault.
- `scanout_capture_size=0`; all four PPM artifacts
  (`browser_event/baseline/fullscreen/restored.ppm`) show
  `*_file_status=missing`, `*_bytes=0` — none exist, so non-uniformity
  cannot be evaluated.
- Net: this run reached first-frame render and the guest event loop with
  **no heap exhaustion and no panic**, but the harness's post-boot input/
  capture sequence (baseline → maximize → restore → screenshot) never ran
  before the CPU-time monitor killed QEMU, so `reason=guest-render-fault` in
  `evidence.env` is a misclassification of "no capture happened" carried
  over from the pre-fix template, not evidence of a fault in this
  particular run.

### What runs between `[wm-loop] polling-active` and the capture step, and what actually killed this run

Read from `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (the gate
script itself, not inference): the readiness wait loop
(`SIMPLEOS_WM_READINESS_TIMEOUT_MS`, default 300000 ms) breaks out **as soon
as** `[scanout-evidence]`, `[production-readiness]`, and a font-evidence
marker are all present in the serial log — all three were present in this
run, so the 300 s readiness ceiling was not what ended it; the script moved
past readiness normally. After that it computes/validates scanout metadata,
then invokes a single unbounded `python3` heredoc (line ~1388) that runs the
whole capture sequence over the QMP socket: `wait_remote_browser_ready()`
(own 120 s deadline) → capture `baseline.ppm` → send F11 → `
wait_press_correlation` for maximize (own 300 s deadline) → capture
`fullscreen.ppm` → send F11 → `wait_press_correlation` for restore (300 s) →
capture `restored.ppm` → pointer click → `wait_pointer_correlation` →
`wait_browser_content_presented` (120 s) → capture `browser-event.ppm`. None
of these internal waits are wrapped by the script's own `timeout`/`gtimeout`
(`TIMEOUT_BIN` is only used for the kernel-build step) — worst case they sum
to ~14 minutes of legitimate internal polling before the script itself would
raise `capture-input-or-guest-correlation-failed`.

This run's serial log contains **zero** markers from that capture phase
(no `[remote-browser-ready]`, no `simpleos_wm_input_submitted`, nothing in
`capture.out` for this run) — the log simply stops at `[wm-loop]
polling-active`. Combined with `qemu.out`'s `terminating on signal 15`, the
kill happened **before or during the very start of the python3 capture
step**, and came from **outside the gate script's own logic** (no internal
timeout in the reachable code path fires that fast from a standing start).
The most likely source, per this repo's own documented trap ("`kill_monitor`
SIGTERMs any run ≥60s CPU"), is the invoking session's external CPU/wall-time
watchdog on the background process running the gate — not a guest fault, not
the 300 s readiness ceiling, and not one of the capture phase's own 120s/300s
deadlines. The archived files alone cannot pin down which external watchdog
or its exact duration; that requires the invoking session's own process
history, which is not part of this evidence set.

**If confirmed as a harness-level kill, this is a materially cheaper problem**
than a rendering defect: the fix path would be running the gate under a
wrapper (or `run_in_background`) exempt from the short external CPU-time
guard, giving the internal ~14-minute worst-case capture budget room to run,
rather than any change to guest or gate code.

## 2026-08-11 (second pass) — detached run attempted; blocked on native-build timeout, not capture

Ran `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` fully detached
(`setsid nohup ... sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
> logfile 2>&1 < /dev/null &`, then `disown`), with `SIMPLE_TIMEOUT_SECONDS=3600`,
polled via file reads (not `tail -f`, per this doc's own prior trap) plus a
`Monitor` task tailing the log for new lines. Binary/kernel identity at start:
`bin/simple` → `release/x86_64-unknown-linux-gnu/simple` (symlink present and
intact throughout — checked at start and end, not deleted by a parallel
session this time). Local working-tree blob for
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` verified identical
(`bba48aa8a09e1033d325db1c42700720d2041dd0`) to the fixed blob at
`4e1d05ba67a4` / `origin/main`, so no rebase was needed — the fix was already
present in the tree the gate built from.

**Mid-run, a false "two concurrent racing gate runs" alarm was raised and
resolved.** `PID 816856` (mine, started 00:30:44) had a short-lived child
`PID 834897` (ppid 816856, exited before the concern was raised) that looked
like a second top-level invocation but was not — `ps` confirms only one
`check-simpleos-wm-fullscreen-evidence.shs` process alive at any checked
instant. The archived directory `runs/20260811T003044Z-fail` that seeded the
alarm carries file mtimes of **2026-08-10 14:10** — the gate's own
`retained_previous_run=...` startup line explains this: it relabels/copies a
prior failed run under a fresh timestamp for reference, it did not represent
a new result. **Correcting the addendum above:** the "external watchdog"
hypothesis was independently re-examined and the actual kill mechanism was
found by reading the script, confirming the coordinator's correction — QEMU
is launched directly (`qemu-system-x86_64 ... &`, `QEMU_PID=$!`,
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs:1209`), not under
`timeout`; the SIGTERM logged as `"from pid ... (sh)"` in `qemu.out` comes
from the script's own `cleanup()` trap (lines 174–179:
`kill "$QEMU_PID"` + `pkill -f "qemu-system.*$QMP_SOCKET"`), which fires
whenever the script's own exit path runs. So `setsid`/`nohup` detachment does
not by itself prevent this class of self-inflicted kill; it only removes an
*external* watchdog as the killer, which the earlier addendum had assumed
without reading the script.

**This run's actual outcome, read from `evidence.env` after the script
exited on its own** (not killed by us or by any watchdog):

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=wm-simple-web-build-timeout
simpleos_wm_fullscreen_kernel_build_status=timeout-cache-preserved
simpleos_wm_fullscreen_kernel_build_attempts=1
simpleos_wm_fullscreen_native_build_timeout_seconds=900
simpleos_wm_fullscreen_serial_log_bytes=0
simpleos_wm_fullscreen_disk_image_status=not-staged
simpleos_wm_fullscreen_browser_demo_build_status=not-built
```

The run never reached QEMU boot at all this time — the kernel's own native
build (from a full `1512`-file source closure, `kernel_source_input_set=
closure+linked-symbol-repair`) exceeded the gate's internal **900 s**
(`SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT`-class) native-build ceiling on this
attempt, despite the same source tree compiling+linking in ~116 s earlier in
the same session when most objects were warm-cached (`Build complete: 5
compiled, 752 cached, 0 failed`). This run's build evidently missed that
cache (new `native-objects-PnAZS3` directory vs. the earlier
`native-objects-tcPW8M`) and had to recompile a much larger fraction of the
1512-file closure from cold, on a host that had other concurrent build/search
activity from parallel sessions during the same window. `serial_log_bytes=0`
and `disk_image_status=not-staged` confirm this is a pure build-timeout
short-circuit, not a boot or capture-phase failure — a different, earlier
failure mode than the truncated-at-`polling-active` one this document's prior
addendum diagnosed, and unrelated to the capture-phase watchdog question.

**Rung (d) remains UNVERIFIED after this pass.** No HARD CONSTRAINT was
touched (read-only + one gate invocation; no stubbing, no relaxation of
`wm_content_frame_web_provenance_valid`, OVMF pflash only, no `-kernel`/
`isa-debug-exit`). Given the task's 60-minute wall-clock ceiling was consumed
by this single native-build-timeout attempt, no further run was started.
**Next required step:** re-run the gate with either (a) a warm/populated
native-object cache guaranteed before starting (so the 900 s native-build
ceiling isn't spent on a cold rebuild), or (b) `SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT`
raised for one diagnostic run, on a host with no concurrent competing
build/search load, budgeting the full ~15–40 min build plus the ~14-minute
worst-case capture sequence documented above — i.e. budget close to an hour
for this step alone, not sharing that hour with kernel-currency verification
or alarm triage as this pass did.

This result was pinned (not pushed — `check-tree-size-push.shs` was reported
too costly/incomplete to run in this window) at
`refs/pending/wm_rung_d_verification_20260811b`.

**Rung (d) is UNVERIFIED, not reached, but the fix is confirmed on
`origin/main`.** No HARD CONSTRAINT was touched by this verification pass
(read-only). Per the task's 40-minute ceiling and the "prefer reading over
generating" budget directive, **no new gate run was started**. Next required
step: re-run `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
end-to-end from a background invocation that will not be killed by a short
external CPU/wall-time watchdog before the ~14-minute worst-case capture
sequence can finish, then confirm `[engine2d-glass]` appears, capture
succeeds (`scanout_capture_size>0`, all four PPMs present and non-uniform),
and the verdict string itself (not just absence of PANIC) says pass.
