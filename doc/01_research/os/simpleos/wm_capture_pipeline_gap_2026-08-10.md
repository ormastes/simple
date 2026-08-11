# SimpleOS WM rung-(d): why `scanout_capture_size=0` and no PPMs

**Date:** 2026-08-10
**Lane:** `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
**Status of gate:** `simpleos_wm_fullscreen_status=fail`,
`reason=dynamic-scanout-or-desktop-readiness-missing`
**Classification:** **(d) upstream precondition never satisfied**, and the thing that
never satisfies it is **(c) code that runs but wedges/faults** — specifically the
first-frame paint. It is *not* (a) mis-wired capture and *not* (b) missing capture code.

This document is written to be executable with no other context.

---

## 1. Where `scanout_capture_size` comes from, and what must happen

Capture is **entirely host-side**. Nothing in the guest captures anything.

| step | location |
|---|---|
| default value | `scripts/check/check-simpleos-wm-fullscreen-evidence.shs:1221` — `scanout_size=0` |
| readiness wait loop | `:1314-1336` — polls `serial.log` for `[scanout-evidence]`, `[production-readiness]`, and one of `[font-evidence]` / `[font-evidence-unavailable]`. Timeout `SIMPLEOS_WM_READINESS_TIMEOUT_MS`, default **300000 ms** (`:1312`) |
| fail-reason ladder | `:1359-1383`. **`:1361-1362`**: `if [ -z "$scanout_marker" ] || [ -z "$ready_marker" ]; then reason="dynamic-scanout-or-desktop-readiness-missing"` |
| size computed | **`:1379`** `scanout_size=$((scanout_stride * scanout_height))` — *inside the final `else`*, i.e. only reached when **both** markers were seen and metadata/bounds/range checks passed |
| capture executed | `:1388` — inline `python3` block, `pmemsave` over QMP: `pmem()` at `:1434-1455` issues HMP `pmemsave <address> <size> <path>.raw`, then converts argb8888 → P6 PPM |
| reported | `:1894` `echo "simpleos_wm_fullscreen_scanout_capture_size=$scanout_size"`; PPM byte counts at `:1929-1948` |

**Therefore `scanout_capture_size=0` is not a capture failure at all — it is the
literal initialiser at `:1221` surviving because control never reached `:1379`.**
The four PPMs are missing for the same reason: the python capture block at `:1388`
is never invoked. `pci_found=1 / pci_decode=1` and full 3840x2160 geometry are
reported because they are parsed from the `[scanout-evidence]` serial line, which
*is* present — the scanout half of the conjunct is satisfied; the
`[production-readiness]` half is not.

**What has to happen for a non-zero size:** the guest must print
```
[production-readiness] wm=live simple_gui=object-tree simple_web=content-frame renderer=engine2d ...
```
Nothing else. There is no other lever.

### Guest emitter chain (the only producer of that line)

Entry: `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
(the gate pins it at `check-simpleos-wm-fullscreen-evidence.shs:886`,
`ENTRY="examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl"`).

Ordered emission points (file: `gui_entry_desktop.spl`):

```
:413  [desktop-gui] initializing framebuffer...
:414  bga_init_scanout(3840,2160,32)
:418  [scanout-evidence] address=... pci_decode=...        <-- gate SEES this
:428  [desktop-gui] framebuffer ready ...
:429  [desktop-gui] engine2d-ready backend=baremetal-framebuffer persistent=true
:521  [desktop-gui] compositor ready
:525  [desktop-gui] shell initialized
:529-548 spawn + materialize Browser Demo / Hello World / Clang
:566  [desktop-gui] process-owned-surfaces-ready count=3
:569  [desktop-gui] launcher apps={registered}             <-- LAST LINE EVER SEEN
:571  map_qemu_host_gpu_ivshmem_bar2_active_vmm()
:581  Engine2dWmFrameExecutor.create_host_gpu(...)
:587  val first_frame_revision = shell.render_baremetal_first_frame(wm_frame_executor)   <-- NEVER RETURNS
:589-592 if first_frame_revision <= 0 -> [production-readiness-failed] + port_outb(0xF4,1) + return
:601  [engine2d-simd] ...
:616-624 font evidence
:625  [desktop-gui] desktop-ready
:626  [production-readiness] ...                            <-- gate NEEDS this
:628  shell.run_baremetal(...)
```

`render_baremetal_first_frame` → `src/os/desktop/shell.spl:1000-1006`, which calls
`render_baremetal_frame` (`shell.spl:971-998`). That function's six steps are:
`runtime_scene_snapshot`, `runtime_taskbar_model`, `runtime_scene_revision`,
`runtime_taskbar_revision`, **`runtime_content_frames(scene_revision)`
(`shell.spl:1295`)**, then `executor.render(...)`
(`src/os/compositor/engine2d_wm_frame_executor.spl`).

`runtime_content_frames` is what drives the `simple_web` browser-engine renderer
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer*.spl`)
and the Engine2D CPU glass composite
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:508
_engine2d_draw_ir_render_glass_material`, called from `:698` inside
`_engine2d_draw_ir_render_commands` at `:1420`). **That is where the run dies.**

---

## 2. Archived-log evidence (per-run copies only)

Canonical `serial.log` is racy; everything below is read from
`build/simpleos_wm_fullscreen_evidence/runs/<ts>/serial.log`.

Census of every archived run (all fail):

| run | serial bytes | `[scanout-evidence]` | `[production-readiness]` | fault frames |
|---|---|---|---|---|
| 20260810T073848Z | 20911 | 1 | **0** | 2 |
| 20260810T074249Z | 16154 | 1 | **0** | 2 |
| 20260810T074701Z | 16318 | 1 | **0** | 2 |
| 20260810T075519Z | 20911 | 1 | **0** | 2 |
| 20260810T080431Z | 21678 | 1 | **0** | 2 |
| 20260810T082051Z | 21679 | 1 | **0** | 2 |
| 20260810T083128Z | 21831 | 1 | **0** | 8 |
| 20260810T112327Z | 21168 | 1 | **0** | 8 |

`build/simpleos_wm_fullscreen_evidence_provlane/runs/*` contain **no `serial.log` at
all** — do not use them.

Caveat for the implementer: in `20260810T112327Z-fail` the directory mtime is
11:23 but `serial.log`'s mtime is **08:46**. Archived runs can carry a serial log
older than the directory stamp. Always check `stat -c %y <run>/serial.log`.

### Most recent run, `20260810T112327Z-fail`, at the decisive point

Boot is healthy right up to the paint:

```
148:[scanout-evidence] address=2147483648 width=3840 height=2160 stride=15360 pixel_format=argb8888 generation=1 device_id=45253 pci_found=1 pci_device=1 framebuffer_bar=2147483648 mmio_bar=2214682624 pci_decode=1
152:[desktop-gui] framebuffer ready width=3840 height=2160 pitch=15360
153:[desktop-gui] engine2d-ready backend=baremetal-framebuffer persistent=true
164:[desktop-gui] compositor ready
170:[desktop-gui] shell initialized
191:[desktop-gui] materialize return app=Browser Demo ok=1 owned=1
212:[desktop-gui] materialize return app=Hello World ok=1 owned=2
233:[desktop-gui] materialize return app=Clang ok=1 owned=3
234:[desktop-gui] process-owned-surfaces-ready count=3
235:[desktop-gui] launcher apps=15
236:[wm-frame] host-gpu-fallback reason=unavailable-or-readback-capacity width=3840 height=2160
237:HOST_GPU_NEGOTIATION_DONE scope=production isa=x86_64 result=fallback backend=software attempts=0 ... elapsed_us=16416 budget_us=500000 reason=1
```

Line 235 (`launcher apps=15`, `gui_entry_desktop.spl:569`) is **the last
progress marker in the whole log.** Everything after it is inside
`render_baremetal_first_frame`.

Then, three times over, the browser-engine style/measure pass runs:

```
238:[web-style-producer] contract-attr index=4 attrs_len=219 raw_len=14 trimmed_len=14 lower_len=14 raw_match=1 final_match=1
...  [rfm] at=default-font / renderer-bound / cache-lookup / measure / measured advances=N
255:[web-style-producer] cpu-entries-ready count=1 len=368
...
268:[web-material-provenance] witness-unconverted cpu_witness=1 cpu_executed=0 metal_executed=0 sha_len=64 target= readback=
269..291:[heap] alloc sz=0x1dc020 ... (x5)  /  [array-repeat] big count=0x100000 caller=0x83d27fe (x3, 8 MiB each)
```

Counts in this log: `cpu-entries-ready` = 3, `witness-unconverted` = 2,
`contract-attr` = 3, `array-repeat` = 6. So three content-frame passes are
attempted (one per owned surface), each allocating ~2 MiB of style buffers plus
3 x 8 MiB `array-repeat` pixel buffers on a **never-freeing bump heap**.

Then the faults, and then silence:

```
[fault] *** EXCEPTION FRAME ***
[fault] rip=0x000000000800434e      <- memcpy
[fault] errcode=0x0000000000000000
[fault] cs=0x0000000000000008
[fault] rflags=0x0000000000200093
[fault] cr2=0x000000037b49f261
[fault] cr3=0x0000000048709000
[fault] *** END FRAME (recovering) ***

[fault] *** EXCEPTION FRAME ***
[fault] rip=0x0000000008004350      <- memcpy+2
[fault] cr2=0xffffffffffffff8e      <- wild: -0x72, i.e. a negative index off a null-ish base
[fault] *** END FRAME (recovering) ***
```
…and the final line of the file is `[rfm] at=default-font family=sans-serif`
(line 415). No `[desktop-gui] first-frame-rendered`, no
`[production-readiness-failed]`, no `desktop-ready`. The guest is killed by the
gate's 300 s readiness timeout while still inside the first frame.

### The page fault is **NOT** resolved — correct the working premise

`rip=` distribution, identical in the two newest runs:

```
20260810T083128Z:  3x 0x800434e  3x 0x8004350  1x 0x8004bc0  1x 0x8004bc2
20260810T112327Z:  3x 0x800434e  3x 0x8004350  1x 0x8004bc0  1x 0x8004bc2
```

`0x8004bc0/0x8004bc2` is `rt_string_concat` and `0x800434e/0x8004350` is `memcpy`
— exactly the "layer 3" signature recorded in
`doc/08_tracking/bug/freestanding_text_local_recompare_flips_material_admission_2026-08-10.md`
(§ *Layer 3 (OPEN)*). **Both are still present in the newest archived run.** Any
statement that the `rt_string_concat`/`memcpy` fault is fixed is contradicted by
the archived evidence; it is unchanged between 08:29 and 08:46.

### Landed-fix verification (blob-level, against origin)

Fetched `refs/heads/main` from `git@github.com:ormastes/simple.git` →
`e55efe888b674ede8258cffe6f99bff740aec588`.

* `4f755fdeb93` (AggregateCopy struct deep-copy) — **ancestor of origin/main: YES**
* `2009e71905e` (AOT GetField f64) — **YES**
* `e99a5b76d11` (recovery of 101 clobbered files) — **YES**
* `c28e1b008b02` (cascade→layout) — **YES**

Blob check: `git cat-file -p e55efe888b:src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
contains `deep_fields: &[crate::mir::AggregateFieldCopy]` (`:400`, `:429`) and the
`for field in deep_fields` loop (`:456`). The fix is at origin.

**TRAP FOR THE IMPLEMENTER:** the local checkout is *behind* on that file.
Local `HEAD` (`1a95cee59c9`, "revert: drop accidental inclusion of
closures_structs.rs from doc-restore commit") plus the working copy leave
`closures_structs.rs` **46 lines short** of origin
(`git diff --stat e55efe888b -- <that file>` → `5 insertions(+), 46 deletions(-)`).
None of `4f755fdeb93 / 2009e71905e / e99a5b76d11` is an ancestor of the local
`HEAD`. **Sync to origin/main and confirm that blob before building anything**,
or you will rebuild a kernel without the struct deep-copy fix and mis-attribute
the result.

---

## 3. Classification: (a)/(b)/(c)/(d)?

**Primary: (d).** The whole capture stage is gated on a guest marker
(`[production-readiness]`) that is a *precondition* by construction
(`check-simpleos-wm-fullscreen-evidence.shs:1327-1330`, `:1361-1362`). The
precondition is never satisfied, so `scanout_size` never leaves its `:1221`
initialiser and the python capture block at `:1388` never runs.

**Proximate cause of (d): (c).** The capture-enabling code *does* run and *does*
fail: `render_baremetal_first_frame` (`shell.spl:1000`) is entered — proven by
the `[web-style-producer]` / `[rfm]` / `[web-material-provenance]` traffic that
only that call can produce — and never returns. It faults in `memcpy` /
`rt_string_concat` with wild `cr2` and is then killed by the readiness timeout.

**Explicitly NOT (a):** capture is correctly wired; it is downstream of the
marker by design, and the design is deliberate — `gui_entry_desktop.spl:582-585`
states the frame must be painted *before* readiness so the baseline capture
cannot race an unpainted scanout.

**Explicitly NOT (b):** capture code exists and is complete
(`pmem()` → `pmemsave` → argb8888→P6 conversion, `:1434-1455`).

---

## 4. Desktop-readiness markers: meaning, and the "painting isn't implemented" hypothesis

The gate's required set (mirrored in `src/os/desktop_qemu_contract.spl:110-119`,
`wm_simple_web_required_marker_fragments`):

| marker | means | status in latest run |
|---|---|---|
| `[scanout-evidence] address=` | BGA/PCI scanout decoded (`bga_init.spl:76,296`) | **present** |
| `[desktop-gui] engine2d-ready` | Engine2D bound to the baremetal framebuffer | **present** |
| `[desktop-gui] shell initialized` | DesktopShell constructed | **present** |
| `[desktop-gui] process-owned-surfaces-ready count=3` | 3 apps spawned via syscall 13 and materialized as compositor-owned surfaces | **present** |
| `[desktop-gui] desktop-ready` | first frame painted + SIMD receipt + font evidence emitted | **absent** |
| `[production-readiness] ...` | all of the above | **absent** |

"input/IRQ/frame/browser-content readiness" (`[wm-input-irq]`, `[wm-state]`,
`[wm-frame]`, `[remote-browser-content-presented]`) are emitted from the
**event loop** `run_baremetal` (`shell.spl:1008+`; the browser-content receipt at
`shell.spl:~1070`, `[remote-browser-ready]` just below). `run_baremetal` is
called at `gui_entry_desktop.spl:628` — **after** the readiness markers.
They are empty for a trivial reason: **the guest never gets there.** They are
not an independent failure and not a precondition for anything.

### Hypothesis "readiness needs real painted content and painting is unimplemented" — **REFUTED**

Evidence against:

1. Painting *is* implemented and *is* executing. The three
   `[web-style-producer] cpu-entries-ready count=1` passes, the `[rfm]` text
   measurement receipts, the 8 MiB `array-repeat` pixel-buffer allocations and
   the CPU glass composite all belong to the real paint path. The failure is a
   **crash inside painting**, not absence of painting.
2. `c28e1b008b02` (cascade→layout) is an ancestor of origin/main and the layout
   stage demonstrably runs (it is what feeds `[rfm] measured advances=`).
3. Readiness does **not** require *successful* content painting. The executor
   tolerates fully-degraded windows:
   `engine2d_wm_frame_executor.spl:277-283` counts `degraded_window_count`, and
   `:284-287` compares against `renderable_images = expected_images -
   degraded_window_count`. A frame in which *every* window degrades still
   satisfies the coverage check and can return a positive revision, so
   `first_frame_revision > 0` and readiness fires with chrome-only content.
   Earlier archived runs prove this path is live: they emit
   `[wm-frame] content-provenance-rejected` and
   `[wm-frame] window-degraded reason=unresolved-or-duplicate-content` without
   aborting the frame.

So: readiness is blocked by a **freestanding-codegen memory-corruption bug in
the content-frame paint path**, not by a missing paint feature.

---

## 5. Minimum viable path to rung (d)

Goal: a run in which `[production-readiness]` is printed, `pmemsave` executes,
and `baseline.ppm` is a real 3840x2160 P6 with **non-uniform** pixels — proving
scanout + compositor + capture end to end, *without* fixing the browser-content
corruption first.

The smallest change is **not** "draw a test rect". It is **stop calling the
crashing stage for the first frame** and let the already-working WM chrome path
paint. The desktop background, three window frames + titlebars, and the taskbar
are more than enough to make the PPM non-uniform.

### Recommended change (one flag, two call sites)

1. **`src/os/desktop/shell.spl`**
   * Add a module-level `val _WM_CONTENT_FRAMES_ENABLED: bool = false` next to
     `val _WM_TRACE: bool = false` (`shell.spl:99`), ideally read from a
     generated config (`build/os/generated/generated/simpleos_log_config.spl`,
     written by the gate at `check-simpleos-wm-fullscreen-evidence.shs:936`) so
     it can be flipped without editing source.
   * In `render_baremetal_frame` (`shell.spl:971-998`), line 990, replace
     `val content_frames = self.runtime_content_frames(scene_revision)` with a
     guarded form that yields an empty `[WmContentFrame]` when the flag is off.
     Every window then takes the `if not resolved` branch at
     `engine2d_wm_frame_executor.spl:277-281`, `degraded_window_count ==
     expected_images`, `renderable_images == 0`, `images.len() == 0` → coverage
     check at `:284` passes → composition proceeds with chrome only.
   * `self.host_gpu_required` must be **false** for `:286-288` not to reject on
     degraded windows. It already is: `gui_entry_desktop.spl:581` passes
     `backend_required: false` explicitly, and the run logs
     `[wm-frame] host-gpu-fallback reason=unavailable-or-readback-capacity`.

2. **Flip `_WM_TRACE` to `true` for the diagnostic run**
   (`shell.spl:99`, plus the executor's `_WM_TRACE` receipts at
   `engine2d_wm_frame_executor.spl:250-282`). This is the single highest-value
   observability change available: it prints
   `[wm-render-step] at=scene-snapshot | taskbar-model | scene-revision |
   taskbar-revision | content-frames | executor-render | done rendered=N`, which
   converts "the log goes quiet" into a named step. The `render_baremetal_frame`
   docstring (`shell.spl:972-979`) already records a prior instance of exactly
   this "render never returns" pattern being localised that way.

3. **If a literal test pattern is still wanted** as the belt-and-braces oracle,
   the cheapest honest one is a solid fill plus one contrasting rect written
   straight to the framebuffer through `FramebufferDriver`
   (already in hand at `gui_entry_desktop.spl:424` as `fb`), emitted between
   `:428` (`framebuffer ready`) and `:429`. Two colours in known rectangles make
   the PPM verifiably non-uniform and let you distinguish "capture works" from
   "compositor works". Do this **only** if step 1 does not produce a non-uniform
   PPM — it proves less.

### Expected post-change log (the acceptance oracle)

```
[desktop-gui] launcher apps=15
[wm-frame] host-gpu-fallback ...
[wm-frame] window-degraded window_id=... reason=unresolved-or-duplicate-content   (x3)
[desktop-gui] first-frame-rendered scene_revision=<N>            <- shell.spl:1005, N > 0
[engine2d-simd] arch=x86_64 isa=sse2 enabled=1 fill_hits=... fill_chunks=...
[font-evidence...]
[desktop-gui] desktop-ready
[production-readiness] wm=live ... scanout_generation=1
```
then, host-side: `simpleos_wm_fullscreen_scanout_capture_size=33177600`
(= stride 15360 x height 2160) and four PPMs of `3840*2160*3 + 15 = 24883215`
bytes each.

### Risks / things that will still fail after this

* `[engine2d-simd] fatal ... reason=zero-runtime-receipt`
  (`gui_entry_desktop.spl:597-600`) hard-exits via `port_outb(0xF4,1)` if the
  SIMD fill never ran. A chrome-only frame does still fill large regions, so
  this should be satisfied — but it is the next hard gate after the frame.
* The F11 maximize/restore and browser-event PPM comparisons later in the gate
  will still fail without content painting. **That is expected and correct** —
  the minimum path targets *baseline capture* (rung d), not full acceptance.
* Do **not** weaken any check in `check-simpleos-wm-fullscreen-evidence.shs` to
  get there. The flag belongs in the guest, is off by default in production, and
  the run that uses it must be reported as a diagnostic run, not a gate pass.

### The real fix, for whoever takes it after rung (d)

Reduce the `memcpy` (`0x800434e`) / `rt_string_concat` (`0x8004bc0`) fault inside
`_engine2d_draw_ir_render_glass_material`
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:508`, called from `:698`
within `_engine2d_draw_ir_render_commands` `:1420`) and
`engine2d_draw_ir_glass_material_pixels`. `cr2=0xffffffffffffff8e` is a small
negative offset from a null-ish base — a length/index computed as -1 and used
unsigned, or a struct field read at the wrong index (the same
field-index-collision class as layer 2 in the bug doc). The tracking anchor is
`doc/08_tracking/bug/freestanding_text_local_recompare_flips_material_admission_2026-08-10.md`
§ *Layer 3 (OPEN)*; that section should be updated to record that the fault
persists as of run `20260810T112327Z`.

---

## Appendix — reproducing this analysis without a build

```sh
cd /home/ormastes/dev/pub/simple
R=build/simpleos_wm_fullscreen_evidence/runs/20260810T112327Z-fail/serial.log
stat -c '%y' "$R"                                  # archived logs can predate their dir
/usr/bin/grep -n 'desktop-gui\|scanout-evidence\|web-\|rfm\]' "$R" | tail -40
/usr/bin/grep 'rip=' "$R" | sort | uniq -c
/usr/bin/grep -c 'production-readiness' "$R"       # expect 0
sed -n '1221p;1312p;1327,1336p;1359,1390p' scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```
Use `/usr/bin/grep` — the wrapped `grep` on PATH is ugrep honouring `.gitignore`
and will not see anything under `build/`.

## 2026-08-10 addendum — page-fault-as-blocker claim SUPERSEDED

This document's § "The page fault is **NOT** resolved — correct the working
premise" and its "Primary: (d) ... first-frame paint [faults on
memcpy/rt_string_concat]" classification are **SUPERSEDED**. Wider evidence
across the archived run set (13 runs, not the 2 examined here) shows this
`memcpy`/`rt_string_concat` page fault **self-recovers** — the serial log's own
`*** END FRAME (recovering) ***` marker, present in both runs quoted above,
means execution continued past it. Only 2 of 13 archived runs show the fault
at all, so it cannot be the rung-(d) blocker on its own evidentiary terms (it
is absent from the majority of runs that still failed to reach rung (d)).

The actual rung-(d) blocker was `render_baremetal_first_frame` never
returning — a TIMEOUT (the guest is killed by the gate's 300 s readiness
timeout, exactly as this document itself observes: "the guest is killed by
the gate's 300 s readiness timeout while still inside the first frame") that
the gate misclassified as `reason=guest-render-fault`/
`reason=dynamic-scanout-or-desktop-readiness-missing`. Root cause: the
font-atlas 8 MiB buffer being reallocated on every reset
(`_reset_font_atlas`, `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`),
exhausting the 1 GiB baremetal bump heap before the render loop could
complete a frame — consistent with this document's own § 2 observation of
repeated `[array-repeat] big count=0x100000` (8 MiB) allocations on "a
never-freeing bump heap". Fixed by commit `4e1d05ba67a4` ("fix(simpleos):
reuse font atlas buffer in place instead of leaking 8MiB per reset"). See
`doc/08_tracking/bug/freestanding_text_local_recompare_flips_material_admission_2026-08-10.md`
(Layer 5 + 2026-08-10 addendum) for the full chain.

This correction does not touch this document's separate, still-accurate
finding that the local checkout was behind origin on
`closures_structs.rs` — that trap-for-the-implementer note stands.
