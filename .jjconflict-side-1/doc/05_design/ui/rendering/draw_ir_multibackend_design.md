<!-- opus-design 2026-07-06 -->
# Draw-IR Multi-Backend Rendering — Design

**Companion research:** `doc/01_research/ui/rendering/draw_ir_multibackend_research.md`.
**Principle:** one Draw-IR, one dispatch point, one interface, **one software reference oracle**;
GPU/SIMD backends **override only what they accelerate** and fall through to the shared reference
for everything else, with **capability-honest** naming and readback. No inheritance — composition
and delegation only (repo rule). No parallel trait — we rationalize the existing `RenderBackend`.

---

## Verification record (2026-07-06)

Two independent checks — an adversarial verification pass and a separate backend coherence audit —
reviewed this design against the actual source. Outcome: **D1, D2, D4 reviewed and
APPROVED_WITH_CHANGE**; **P1 is GO, gated on a new bit-exact harness prerequisite** (§3b); **mixin
stub-elimination is deferred to a new feature, FR-RENDER-MIXIN** (§3a) — both probes confirmed the
shipped compiler does not auto-forward trait/mixin methods today, so eliminating the ~191
hand-written forwarding stubs is not a free refactor. Corrected facts folded in below: the shared
reference is **28** `emu_draw_*` functions (23 in `backend_emu.spl` + 5 in `backend_emu_adv.spl`,
not "~34"); forwarding boilerplate is **~191** stubs (not "~300"), and the boilerplate-reduction
case for the mixin was overstated by ~57%; the blend reference `_emu_blend_over` is defined at
`backend_emu_math.spl:33` (backend_emu.spl:642 is only the call site). A deeper coherence audit
also surfaced honesty/dedup debt not previously captured here — see research §9 and plan
P1/P2/P3 — covering a live-dishonest WebGPU backend, vaporware Intel/OpenGL, the `cpu_simd` bare
alias, orphaned fabricated-FFI files, a `RenderBackend` naming collision plus three dead
shared-interface attempts, and the `Engine2D` facade's dead 3-way branch with its two disagreeing
backend-selection paths.

---

## 1. Canonical layering (target)

```
UI / WM / web layout / browser_engine
        │  emit
        ▼
Draw-IR:  RenderScene / SceneCommand   (extended — §6)          common/render_scene/scene.spl
        │  the ONLY serializable source of truth for a frame
        ▼
Executor: execute_scene_to_engine2d    (single dispatch point; complete replay — §6)
        ▼
Facade:   Engine2D  (capability-aware backend selection — §4)
        ▼
Interface: trait RenderBackend  (ONE interface — §2)
        ▼
   ┌─────────────────────────────────────────────────────────────┐
   │ SharedRaster  (mixin/free-function reference — §3)           │  ← the parity oracle
   │   every Draw-IR op implemented over draw_rect_filled + fb    │
   └─────────────────────────────────────────────────────────────┘
        ▲ delegate unaccelerated ops          ▲ override accelerated ops
        │                                      │
   software / cpu / directx / …          metal / vulkan / cuda / cpu_simd / …
   (accelerate nothing → all shared)     (declare accelerated set; rest → shared)
```

---

## 2. ONE interface (resolve the three-trait drift)

**Decision D1 — collapse to a single trait `RenderBackend` + a capability descriptor; retire the
Core/Adv split as *dead code*. Status (2026-07-06): APPROVED_WITH_CHANGE.**

Rationale (from research §2): every backend already implements the flat `RenderBackend`; **nothing**
implements `RenderBackendCore`/`RenderBackendAdv`; the "implement Core, get Adv free" promise is
un-enforced. Rather than keep three traits and hope, we encode the same idea *correctly* with:

1. **`RenderBackend`** stays the sole trait every backend implements. Its method set = the union
   the executor needs to replay a complete scene (clear, fills, primitives, gradient, text, image,
   clip stack, mask, transform, present, sized readback). This is the **contract**.
2. A backend is **not required to accelerate** any op — the *shared reference* provides a correct
   body for all of them (§3). "Implement only what you accelerate" becomes true because the shared
   reference supplies the rest via delegation, not via a trait-inheritance trick the language
   forbids.
3. `RenderBackendCore` / `RenderBackendAdv` / their `.spl` files are **deleted** (or reduced to a
   doc note) once §3 lands — they encode a contract the shared reference now enforces at the
   call-forwarding layer. `Engine2DExtended` (`draw_text_bg`) folds into `RenderBackend` as an
   ordinary op with a shared body.

**Change folded in (coherence audit, research §9):** `RenderBackendCore`/`RenderBackendAdv` are not
the only dead shared-interface attempts to retire — `ComputeSession` (backend_session.spl:78-95,
zero implementations) and the textual copy of the whole `RenderBackend` trait in
`nogc_async_mut/gpu/engine2d/backend.spl` (byte-for-byte duplicate, separate nominal type, no
facade re-export) should be retired/reconciled in the same pass (plan P1). Also note: this pixel-level
`RenderBackend` shares its name with an unrelated widget-tree trait in `common/ui/backend.spl:22-40`
(implemented by `fb_backend.spl`/`browser_backend.spl`) — the naming collision must be resolved
(one side renamed) before/early in the unification work so greps and refactors during P1-P6 are
unambiguous (plan P1).

**Method surface of the unified `RenderBackend`** = current `RenderBackend` (backend.spl:21-44)
**plus** `capability() -> BackendCapability` (§4) **plus** the IR-completeness ops the executor must
be able to call (`draw_triangle_filled` already present; add `push_clip`/`pop_clip` stack form,
`set_transform`, `draw_glyph_run`, `draw_gradient_stops`, `draw_rect_blend_mode` — §6). Ops a
backend does not accelerate are satisfied by the shared reference (§3), so widening the trait costs
backends nothing.

---

## 3. Shared-logic layer — `SharedRaster` (the parity oracle)

**Decision D2 — `backend_emu.spl` becomes THE canonical software reference (`SharedRaster`); it is
the single bit-exact parity oracle. `backend_software.spl` is refactored to *be* that reference
plus SIMD span overrides — it stops being a second, independently-drifting implementation. Status
(2026-07-06): APPROVED_WITH_CHANGE — promotion to oracle is gated on the bit-exact harness in §3b,
and the mixin-based stub elimination in §3a is deferred (see below).**

### 3a. Shape (composition, not inheritance)

`SharedRaster` is a **mixin over `draw_rect_filled` + framebuffer access**. It is the set of
stateless functions already in `backend_emu.spl` (`emu_draw_*`), promoted to the canonical library
and re-parented from the flat trait onto the minimal core surface:

- **Core surface a backend must supply** (the irreducible kernel — matches today's
  `RenderBackendCore` intent, backend_core.spl:23): `clear`, `draw_rect_filled`, `draw_image`,
  `set_clip`/`clear_clip`, `set_mask`/`clear_mask`, `present`, `read_pixels`, `width`, `height`.
- **Everything else** (`draw_rect`, `draw_line`, `draw_circle[_filled]`, `draw_rounded_rect`,
  `draw_triangle_filled`, `draw_gradient_rect`, `draw_text`, blend variants, transforms, gradients,
  blur/shadow, polygons) has a `SharedRaster` reference body composed from that core surface —
  already written in `backend_emu.spl` + `backend_emu_adv.spl`.

A backend gets shared behavior by delegating: for each non-core op the backend does not accelerate,
its method body is a one-line call to the `SharedRaster` **free function**, passing `self` as the
first argument — `me draw_circle_filled(...): shared_draw_circle_filled(self, ...)`. There is no
`emu`/`shared` field on the backend struct; this is a plain free-function call, not a method call
through a composed object.

**Mixin auto-forwarding is confirmed infeasible with today's shipped compiler — this is a critical
change from the original design intent, not a stylistic detail.** Two independent empirical probes
verified: the alias/mixin desugar pipeline (`src/app/desugar/forwarding.spl`, a five-pass text-level
rewrite: forwarding-alias generation, static-constant/method extraction, enum-constructor
generation, call-site rewriting — `src/app/desugar/mod.spl:1-16`) is exposed only as an **explicit,
manually-invoked CLI subcommand** (`bin/simple desugar <file>`, `file_delegation` to
`app/desugar/mod.spl`, wired at `main_and_help.spl:312`) — it is **not** wired into the normal
build/compile pipeline: `create_default_services()` (`compiler_services.spl:200-247`) wires every
real build's `desugarer:` port to `_make_noop_desugarer()`/`_noop_desugar` (`compiler_services.spl:157`,
docstring: "Wiring to real pipeline stages is done incrementally... Phase 2 of MDSoC migration"),
and there is no other `desugarer:` override anywhere in `src/`. So an `alias`/mixin `include`
declaration written in ordinary backend source is **not** expanded by `bin/simple build`/`test`/
`run` — a developer would have to manually pre-run `bin/simple desugar` per file, per edit, which
is not "free" and does not match the composition-helper workflow this section originally described.
The originally-proposed **`SharedRasterMixin` composition helper does not exist and cannot be made
to auto-forward trait methods today.** Eliminating the ~191 hand-written forwarding stubs (research
§9, corrected count) is therefore **removed from P1** and re-filed as a separate feature,
**FR-RENDER-MIXIN**: wire `src/app/desugar` into the compiler front-end (not just the standalone
CLI subcommand); the offline desugar as it stands today **drops return-type annotations** during
its rewrite, which would silently break a strictly-typed native backend — the fix must **preserve**
them; add an end-to-end test using `alias` with **zero hand-written stubs** as proof the wiring
works. FR-RENDER-MIXIN is a **prerequisite for a later stub-cleanup phase**, not part of P1 (plan
P1 note). Until it lands, backends keep hand-writing the ~191 forwarding stubs shown above —
unchanged from today, just no longer mis-costed as free.

### 3b. Bit-exact contract (the oracle)

The shared reference defines the **canonical pixel math**; every backend's accelerated path must
match it bit-for-bit on readback. The blend primitive is `_emu_blend_over`, **defined at
`backend_emu_math.spl:33`** (backend_emu.spl:642 is only the call site, `emu_draw_rect_blend`,
straight src-over on ARGB u32). The contract, restated as an acceptance invariant:

> For any scene S and any backend B, `B.read_pixels(S)` **==** `SharedRaster.read_pixels(S)`
> pixel-for-pixel, where equality is exact u32 ARGB match. Example anchor (src-over,
> 0xAARRGGBB): `blend_over(src=0x01020304, dst=0x10203040) == 0x101F2F3F`.

This makes the shared reference the **single oracle**: parity gates compare every backend against
`SharedRaster`, not against each other, so there is exactly one truth. Any op a backend does not
accelerate trivially passes (it *is* the oracle). Accelerated GPU ops must be validated against it.

**Duplicate blend implementation to unify:** `color.spl`'s `blend()` and `backend_emu_math`'s
`_emu_blend_over` are **byte-identical duplicate src-over copies**, independently confirmed against
the same anchor (`0x01020304` over `0x10203040` == `0x101F2F3F`). Promoting `_emu_blend_over` to
canonical means deleting `color.spl`'s copy and routing both consumers through the one reference —
do not leave two source-identical implementations that can drift apart on a future edit to only one
of them.

**Prerequisite gate before promoting `backend_emu` to the oracle (critical addition, not optional):**
`backend_software.spl`'s ~9 core ops (`rect`, `line`, `circle`, `circle_filled`, `rounded_rect`,
`triangle_filled`, `gradient_rect`, `text`, `text_bg` — e.g. `draw_circle` at
backend_software.spl:227) are **independently hand-written**, not derived from or previously proven
equal to `backend_emu`'s reference math. Promoting `backend_emu` to *the* `SharedRaster` oracle is
therefore **not automatically behavior-preserving** for any backend (including `software` itself)
that currently ships its own core-op bodies. Before any core op is switched to delegate to
`SharedRaster`, a **bit-exact validation harness** (emu vs. software, per op) must pass; where the
two diverge, the design does not presume `backend_emu` wins by default — pick the canonical
algorithm **per op** based on the harness result. This harness is being built now at
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` and is a **prerequisite gate
in plan P1**, ahead of any core-op delegation switch.

### 3c. Consolidating the two references

`backend_software.spl` today re-derives fills and owns SIMD hooks. Under D2 it becomes:
`SoftwareBackend` supplies the **core surface** (owns the framebuffer, implements `draw_rect_filled`,
`draw_image`, clip, mask, subject to the §3b harness gate above) with **SIMD span kernels** on the
hot core ops; higher-level ops delegate to `SharedRaster` via the same free-function calls every
other backend uses (no inheritance — composition only, per repo rule). There is then **one**
algorithm for circle/triangle/gradient (in `SharedRaster`), fed by either scalar or SIMD
`draw_rect_filled`/span fills underneath. No second oracle.

---

## D2 op-consolidation roadmap (empirical equality matrix, 2026-07-06)

The §3b prerequisite gate has now run: the P1 structural unification (single `RenderBackend`
trait, dead-trait deletion, `BackendCapability`/`ReadbackSource` enum, unified src-over blend) has
landed and was verified CLEAN, and the committed bit-exact parity harness
(`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`) ran every Draw-IR op
through both `backend_emu`/`backend_emu_adv` (the emu oracle candidate) and `backend_software.spl`
(sw) and diffed the resulting pixel buffers per op. This section is the resulting **empirical
per-op equality matrix** with a named canonical winner for each divergence — it is the direct
implementation roadmap for the next increment (op-by-op consolidation onto `SharedRaster`, §3a/§3c).

### Equality matrix

| Op | Δ (px) | Verdict | Canonical winner | Note |
|---|---|---|---|---|
| `clear` | 0 | BIT-EXACT | n/a — single-source already | core primitive |
| `draw_rect_filled` | 0 | BIT-EXACT | n/a — single-source already | core primitive |
| `draw_image` | 0 | BIT-EXACT | n/a — single-source already | core primitive |
| `draw_gradient_rect_h` | 0 | BIT-EXACT | n/a — delegating stub | already routes through the shared fill |
| `draw_rect_blend` | 0 | BIT-EXACT | n/a — delegating stub | src-over anchor `0x01020304` over `0x10203040` == `0x101F2F3F` (§3b anchor) |
| `draw_image_blend` | 0 | BIT-EXACT | n/a — delegating stub | same src-over anchor as `draw_rect_blend` |
| `draw_rect` (OPAQUE outline repr.) | 0 | BIT-EXACT *for this representative only* | — | alpha=255 only; alpha<255 diverges, see below |
| `draw_gradient_rect` (OPAQUE repr.) | 0 | BIT-EXACT *for this representative only* | — | integer lerp; only exact at the opaque representative |
| `draw_line` (THIN repr., thickness<=1) | 0 | BIT-EXACT *for this representative only* | — | only exact at thickness<=1; thick diverges, see below |
| `draw_rect` (alpha<255 outline) | 96px | DIVERGENT | **EMU** | route sw's outline edges through the blending fill (`draw_rect_filled`) instead of raw `sw_hline`/`sw_vline` writes |
| `draw_line` (thick, e.g. thickness=3) | 58px | DIVERGENT — **no canonical** | **deferred** | sw = parallel-offset Bresenham strokes (114px); emu = t×t filled square stamped per Bresenham point (172px overdraw). Needs a design decision, not an auto-pick |
| `draw_circle` (outline) | 32px @ r=9 | DIVERGENT | **EMU body + SW guard** | emu's textbook midpoint body (`d<0`) for r>=1, **plus** sw's `r<=0` no-op guard (drop emu's stray center pixel) |
| `draw_circle_filled` | 40px @ r=15, grows with r | DIVERGENT | **SW** | exact per-row distance-test disk (isqrt), bit-exact with Metal `kernel_draw_circle_filled`; keep sw's `r<=0` no-op; replace emu's midpoint scanline |
| `draw_rounded_rect` | 604px | DIVERGENT | **EMU (FILL)** | sw draws an **OUTLINE** — a bug; a separate `_outline` method already exists. Being fixed now in a parallel task |
| `draw_triangle_filled` | ~1 boundary px + 16px on degenerate | DIVERGENT | **SW** | integer barycentric edge-function fill, bit-exact with Metal `kernel_draw_triangle_filled`; keep sw's `d==0` degenerate no-op; replace emu's y-sorted scanline |
| `draw_text` | 33px | DIVERGENT | **SW** | real 5x7 glyphs (`glyph_data`/`text_metrics`) + AA (`text_aa_blit_buffer`); `emu_draw_text` is a placeholder box **stub** and must never be the text reference. Being fixed now — emu delegates to `core.draw_text` |
| `draw_text_bg` | 43px | DIVERGENT | **SW** | same as `draw_text`; `emu_draw_text_bg` is a placeholder box stub |

Every divergent row above is a **behavior-changing** fix: landing it flips that op's harness
assertion from `> 0` to `== 0`. The three BIT-EXACT-for-representative rows (`draw_rect`,
`draw_gradient_rect`, `draw_line`) are byte-exact **only** for the opaque/thin case tested — their
non-representative cases are exactly the divergent rows listed immediately below them in the table.

### Two standout bugs surfaced

1. **`SoftwareBackend.draw_rounded_rect` draws an outline, not a fill** — the Draw-IR op is
   documented and used as a filled rounded rectangle everywhere else (emu, Metal); sw silently
   renders the outline variant instead, and a correct `_outline` method already exists separately.
   See `doc/08_tracking/bug/engine2d_software_rounded_rect_draws_outline_not_fill_2026-07-06.md`.
2. **`emu_draw_text`/`emu_draw_text_bg` are placeholder box stubs**, not text rendering — they must
   never be treated as the text canonical reference, which is why SW (real glyphs + AA) is the
   named winner for both text rows above, not EMU. See
   `doc/08_tracking/bug/engine2d_emu_draw_text_placeholder_box_stub_2026-07-06.md`.

(Both bug records are being filed by a parallel task alongside this roadmap.)

### Canonical-winner rule for D2

Adopt **EMU as the single reference** for op consolidation **except**: keep **SW** for
`draw_circle_filled`, `draw_triangle_filled`, `draw_text`, `draw_text_bg` (and all
degenerate/no-op guards on every op — e.g. `r<=0`, `d==0`); `draw_circle` (outline) takes **emu's
body plus sw's `r<=0` guard**; `draw_line` (thick) is **deferred pending a design decision** (no
canonical winner exists yet — see the matrix row above). This rule is what an implementer should
apply mechanically when routing each divergent op through `SharedRaster` in the next increment.

### D2 executed (2026-07-06)

Applied the canonical-winner rule above op-by-op. The parity harness
(`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`) stayed green
throughout (21 examples), with assertions flipped only where the fix was pixel-changing.

**Consolidated (behavior-preserving; harness assertion stayed `== 0`):**
- `draw_rect` (opaque outline) — `SoftwareBackend.draw_rect` now delegates to
  `emu_draw_rect(self, ...)`, same idiom as the existing `draw_rounded_rect` delegation.
- `draw_gradient_rect` (opaque) — `SoftwareBackend.draw_gradient_rect` now delegates to
  `emu_draw_gradient_rect(self, ...)`.
- `draw_gradient_rect_h`, `draw_rect_blend`, `draw_image_blend` were found already
  consolidated (sw already delegates to the emu free function) — no action needed.
- `clear` / `draw_rect_filled` / `draw_image` have no independent emu reimplementation to
  consolidate against (emu builds ON these core primitives) — no action possible or needed.
- `draw_line` (thin, thickness<=1) — **left unconsolidated, by design**: emu's per-point body
  re-enters `core.draw_rect_filled(cx, cy, 1, 1, color)` for every Bresenham step (full
  clip/mask/dirty-span overhead per pixel), whereas sw's `sw_bresenham` uses the lean
  single-guard `sw_set_pixel` primitive. Consolidating would multiply per-pixel cost on long
  lines for zero behavior change, so this stays a documented exception (see comment at
  `backend_software.spl` `draw_line`).

**Reconciled toward the named canonical (pixel-changing; harness assertion flipped `> 0` → `== 0`):**
- `draw_rect` (alpha<255 outline) → **EMU**: came for free from the `draw_rect` consolidation
  above, since `emu_draw_rect` routes all four edges through `core.draw_rect_filled`, which
  already alpha-blends; sw's old hand-written edges wrote raw color and never blended.
- `draw_circle` (outline) → **EMU body + SW `r<=0` guard**: changed `SoftwareBackend.draw_circle`'s
  midpoint decision-variable test from `d <= 0` to `d < 0` (matching emu's textbook tie-break) for
  the `r > 0` loop only; the `r <= 0` no-op guard is untouched and stays sw-canonical (still
  diverges from emu's stray-center-pixel stamp — that sub-case was intentionally out of scope,
  see below).
- `draw_circle_filled` → **SW**: replaced `emu_draw_circle_filled`'s midpoint-scanline body with
  sw's per-row exact distance test (`_emu_isqrt(r*r - dy*dy)` half-width per row), Metal-exact;
  the `r <= 0` stray-center-pixel behavior in emu is untouched (also out of scope, see below).
- `draw_triangle_filled` (incl. the collinear `d==0` case) → **SW**: replaced
  `emu_draw_triangle_filled`'s y-sorted scanline algorithm with sw's integer barycentric
  bounding-box fill (Metal-exact), including sw's `d==0` no-op guard the old scanline algorithm
  lacked. Both the main-triangle and collinear-degenerate harness assertions flipped together
  since they share the one fix.

**Skipped, left divergent (unchanged):**
- `draw_line` (thick) — per guide: design decision pending, no canonical winner yet.
- `draw_circle` (`r<=0`) and `draw_circle_filled` (`r<=0`) — these two guard-only sub-cases were
  **not** in this increment's reconciliation list (only the `r>0` bodies were); emu still stamps a
  stray center pixel there vs sw's no-op. Left as their own tracked divergence for a future pass.

Files touched: `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`,
`src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`,
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`. (`gc_sync_mut`'s
`backend_software.spl`/`backend_emu.spl` are pure re-export facades onto the `gc_async_mut`
originals — no mirrored edit needed. `nogc_async_mut`/`nogc_sync_mut` have no copies of these
files.)

---

## 4. Capability + honesty model

**Decision D3 — every backend advertises a `BackendCapability` descriptor; `Engine2D` selects and
labels backends from it; readback source and `gpu_frame_complete` are computed uniformly in the
shared base, not hand-set per backend.**

```
class BackendCapability:
    name: text                 # honest, e.g. "metal", "directx-software-emulation", "cpu-simd-neon"
    class_: text               # "real-gpu" | "software-emulation" | "software-reference"
    device_present: bool       # a real device was opened (probe result)
    accelerated_ops: [text]    # op kinds this backend runs natively; all others → SharedRaster
    readback_source: text      # what read_pixels actually returns: "gpu-readback" | "software-fb"
```

Rules enforced by the shared base:
- `name` **must** disclose emulation when `class_ == "software-emulation"` (directx already does —
  backend_directx.spl:22; generalize to cpu, and any GPU backend that failed to open a device and
  fell back). **Concrete case to fix (research §9):** WebGPU's `init()` unconditionally returns
  `true` and `name()` always reports `"webgpu"`, with `probe_backend()` checking only `init()` and
  never `gpu_ready` (backend_webgpu.spl:227-252, engine.spl:382-387) — the same class of bug
  DirectX had before its fix, currently live. Bring WebGPU under this rule (plan P2).
- `readback_source` is set by the **actual** path taken (GPU present-then-readback vs shared-fb
  copy), not asserted. `Engine2DReadback.source` (backend.spl:5) is populated from it, closing the
  "claimed GPU while software fell back" hole (MEMORY 06-10).
- `gpu_frame_complete` (today metal-only, backend_metal.spl:215) becomes a **shared-base field**:
  set true only when *every* op in the frame was serviced by an accelerated path with a real
  device; any fall-through to `SharedRaster` on a real-GPU backend flips it false (metal already
  does this per-op — we lift the pattern into the base so vulkan/cuda get it identically).
- Selection: `Engine2D` picks the highest-priority backend whose `device_present` is true; if none,
  it selects `SoftwareBackend` (or `cpu-simd`) and the descriptor honestly says
  `class_ == "software-reference"`. `SIMPLE_2D_BACKEND` override (engine.spl) still wins but the
  descriptor still tells the truth about what got selected.

---

## 5. SIMD-CPU as a first-class backend (not a parallel one)

**Decision D4 — SIMD-CPU is the `SoftwareBackend` core surface with SIMD-accelerated span kernels;
it is selected as `cpu-simd` and declares `accelerated_ops = [fill spans, copy, alpha-blend]`. It
does not fork the higher-level raster logic. Status (2026-07-06): APPROVED_WITH_CHANGE.**

**Change folded in (research §9):** today `"cpu_simd"` is a **bare alias** for `"cpu"` —
`engine.spl:271-279` instantiates the byte-identical `CpuBackend.create()` for both, and the only
"SIMD" signal on the hot path is `record_simd_*_hit()` telemetry counters with no vector dispatch
behind them. Genuine NEON/AVX2 kernels **already exist**
(`nogc_sync_mut/gpu/engine2d/simd_kernels.spl:333-378`, real `extern`-backed C intrinsics; also
`rt_engine2d_simd_*`) but are unwired from `backend_software.spl`/`backend_cpu.spl`. D4 is therefore
**not** "write new SIMD kernels" — it is **"wire the existing real kernels into the hot path, and
fix the gate so it isn't NEON-only"** (the current arch-detection gate must also engage AVX2 on x86
hosts rather than falling through to scalar). Proof of execution must observe the **real vector
kernel actually running** (e.g. an instrumented call-count or return-value check on the
`simd_kernels.spl`/`rt_engine2d_simd_*` entry points) — **`record_simd_*_hit` counters are
explicitly discredited as proof**: they are exactly the fake-evidence pattern this project has hit
before (a counter increments with no vectorized code behind it) and must not be accepted as
sufficient by the plan's gate (plan P3).

- The hot kernels are `draw_rect_filled` (span fill), `draw_image` (copy), and alpha blend — exactly
  where `backend_software` already records `record_simd_{fill,copy,alpha}_hit` (research §5), which
  is telemetry only, not the acceptance evidence (see above).
- Arch dispatch (x86 SSE/AVX, arm NEON — genuine per MEMORY 06-03, riscv RVV) routes through the
  existing `simd_provider` probes; scalar fallback when no ISA span kernel is available.
- Because circle/triangle/gradient/text all funnel through `draw_rect_filled`/spans in
  `SharedRaster`, accelerating the spans accelerates **every** higher-level op with **zero** risk of
  parity drift — the algorithm is unchanged, only the innermost fill is vectorized. This is the
  cleanest possible "SIMD without a parallel backend."

---

## 6. Draw-IR completeness (make the scene the sole source of truth)

Extend `SceneCommand`/`RenderScene` and the **executor** so a serialized scene fully describes a
frame (research §6). Keep the single struct (no numbered splits); add kinds/fields:

| Add | Kind / field | Executor action |
|---|---|---|
| Clip **stack** | keep `clip_push`/`clip_pop`, define **intersection** stack semantics | maintain clip stack; backend `push_clip`/`pop_clip` |
| **Mask** | `mask_set` (pixels [u8], w, h) / `mask_clear` | `engine.set_mask` / `clear_mask` (trait already has these) |
| Gradient **stops** + direction | `gradient` gains `stops: [(offset,color)]`, `dir: text` (v/h/radial) | `draw_gradient_stops`; 2-color stays a fast path |
| **Transform / CTM** | `transform_set(a,b,c,d,tx,ty)` | `set_transform`; image/primitive ops apply it |
| **Glyph run** | `glyph_run(font, size, glyphs, x, y, color)` | `draw_glyph_run`; plain `text` stays a fallback |
| **Triangle / polygon** | `triangle`, `polygon(xs,ys)` | `draw_triangle_filled` / `draw_polygon_filled` |
| **Blend mode** | `blend_mode: i32` on paint ops | `draw_rect_blend_mode` |
| Fix replay holes | `blur_rect` (in IR, dropped by executor) | wire to `draw_blur_rect` |

The **executor stays the single dispatch point**; every new kind routes there. Default background
`clear` should be a scene command, not the hardcoded white (engine2d_executor.spl:31), so headless
replay is deterministic. (This gap, plus the `scene_blur_rect`-dropped-by-executor gap below, is
tracked in `doc/08_tracking/bug/engine2d_facade_dead_3way_branch_and_drawir_gaps_2026-07-06.md`.)

---

## 7. Adding a new backend — the seam

To add backend `Foo`, an implementer:
1. Implements the **core surface** (§3a): `clear`, `draw_rect_filled`, `draw_image`, clip, mask,
   present, `read_pixels`, `width`, `height` — validated against the §3b bit-exact harness.
2. **Today (until FR-RENDER-MIXIN lands):** hand-writes the forwarding stub for each non-core op it
   does not accelerate, one line each, calling the `SharedRaster` free function with `self` — the
   same ~191-stub pattern every current backend uses (§3a). **Once FR-RENDER-MIXIN lands:** includes
   the mixin instead and gets these for free. Either way, Foo is correct and passes the parity gate
   at this point.
3. Declares a **`BackendCapability`** (name, class, device_present probe, `accelerated_ops=[]`).
4. **Optionally** overrides individual ops with native kernels, adding each to `accelerated_ops`;
   each override must pass the bit-exact gate against `SharedRaster`.

"Implement 9 core methods + a capability descriptor, get a complete honest backend correct;
accelerate incrementally." That is the whole onboarding cost — **"free" applies to correctness**
(no per-op math to re-derive); the forwarding-stub *typing* cost is still hand-written today and
only becomes literally free once FR-RENDER-MIXIN lands (§3a).

- **DirectX/Vulkan/Metal/CUDA/etc.** each map their `accelerated_ops` to native kernels; everything
  else → `SharedRaster`. Metal/Vulkan (real GPU) keep their present+readback path and set
  `readback_source="gpu-readback"`; on any device-open failure they downgrade honestly to
  `software-emulation` and their name discloses it.

---

## 8. Web-lane fold-in (SIMPLE_WEB_GPU_PAINT)

The web GPU-paint path (research: emits `SceneCommand`s dispatched as per-primitive Metal calls,
parity kept via residual-vs-readback blit) is **already** a Draw-IR producer. Under this design it
stops being a special path:
- Its emitter produces the extended `RenderScene`; the **standard executor** replays it against the
  selected backend (Metal when present).
- Parity is no longer "residual-vs-readback blit" bookkeeping but the **standard shared-oracle
  gate**: web-lane Metal output is compared to `SharedRaster` on the same scene. The residual-blit
  becomes an optimization detail behind the capability descriptor, not a separate correctness story.
- `browser_engine/simple_web_layout_engine2d_fast.spl` and the HTML presenters become ordinary
  `Engine2D` clients.

---

## 8b. CPU/GPU dual-algorithm mechanism & GPU dictionary (cross-ref)

The per-op fork this design introduces via `BackendCapability.accelerated_ops` (§4) is extended into
an explicit **two-algorithm-set** mechanism (CPU bulk-idiom variant vs GPU data-parallel kernel,
selected per-op / per-`SIMPLE_2D_BACKEND` / per-`variants.ui.renderer`) plus a buffer-backed **GPU
dictionary** primitive (`lut_lookup` MSL fn + upload-only `GpuLut`, no new extern) in
`doc/05_design/ui/rendering/cpu_gpu_dual_algorithm_design.md` (research
`doc/01_research/ui/rendering/cpu_gpu_dual_algorithm_research.md`, plan
`doc/03_plan/ui/rendering/cpu_gpu_dual_algorithm_plan.md`). New accelerated ops (`indexed_fill`,
`glyph_atlas_blit`) inherit this section's parity oracle and add rows to the §D2 harness.

## 9. MDSOC+ placement & module layout

- **Reuse the existing `src/lib/gc_async_mut/gpu/engine2d/` directory** — no new numbered split, no
  `engine2d_v2` (repo rule). Files evolve in place:
  - `backend_emu.spl` (23 ops) + `backend_emu_adv.spl` (5 ops) → promoted to `SharedRaster`
    canonical reference; forwarding stays hand-written (~191 stubs) until **FR-RENDER-MIXIN** lands
    (§3a) — do not assume a `SharedRasterMixin` `include` exists yet.
  - `backend_core.spl` defines the **core surface** the (future) mixin needs; `backend_adv.spl`,
    `backend_session.spl`'s `ComputeSession`, and the textually-duplicated `RenderBackend` trait in
    `nogc_async_mut/gpu/engine2d/backend.spl` are retired/reconciled together (research §9, plan P1)
    once §2/§3 land — three dead attempts at this exact problem, not one.
  - New `backend_capability.spl` — the `BackendCapability` type + honesty helpers.
  - `backend_software.spl` → core-surface + SIMD spans only (higher ops from `SharedRaster`), gated
    on the §3b bit-exact harness before any core op switches to delegate.
  - `backend.spl` — unified `RenderBackend` (+`capability()`), `Engine2DExtended` folded in; resolve
    the naming collision with `common/ui/backend.spl`'s unrelated `RenderBackend` (plan P1, research
    §9) before/early in this work.
  - The dead 3-way `if val Some(vg) ... elif val Some(bm) ... else backend` branch across ~35
    `engine.spl` methods (e.g. `clear` :534-541) collapses to a single `self.backend` call — every
    constructor already sets all three fields to the identical object, so no behavior changes
    (plan P1). `backend_accel_{cuda,metal,vulkan}.spl` and `backend_{cuda,webgpu}_proof*.spl` are
    orphaned, fabricated-FFI files with no wiring into selection or the executor — quarantine/delete
    them rather than carry them forward (plan P2, same precedent as the earlier `backend_metal_proof`
    deletions).
- **Draw-IR** stays in `common/render_scene/` (pure, dependency-light — correct MDSOC layer).
- **Executor** stays in `gc_async_mut/render_scene/` as the single dispatch point (mirror the
  `gc_sync_mut` variant). Unify the two disagreeing backend-selection paths
  (`Engine2D.probe_backend()` vs. `compute_dispatch.spl`'s `BackendProber`) into one source of truth
  (plan P1, research §9).
- **MDSOC+**: rendering is a userland service surface → MDSOC outer facade (`Engine2D`) + the
  backend set as the business/driver layer; `baremetal`/`virtio_gpu` stay MDSOC-only (kernel/driver)
  and simply implement the same core surface — they get `SharedRaster` for free like everyone else.

---

## 10. Honesty — exists / designed / deferred

**Exists (reused as-is):** `RenderBackend` trait, `SceneCommand`/executor single dispatch,
`backend_emu` reference bodies (28 ops: 23 in `backend_emu.spl` + 5 in `backend_emu_adv.spl`),
`backend_software` SIMD hooks, directx honest naming, metal `gpu_frame_complete`,
`Engine2DReadback.source`, `SIMPLE_2D_BACKEND`/`cpu_simd` selection.

**Designed here (new):** single-trait consolidation + retirement of Core/Adv **plus** the two other
dead shared-interface attempts, `ComputeSession` and the `nogc_async_mut` textual trait copy (D1);
`SharedRaster` as the one parity oracle, gated on the §3b bit-exact harness, with forwarding stubs
(~191, corrected count) staying hand-written until FR-RENDER-MIXIN lands (D2 — **not** a free mixin
kill today); `BackendCapability` + uniform readback/`gpu_frame_complete` in the shared base,
explicitly closing the live WebGPU dishonesty case (D3); SIMD-CPU as span-override of the software
core wiring the **existing** unwired NEON/AVX2 kernels rather than writing new ones, proof-gated on
observing real kernel execution rather than `record_simd_*_hit` counters (D4); IR-completeness
additions (masks, stops, transforms, glyph runs, triangle/polygon, blend modes, executor replay of
blur, the `scene_blur_rect` drop); the add-a-backend seam; web-lane fold-in; the `Engine2D` facade's
dead 3-way branch collapse and the two disagreeing backend-selection paths unified into one; the
`RenderBackend` naming collision resolved; Intel/OpenGL vaporware either registered or de-listed
from selection priority; orphaned `backend_accel_*`/`*_proof*.spl` files quarantined/deleted.

**Decisions (2026-07-06):** D1, D2, D4 reviewed and **APPROVED_WITH_CHANGE** (changes folded in
above); **P1 is GO**, gated on the §3b bit-exact harness landing first; **mixin stub-elimination is
deferred to FR-RENDER-MIXIN**, filed as a prerequisite for a future stub-cleanup phase, not part of
P1.

**Deferred / risks:** mixin/`include` auto-forwarding is **confirmed infeasible** with the shipped
compiler (not a hypothetical "if") — the boilerplate kill needs the FR-RENDER-MIXIN codegen/wiring
work, which must also **preserve return-type annotations** the offline desugar currently drops.
Real GPU parity for transform/glyph-run may lag the reference (accelerate later; correctness via
`SharedRaster` meanwhile). Known blockers to respect in the plan: **engine2d drift** (line/circle
CPU↔GPU, MEMORY 06-03), **metal readback** falling back to software silently (MEMORY 06-10),
**JIT-render crash** on some winit/graphics apps (needs `SIMPLE_EXECUTION_MODE=interpret`, MEMORY
06-06), plus the newly-filed **honesty & coherence debt** (research §9): live WebGPU dishonesty,
Intel/OpenGL vaporware, the `cpu_simd` bare alias, orphaned fabricated-FFI files, the
`RenderBackend` naming collision, and the dead facade branch / dual selection paths.

---

## Layering: app-level backend isolation (2026-07-06)

This design governs Engine2D's *internal* multi-backend dispatch. A companion effort governs the
*external* boundary — that apps reach any renderer only through a named facade, never a backend or
`rt_*` extern directly. Full spec: plan
[`doc/03_plan/ui/rendering/backend_isolation_plan.md`](../../../03_plan/ui/rendering/backend_isolation_plan.md),
architecture
[`doc/04_architecture/ui/rendering/backend_isolation_architecture.md`](../../../04_architecture/ui/rendering/backend_isolation_architecture.md),
dev guide
[`doc/07_guide/ui/rendering/backend_isolation_guide.md`](../../../07_guide/ui/rendering/backend_isolation_guide.md).

### Rule

Apps, examples, and UI libraries call **only facades**; a facade may compose down onto Engine2D
(this design). Only backend implementations (`src/lib/**/gpu/**`) and the designated `io`/`ffi`
facades may declare or call `rt_*` externs. `extern rt_*` in `src/app/**` (outside
`src/app/interpreter/ffi`) or an unwrapped `simple_web_*` backend-engine call is a violation.

### Three facades, one shape

| Facade | Engines (by name) | Core engine resolves to |
|---|---|---|
| `Simple2D` (`Engine2D`) | metal · vulkan · directx · software · cpu_simd · … | *is* the reference oracle in this design |
| `WebRenderer` (`WebRenderBackend`) | chromium · pure_simple | `pure_simple` → Engine2D (`create_requested_backend`) |
| `GuiRenderer` (P3 gap — not built) | electron · gui_renderer_core | `gui_renderer_core` → native `CompositorBackend`/`hosted_entry` |

`WebRenderer.pure_simple` and `GuiRenderer.gui_renderer_core` **compose onto** the Simple2D / native
core — they do not duplicate a renderer. This is the "do not reinvent the GUI" invariant applied to
the facade layer.

### Allowlist (dirs where `rt_*` / backend-engine calls are legitimate)

```
src/lib/**/gpu/**   src/lib/**/io/**   src/lib/nogc_sync_mut/**
src/app/interpreter/ffi/**   src/os/compositor/**   src/os/hosted/**
```

Everything else under `src/app/**` and all of `examples/**` is forbidden. Enforced by
`scripts/check/check-backend-isolation-source-contract.shs` (plan P2), modeled on
`check-shared-wm-renderer-unification-evidence.shs`.

### Rationale

Splitting *what to draw* (app), *which engine* (facade name), and *how it reaches hardware*
(backend + `rt_*`) lets this design evolve Engine2D's backend roster and the dual-selection collapse
(D2) without touching a single app call site, and lets chrome/electron engines be selected by name
without an app learning a second API. It also makes the seam gate-able by a source-contract grep
rather than a bitmap diff.

### Perf non-regression anchors (facade must route *through*, never around)

The facade boundary is a naming boundary, not a data-copy boundary. These backend-internal fast
paths from this design are reached unchanged through the facades:

- Metal no-mirror fast path: `Engine2D.create_with_backend_fast` (`engine.spl:156`) →
  `MetalBackend.use_gpu_only()` (`backend_metal.spl:492`) — a facade must not downgrade the metal
  case to `create_with_backend`.
- Batched Metal buffer FFI: `rt_metal_buffer_upload/_download/set_bytes`
  (`backend_metal_runtime_ops.spl:2-4`) — one FFI shot per frame.
- NEON/SSE2 row kernels: `simd_fill_row` (`simd_kernels.spl:11`) →
  `fill_row_neon`/`copy_row_neon` (`engine2d_simd_ops.rs:95,161`).
- Browser pixel cache: `WebRenderPixelArtifactCache` (`web_render_pixel_backend.spl:111`) →
  `SimpleWebEngine2DStaticPixelCache.pixels_for_html` (`simple_web_engine2d_renderer.spl:66`) —
  `BrowserBackend.render_frame` calls the cache first (`backend.spl:561`).

The `SimpleWebHeuristicSurface` micro-fast-path (`simple_web_engine2d_renderer.spl:808`) is a known
intentional Engine2D bypass in the backend layer; the isolation lint special-cases it (it is not an
app-layer violation).
