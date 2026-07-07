<!-- opus-design 2026-07-07 -->
# CPU vs GPU Dual-Algorithm Rendering — Design

**Companion research:** `doc/01_research/ui/rendering/cpu_gpu_dual_algorithm_research.md`.
**Companion plan:** `doc/03_plan/ui/rendering/cpu_gpu_dual_algorithm_plan.md`.
**Builds on:** `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` (D2 parity oracle, D3
capability model, D4 SIMD-CPU) — this design **extends** that mechanism, it does not replace it.

**Principle.** An op has (at least) two lawful algorithm shapes: a **CPU-lane** shape (bulk / native
/ one-call — never a per-element interpreted loop on a hot path) and a **GPU-lane** shape
(data-parallel kernel + buffer LUTs). Both are checked against **one parity oracle**. Selection is
per-op via the existing `BackendCapability`, per-process via `SIMPLE_2D_BACKEND`, per-build via
`variants/ui.renderer`. No new trait, no inheritance, no numbered module split (repo rules).

---

## 1. How an op declares CPU and GPU variants

Reuse D3's `BackendCapability.accelerated_ops` (`backend_capability.spl:41`) as the **fork point**.
No new abstraction is invented; the two-algorithm-set idea is made explicit on top of it.

- **GPU variant of op X** = X ∈ `accelerated_ops` **and** a native kernel for X exists
  (MSL/CUDA/…​). The facade/executor routes X to the backend method, which dispatches the kernel.
- **CPU variant of op X** = the `SharedRaster` reference body (the D2 canonical winner for X). Any
  backend that does not list X in `accelerated_ops` falls through to it
  (`draw_ir_multibackend_design.md` §3a: one-line `shared_draw_X(self, …)` delegation).
- **The contract the CPU variant must honor** (new, enforced by §6): the CPU-lane body of X on a
  designated hot path must use a **bulk/native idiom** (native `split`/`dict`/`memcpy`/one-call bulk
  marshalling), **not** a per-element interpreted loop. Where the extern bridge to do this is missing
  (bulk clear/read_pixels, N5), the op stays scalar **and is annotated as blocked**, not silently
  accepted (§6 allowlist).

This keeps a single dispatch point (the executor) and a single interface (`RenderBackend`); "two
algorithm sets" is a property of *which body runs*, decided by `is_accelerated(op)`, not a parallel
backend or a parallel trait.

## 2. Selection points (granularity → seam)

| Granularity | Seam | Binding |
|---|---|---|
| Per-op: kernel vs CPU reference | `BackendCapability.accelerated_ops` + `SharedRaster` fallthrough (research §3c) | runtime, per op, per selected backend |
| Per-process: which lane/backend | `SIMPLE_2D_BACKEND` env override → `Engine2D` backend selection (research §3b) | runtime, per process |
| Per-build: whole-module priority order | `variants/ui.renderer` overlay of `renderer_select.spl` (research §3a) | build target, whole module |

The dual-algorithm mechanism lives at the **per-op** seam. The per-process and per-build seams
choose *which backend is present*, which in turn determines which ops can be accelerated (a backend
with no device has an empty `accelerated_ops`, so every op is the CPU variant — honestly labeled
`class_ == "software-reference"`, D3).

**Environment-selected two sets (the mandate's "TWO algorithm sets selected by environment").**
`SIMPLE_2D_BACKEND=software` → every op runs its CPU-lane variant. `SIMPLE_2D_BACKEND=metal` (device
present) → ops in `accelerated_ops` run GPU kernels, the rest run CPU variants. No new env var is
introduced; the existing override already expresses the lane choice. A GPU build must never
degrade a CPU-lane op to a per-element loop, and a CPU build must never claim GPU acceleration
(D3 honesty).

## 3. The GPU dictionary primitive

A read-only, per-frame **buffer-backed lookup table** bound as one additional device buffer. Chosen
because it is realizable on the deployed interpret-mode binary with **no new extern** (upload-only,
via the working `rt_metal_buffer_upload`; research §2).

### 3.1 Buffer layout

Header + payload, little-endian, uploaded as one contiguous block:

```
GpuLut buffer (u32 words):
  word[0]   = kind         # 0=dense-direct, 1=sorted-binsearch, 2=open-addressing
  word[1]   = count        # number of entries (dense: table length; sparse: key count)
  word[2]   = mask         # (open-addressing only) slot_count-1, else 0
  word[3]   = value_stride # u32 words per value (1 for ARGB/palette)
  --- payload ---
  dense (kind 0):   values[count]                 # key IS the index
  binsearch (1):    keys[count], values[count*stride]   # keys ascending
  open-addr (2):    slots[slot_count] = (key,val…)       # empty slot key = 0xFFFFFFFF sentinel
```

### 3.2 Kernel-side lookup fn (MSL, added to the `_engine2d_msl()` string)

```metal
// returns value word offset for `key`, or 0xFFFFFFFF if absent
uint lut_lookup(device const uint* lut, uint key) {
    uint kind = lut[0], count = lut[1];
    if (kind == 0u) { return (key < count) ? lut[4 + key] : 0xFFFFFFFFu; }      // dense
    if (kind == 1u) {                                                            // binary search
        uint lo = 0u, hi = count; device const uint* keys = lut + 4u;
        while (lo < hi) { uint mid = (lo+hi)>>1; uint k = keys[mid];
            if (k == key) return (lut + 4u + count)[mid*lut[3]];
            if (k < key) lo = mid+1u; else hi = mid; }
        return 0xFFFFFFFFu;
    }
    uint mask = lut[2]; uint i = (key*2654435761u) & mask;                       // open-addressing
    device const uint* slots = lut + 4u;
    for (uint p=0u; p<=mask; ++p) { uint s=(i+p)&mask; uint sk=slots[s*2u];
        if (sk == key) return slots[s*2u+1u]; if (sk == 0xFFFFFFFFu) break; }
    return 0xFFFFFFFFu;
}
```

The pilot kernel (`kernel_indexed_fill`) reads an 8-bit index framebuffer and writes
`lut_lookup(palette, idx)` per pixel — the dense (kind 0) path, no search.

### 3.3 Upload / invalidation contract

- A `GpuLut` is built CPU-side (native array pack — **bulk, no per-element FFI**) and uploaded once
  via `metal_buffer_upload_ptr` (`backend_metal_runtime_ops.spl:20`) when its **version** changes.
- The backend holds `(lut_buffer_handle, lut_version)`. The op call carries the caller's
  `lut_version`; if it differs, re-upload before dispatch, else reuse (persistent-session idiom).
- Bind as `buffer(3)` (framebuffer=0, params=1, source=2 are taken; `backend_metal_msl.spl:16-20`).
- **Never** rebuild/re-upload per primitive or per frame when unchanged (research §4 GPU DON'T).

### 3.4 Loud-fail when absent

A backend that cannot bind an extra buffer (no device, or a platform whose kernel string lacks the
lookup fn) MUST **fall through to the CPU-lane variant of the same op** (the identical array-index /
dict lookup on the host), never emit wrong pixels and never silently skip. The capability descriptor
reports the op as *not* accelerated on that backend (`is_accelerated("indexed_fill") == false`), so
the fallthrough is the normal D2 path, not a special case. Absence is a capability fact, not an
error — but a backend that *claims* `indexed_fill ∈ accelerated_ops` while the buffer bind failed at
runtime is a D3 honesty violation and must flip `gpu_frame_complete` false.

## 4. Parity requirements (D2 matrix extension)

The GPU-dict path is a new accelerated op and inherits the D2 rule: **`B.read_pixels(S) ==
SharedRaster.read_pixels(S)` pixel-for-pixel** (`draw_ir_multibackend_design.md` §3b). Concretely:

- The **CPU-lane variant is the oracle**: `indexed_fill` on the software backend is a plain host
  array index (`palette[idx]`) into the framebuffer — this is the canonical body.
- Add an `indexed_fill` (and later `glyph_atlas_blit`) **row** to
  `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`, asserting Metal-`lut_lookup`
  output `== 0` diff vs the host-index reference on a fixed palette + index buffer.
- Divergence is only sanctioned the D2 way: a documented per-op decision with the assertion flipped
  through the harness (§the N2/N4 precedent). Absent divergence, the row stays `== 0`.

## 5. Where the two sets physically live

No numbered split (repo rule). Files evolve in place under
`src/lib/gc_async_mut/gpu/engine2d/`:

- **CPU variant** — `backend_software.spl` core ops + `SharedRaster` (`backend_emu*.spl`) higher ops.
  The `indexed_fill` host reference lands here as a new `SharedRaster` free fn.
- **GPU variant** — `kernel_indexed_fill` + `lut_lookup` in the `_engine2d_msl()` string
  (`backend_metal_msl.spl`); the `GpuLut` pack/upload helper alongside the existing
  `metal_buffer_upload_ptr` wrappers (`backend_metal_runtime_ops.spl`); the op added to
  `MetalBackend`'s `accelerated_ops`.
- **Capability** — `backend_capability.spl` gains an `indexed_fill` op string; Metal's descriptor
  lists it when a device is present.

## 6. Enforcement — the per-element-loop hot-path lint

A source-contract gate, modeled on the backend-isolation lint
(`scripts/check/check-backend-isolation-source-contract.shs`,
`check-ui-backend-isolation.shs`) — grep-based, no bitmap diff:

- **Rule.** In a **designated CPU hot-path set** (initially `backend_software.spl` core ops, the
  blur/gradient bodies in `backend_emu_adv.spl`, and the web renderer parse/style paths in
  `simple_web_html_layout_renderer.spl`), a `while`/`for` loop whose bound is a pixel-count /
  element-count / string length is a **violation** unless annotated `# cpu-lane-loop-ok: <reason>`
  (e.g. the documented `draw_line` per-point exception, `backend_software.spl draw_line`, or a
  blocked-on-N5 memset).
- **Also flag** `[u8]` byte-array element reads and per-position `substring(pos, …)` on those paths
  (research §4 CPU DON'T).
- **Output.** The gate lists each unannotated hot-loop with file:line and the required annotation, so
  a reviewer either fixes it (bulk idiom) or records the concrete blocker (never converts it to a
  silent NOTE — repo rule).
- **Scope discipline.** The designated set is an **explicit allowlist file**, not "all of
  `src/lib/**/gpu`", to avoid flagging the legitimately-scalar `r<=0` guards and the GPU kernel
  strings themselves.

## 7. Honesty — exists / designed / deferred

**Exists (reused):** `BackendCapability.accelerated_ops` per-op fork (`backend_capability.spl`);
`SharedRaster` parity oracle + the committed harness; `rt_metal_buffer_upload/set_bytes` batched FFI;
`SIMPLE_2D_BACKEND` runtime lane select; `variants/ui.renderer` build overlay; MSL multi-buffer
binds (buffer 0/1/2).

**Designed here (new):** the explicit CPU-variant *bulk-idiom* contract on hot paths; the buffer-backed
`GpuLut` primitive (layout + `lut_lookup` MSL fn + version/upload/invalidation contract +
loud-fall-through when absent); the D2 harness rows for `indexed_fill`/`glyph_atlas_blit`; the
per-element-loop hot-path lint gate.

**Deferred / blocked:** bulk clear/read_pixels memset (perf plan N5 — mutable-array-extern bridge,
seed); glyph-atlas GPU-dict pilot (needs atlas device upload + AA parity, larger than the palette
pilot); CUDA/Vulkan `lut_lookup` (Metal-first; other lanes ASSUMPTION until buffer-bind verified);
style/class GPU table (no consumer until web GPU-paint fold-in, `draw_ir_multibackend_design.md` §8).
