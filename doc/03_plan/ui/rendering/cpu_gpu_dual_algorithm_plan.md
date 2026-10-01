<!-- opus-plan 2026-07-07 -->
# CPU vs GPU Dual-Algorithm Rendering — Plan

**Research:** `doc/01_research/ui/rendering/cpu_gpu_dual_algorithm_research.md`.
**Design:** `doc/05_design/ui/rendering/cpu_gpu_dual_algorithm_design.md`.
**Sequenced against:** `doc/03_plan/ui/perf/gui_web_2d_perf_fix_plan.md` (perf next-wave N1–N8) and
`doc/05_design/ui/rendering/draw_ir_multibackend_design.md` §D2 (parity oracle; op consolidation
remainder). Parity rule for every pixel-touching item: the assertion moves through
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` — `== 0` if output-preserving,
flipped `> 0 → == 0` only for a documented per-op reconciliation.

Each work item is agent-executable: files · steps · specs · gates · size · deps · risks.

---

## First wave (recommended — no seed dependency)

### W1 — GPU-dict pilot: `indexed_fill` palette LUT (Metal) **← ✅ LANDED + GPU-PROVEN (2026-07-07)**

> **Status: LANDED — GPU path PROVEN bit-exact via genuine `device_readback`.**
> `MetalSession.init()` creates the `kernel_indexed_fill` compute pipeline on the
> deployed 2026-07-05 self-hosted binary (`init=true pipe_indexed_fill=15
> pipe_clear=4 pipe_blit=14 err_code=0`, 5/5 runs). Metal palette `indexed_fill`
> via the buffer-backed LUT is proven **bit-exact vs the CPU oracle**
> (`SoftwareBackend.indexed_fill`) on the same palette+indices — including
> out-of-range → `0xFFFFFFFF` sentinel misses — read back through real
> `device_readback`: `indexed_fill: MATCH pixels=3072 source=device_readback`,
> **checksum `1413576747` on both backends**. Proof lives in a dedicated row of
> `scripts/check/check-engine2d-gpu-offload-evidence.shs` /
> `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl` (gate
> `pass (cpu-metal-bitexact-device-readback)`). Parity spec 24/24;
> `engine2d_gpu_offload_contract_spec` 12/12. The one-time "new kernel not found"
> report was **non-reproducing/transient** (see
> `doc/08_tracking/bug/engine2d_metal_new_kernel_pipeline_not_found_2026-07-07.md`).

- **Motivation.** Establishes the buffer-backed GPU dict end-to-end on the deployed interpret-mode
  binary with **no new extern** (upload-only via `rt_metal_buffer_upload`; research §2). Proves the
  primitive before spending it on the larger glyph-atlas case.
- **Files.** `backend_metal_msl.spl` (add `lut_lookup` + `kernel_indexed_fill` to `_engine2d_msl()`),
  `backend_metal_runtime_ops.spl` (a `GpuLut` pack/upload helper beside `metal_buffer_upload_ptr`),
  `backend_metal.spl` (dispatch + bind `buffer(3)`; add `indexed_fill` to `accelerated_ops`),
  `backend_software.spl` (host `indexed_fill` reference = `palette[idx]` — the oracle),
  `backend_capability.spl` (register the `indexed_fill` op string),
  `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` (add the row).
- **Steps.** (1) Host reference `indexed_fill` in `backend_software.spl` (native array index, no
  per-pixel FFI). (2) `GpuLut` dense-kind pack (bulk host pack) + upload helper. (3) MSL `lut_lookup`
  (dense path) + `kernel_indexed_fill`; bind palette as `buffer(3)`; version/reuse per design §3.3.
  (4) Parity row: Metal output `== 0` diff vs host reference on a fixed 256-entry palette + index
  buffer. (5) Loud fall-through: if device/bind absent, run the host variant (design §3.4).
- **Specs.** New `indexed_fill` parity row; `engine2d_gpu_offload_contract_spec` stays green.
- **Gates.** Parity spec; `check-engine2d-gpu-offload-evidence.shs`; `check-ui-backend-isolation.shs`
  (no new `rt_*` outside the allowlisted gpu dir).
- **Size:** M. **Deps:** none (buffer upload works today). **Risks/rollback:** MSL compile error
  silently falls to software (MEMORY 05-30) → assert `gpu_frame_complete` true on the accelerated
  path in the spec; rollback = drop `indexed_fill` from `accelerated_ops` (op reverts to host
  variant, still correct).

### W2 — Per-element-loop hot-path lint gate **← ✅ LANDED (2026-07-07)**

> **Status: LANDED — first real CI-enforced gate in this repo (task #34,
> gates-vestigial-under-jj, partially addressed).** `scripts/check/check-cpu-hotloop-idiom.shs`
> (content-keyed baseline ratchet, 245 keys / 393 instances) is wired into
> **`.github/workflows/repo-hygiene.yml`** as a push/PR step — CI is now the
> **authoritative, non-bypassable** enforcement lane, since `jj` bypasses git hooks
> (see `doc/05_design/ui/rendering/cpu_gpu_dual_algorithm_design.md` §6.1). Also wired
> into `src/app/io/_CliCommands/run_commands.spl` `cli_run_lint` beside the sibling
> `check-ui-backend-isolation.shs` call — code-correct, but this lane only fires after
> the next self-hosted rebuild (deployed `bin/release` binary predates the change), and
> `bin/simple build lint` still routes to the inert Rust clippy shim
> (`build_lint_routes_to_rust_clippy`) so a gate wired only there would never run.
> Spec `test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl` 15/15.

- **Motivation.** Makes the CPU-lane "no per-element loop" contract (design §6) enforceable so the
  dual-algorithm discipline does not regress.
- **Files.** new `scripts/check/check-cpu-lane-hot-loops.shs`; a checked-in allowlist file
  (designated hot-path set + `# cpu-lane-loop-ok:` annotations); wire into `bin/simple build lint` /
  pre-commit like the sibling backend-isolation gate.
- **Steps.** (1) Author the grep gate (flag pixel/element-count `while`/`for`, `[u8]` element reads,
  `substring(pos,…)` on the designated set unless annotated). (2) Seed the allowlist with today's
  sanctioned exceptions (`backend_software.spl` `draw_line` per-point; N5-blocked bulk clear/readback;
  `r<=0`/`d==0` guards). (3) Wire into lint.
- **Specs.** A meta-spec: the gate flags a planted violation and passes the annotated baseline.
- **Gates.** Runs clean on the current tree after the allowlist seed (no false-positive storm).
- **Size:** S–M. **Deps:** none. **Risks/rollback:** over-broad scope flags legitimate guards →
  keep the designated set an explicit allowlist, not `src/lib/**/gpu/**`; rollback = disable the gate.

### W3 — `draw_gradient_rect` one-pass CPU variant + GPU-kernel parity (perf N4, D2-gated)

- **Motivation.** Gradient is 6.16x per-px vs a plain fill (perf plan N4); a clean case where the
  CPU variant (one-pass integer lerp) and the GPU variant (`kernel_draw_gradient_rect`) are both
  already present and just need the dual-algorithm parity row + the D2 sw↔emu decision.
- **Files.** `backend_emu.spl` (D2-hot — coordinate with N4), the D2 canonical reference, the parity
  spec.
- **Steps.** Per perf plan N4: D2-aligned decision (shared one-pass in `backend_emu` vs documented
  software override, mirroring the `draw_line` exception), then implement + parity.
- **Specs.** Gradient parity rows (`== 0` if output-preserving; else flip per D2).
- **Gates.** Parity spec. **Size:** M. **Deps:** the D2 gradient decision (perf N4). **Risks/rollback:**
  reversing the sw→emu delegation regresses other callers → gate on parity; rollback = revert to
  delegation.

---

## Second wave (D2-settled or seed-unblocked)

### W4 — Glyph-atlas GPU dict (`glyph_atlas_blit`) — moves `draw_text` to the GPU lane

- **Motivation.** `draw_text` is CPU-only today (~547 µs/char, perf plan 2D-5) and is the strongest
  real consumer of a GPU dict (codepoint→atlas-offset table + device atlas; the exact case
  `backend_intel_kernels.spl:132` envisions). Depends on W1's primitive.
- **Files.** `backend_metal_msl.spl` (`glyph_atlas_blit` kernel using `lut_lookup` binsearch/dense),
  atlas device-upload helper, `backend_metal.spl`, `backend_software.spl` (host reference already
  exists — real 5x7 glyphs + AA, the D2 text canonical), parity spec.
- **Steps.** (1) Build a codepoint→offset `GpuLut` + upload the glyph atlas as a device buffer. (2)
  `glyph_atlas_blit` kernel: per pixel, look up glyph offset, sample atlas, AA-blend. (3) Parity vs
  the SW glyph reference (D2 text winner). (4) Loud fall-through to the host glyph path when absent.
- **Specs.** `glyph_atlas_blit`/`draw_text` parity row (must match SW glyphs+AA bit-exact, D2).
- **Gates.** Parity spec; offload evidence. **Size:** L. **Deps:** W1 (primitive); the D2 text
  canonical (already SW). **Risks/rollback:** AA rounding divergence from the CPU AA → gate on the
  parity row; rollback = keep `draw_text` off `accelerated_ops` (CPU variant, unchanged).

### W5 — Separable box blur (perf N2) — GPU-lane data-parallel candidate

- **Motivation.** ~6x on top of 2D-1 for large radii; the 2-pass shape is the GPU-lane-correct form.
  Pixel-changing (perf plan N2).
- **Files/steps/specs/gates/size/deps/risks:** as perf plan **N2** — wait for D2 to settle
  `backend_emu.spl`/parity spec, implement 2-pass, regen the D2 blur reference, flip the blur
  assertion. **Size:** M. **Deps:** D2 settled. A GPU blur kernel is a later add once the CPU 2-pass
  reference is canonical.

### W6 — Bulk `clear`/`read_pixels` (perf N5) — **BLOCKED (seed)**

- The CPU-lane bulk memset/memcpy variant (50–200x, research §4) needs the mutable-array-extern
  bridge (`cpu_simd_mutable_array_extern_wiring_2026-05-31.md`, OPEN) — a runtime/seed change,
  off the pure-Simple path. **Do not attempt in this plan.** Track as a dependency; W2's lint
  annotates these loops `# cpu-lane-loop-ok: blocked-on-N5` until the bridge lands. Sequenced after
  the seed owner lands the bridge; then wire per perf plan N5, and only then real `cpu_simd` (N6).

### W7 — `cpu_simd` honesty (perf N6)

- The `cpu_simd` backend is a bare alias of scalar `cpu` (research §1; `engine.spl:271-279`). Until
  W6's bridge lands, either dispatch to the real `simd_fill_row` kernels where the extern already
  supports it, or report honestly that it is scalar (no fake `record_simd_*_hit` counter). Per perf
  plan N6. **Size:** S (honesty) / M (real dispatch, deps W6). Discredit `record_simd_*_hit` as
  proof (D4).

---

## Sequencing summary

```
Wave 1 (no seed dep, parallelizable — disjoint files):
  W1 GPU-dict palette pilot   (Metal msl/runtime/backend + sw ref + capability + parity spec)
  W2 CPU-lane hot-loop lint    (scripts/check + allowlist)          [independent]
  W3 gradient one-pass         (backend_emu D2-hot)                 [after/with perf N4 D2 decision]

Wave 2:
  W4 glyph-atlas GPU dict      [deps W1]
  W5 separable blur            [deps D2 settled]
  W6 bulk clear/readback       [BLOCKED: seed mutable-array-extern bridge]
  W7 cpu_simd honesty          [S now; M real-dispatch deps W6]
```

**First-wave recommendation:** land **W1** (GPU-dict palette pilot — the mandate's core "add GPU
dict if possible", upload-only, no seed dependency, tight parity) and **W2** (the enforcement gate
that keeps the CPU lane honest), in parallel with **W3** if the perf-plan N4 D2 gradient decision is
made. Avoid W6 (seed-blocked) and defer W4 (larger, deps W1).

**Disjointness for parallel dispatch:** W1 touches the Metal/software/capability/parity files; W2
touches only `scripts/check/` + a new allowlist; W3 touches `backend_emu.spl` (D2-hot — must serialize
with any live D2/N4 work). W1 and W2 are fully disjoint and can run concurrently.
