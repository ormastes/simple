# A trait-typed field call (`self.backend.<m>()`) has no vtable on the freestanding native lane

- Date: 2026-08-05
- Lane: freestanding `--target x86_64-unknown-none --backend cranelift
  --entry-closure --mode dynload`, OVMF pflash + GRUB EFI boot, stage3
  self-hosted compiler `build/bootstrap/stage3/aarch64-apple-darwin/simple`
- Symptom: `runtime error: duck-typed virtual method call (trait has no
  `impl Trait for ...` in unit; no vtable) — run with
  SIMPLE_EXECUTION_MODE=interpreter; see bug
  jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`, immediately followed
  by `[fault] rip=0x000000000868beb1 ... cr2=0x0 (recovering)`.
  Gate `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` never reaches
  a painted first frame, so `[ring3-slice] prime`, `[wm-loop] polling-active`
  and every downstream ring-3/IPC receipt are unreachable by construction.
- Serial evidence: `build/simpleos_wm_fullscreen_evidence/serial.log` (run of
  2026-08-05 10:06) — the last live rungs are web layout/font measurement
  (`[web-style-producer]`, `[font-inherit-trace]`, `[rfm] at=cache-hit`), then
  the runtime error and the fault frame.

## Root cause (disassembly-proven)

`llvm-symbolizer --obj=<kernel.elf> 0x0868beb1` →
`lib__gc_async_mut__gpu__engine2d__engine__Engine2D_dot_clear`.

`llvm-objdump -d --triple=x86_64-unknown-none
--disassemble-symbols=lib__gc_async_mut__gpu__engine2d__engine__Engine2D_dot_clear`
shows the whole ladder of `Engine2D.clear` and exactly where the fault RIP sits:

```
868bd52: movq 0x18(%r11), %rdi      ; self.virtio_gpu_backend
868bd65: callq *0x800e3e0           ; option-present helper
868bd6e: jne  0x868c11f             ; -> virtio rung
868bd9f: movq 0x10(%r8), %rdi       ; self.baremetal_backend
868bdb2: callq *0x800e3e0
868bdbb: jne  0x868c0aa             ; -> baremetal rung
868bdeb: movq 0x78(%rax), %rbx      ; self.selected_backend_name
868be05: callq *0x8011830           ; literal "cuda" (len 4)
868be18: callq *0x8002850           ; text ==
868be1e: jne  0x868bfae             ; -> cuda rung
868be4e: movq 0x28(%r11), %rdi      ; self.vulkan_backend
868be5f: callq *0x800e3e0
868be68: jne  0x868beb3             ; -> vulkan rung
868be96: movq (%r15), %rsi          ; self.backend  (TRAIT field, offset 0)
868be99: leaq .Ldata_c24cb8cc2c368911(%rip), %rdi
868bea0: movl $0xd2, %esi           ; 210-byte message
868bea5: callq *0x800bf60           ; runtime-error printer
868beb1: ud2                        ; <-- reported fault RIP
```

The terminal `else: self.backend.clear(color)` was **not compiled into a
dispatch at all**. `backend: RenderBackend` is a trait-typed field, and this
compilation unit has no vtable for it, so the backend emitted a
runtime-error-then-`ud2` stub in place of the call. Every ladder in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` that terminates in
`self.backend.<m>(...)` (22 sites) or `emu_<op>(self.backend, ...)` (18 sites)
carries the same stub.

## Which Engine2D reached it, and why the branch was correct

This is **not** an Option mis-discrimination. The taken branch was right: the
faulting engine genuinely has no virtio/baremetal/cuda/vulkan handle.

The SimpleOS WM's own engine is fine — `create_fb_engine_sized` →
`Engine2D.create_with_baremetal_backend_dims` pins
`baremetal_backend: Some(backend)` and takes the baremetal rung. The engine
that faulted belongs to the **web content producer**, reached from
`DesktopShell.render_baremetal_frame` → `runtime_content_frames` → the Simple
Web renderer:

```
# src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_cpu.spl:11
var engine = Engine2D.create_with_backend(width, height, backend_name)   # "cpu"
engine.clear(0u32)                                                       # <-- fault
```

`create_with_backend(w, h, "cpu")` built `Engine2D(backend: cpu, ...,
baremetal_backend: nil, virtio_gpu_backend: nil, selected_backend_name: "cpu")`
— every concrete accelerator handle nil, so the ladder correctly fell to the
trait rung, which does not exist on this lane. The accelerator lanes had all
been given concrete `Option` handles over time (baremetal, virtio, cuda,
vulkan, metal); the CPU/software lane never was, so it was the only one still
depending on real trait dispatch — and it is precisely the lane the
freestanding target uses for web content.

The fault therefore fires on the *first* content render of the *first* WM
frame, before `[ring3-slice] prime` and before `shell.run_baremetal`, which is
why no ring-3/IPC receipt had ever been observed.

## Source-shape fix applied (2026-08-05)

`src/lib/gc_async_mut/gpu/engine2d/engine.spl`:

- new field `cpu_backend: CpuBackend? = nil`, pinned **explicitly** in all 23
  `Engine2D(...)` constructor calls (per the 2026-07-16/07-19 landmine notes on
  the same class: an omitted named field is not reliably defaulted on this
  lane), set to `Some(...)` for `"cpu"`, `"cpu_simd"`, and — via a
  `CpuBackend` wrapper over the *same* `SoftwareBackend` instance — for
  `"software"`/`create_offscreen()`/`_poison_vulkan_font_surface`;
- an `elif val Some(cpu) = self.cpu_backend:` rung inserted immediately before
  the terminal `else` of every delegation ladder (42 rungs), calling the
  concrete `cpu.<m>(...)` / `emu_<op>(cpu, ...)`;
- the trait `else` rung is **kept unchanged** — hosted lanes still use it, and
  the new rung dispatches on the same object `self.backend` already points at,
  so hosted behaviour is unchanged;
- a bounded (8-line cap) `_dispatch_receipt()` probe in `clear()` naming the
  rung entered plus the presence of each concrete handle.

## Still open (compiler-side)

The source shape is a workaround, not the fix. The compiler should either
emit a real vtable for a trait-typed *field* call in a freestanding unit, or
reject the construct at compile time. Silently substituting a
runtime-error-plus-`ud2` stub for a call that type-checks means any trait field
in `src/lib` is a latent guest fault that only shows up on a boot. The
remaining trait-field call sites in this class (`backend_name()`'s
`self.backend.name()`, and the whole `Engine2DExtended` route through
`backend_emu.spl`, which takes a trait *parameter* and dispatches inside) have
the same exposure.

## Verification (build + OVMF boot, 2026-08-05)

Own build dir `build/e2d_cpu_rung_verify`, gate wrapper invoked with
`BUILD_DIR=... SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple`,
OVMF pflash + GRUB EFI, browser_demo client staged
(`browser_demo_build_status=pass`, `browser_demo_disk_status=pass`).

- Link: `Build complete: 733 compiled, 0 cached, 0 failed`, 11891 KB,
  `kernel_build_status=current-source-built`,
  `kernel_sha256=fcce953d239c8edf242d8695703e3b16e5535a58e69010c0d01b0f10d9551b3a`.
- Boot: real 4K scanout negotiated
  (`[scanout-evidence] ... width=3840 height=2160 stride=15360 argb8888
  generation=1`), font asset loaded, all three app spawns, `[ring3-slice]
  prepare pid=1 tss=ok handoff_ok=1` + `[ring3-slice] armed pid=1`, then the
  web content producer runs its layout/style/measure pass — byte-for-byte the
  same ladder as the failing run.
- **At the exact log position where the previous run emitted
  `runtime error: duck-typed virtual method call ...` + `[fault]
  rip=0x0000000000868beb1`, the new run emits nothing and keeps executing.**
  `grep -n 'duck-typed\|\[fault\] rip' serial.log` → no matches. Serial dropped
  from 19041 to 18522 bytes: exactly the removed error + fault frame, every
  preceding line identical. Since the trait rung traps *unconditionally* on
  this lane, not trapping is itself the proof that the new concrete `cpu` rung
  was taken.

Not yet green — a NEW, different blocker is now exposed: after `clear()`
succeeds the guest enters the CPU rasterization of the web content surface and
emits no further serial for the wrapper's 300s readiness window, so
`[desktop-gui] desktop-ready` never appears and the gate reports
`simpleos_wm_fullscreen_status=fail
reason=dynamic-scanout-or-desktop-readiness-missing`. Whether that is a hang or
merely software-raster throughput at 4K under TCG is the next thing to
determine — it is a different failure from this bug and needs its own
investigation.

Two caveats on this run, both unrelated to this fix:

- `rt_ring3_slice_tick` (parallel in-flight work in the untracked
  `src/os/kernel/arch/x86_64/ring3_slice.spl`) currently links as
  `FABRICATED-NEW` and hard-fails the freestanding stub ratchet, so this
  verification build used a scratch `SIMPLE_FABRICATED_STUB_BASELINE` override.
  The repo baseline `config/freestanding_fabricated_stub_baseline.sdn` was NOT
  modified. Consequently `rt_ring3_slice_tick` returns 0 in this kernel and the
  ring-3 slice rungs of this run carry no signal.
- The bounded `[e2d-dispatch]` receipt never printed. Most likely the
  module-level `val _E2D_DISPATCH_PROBE: bool = true` initialiser is not applied
  on this lane (the same defaulted/module-global initialisation landmine
  documented elsewhere in this class), so the probe gates itself off. The
  fault-absence evidence above does not depend on it.

## Known remaining exposure in the same file (not touched by this fix)

`backend_emu.spl`'s helpers take `mut core: RenderBackend` — a trait
*parameter*. Passing a **concrete** backend into it is fine (the call site
specialises; the existing `emu_<op>(cuda, ...)` rungs prove it, and the new
`emu_<op>(cpu, ...)` rungs rely on the same), but passing an already-erased
`self.backend` is not. Several `Engine2D` methods still do exactly that
*inside their virtio/baremetal rungs* — e.g. `draw_text_bg`, `draw_ellipse`,
`draw_arc`, `draw_polygon_filled` all call `emu_<op>(self.backend, ...)`
where the concrete `vg` / `bm` binding is right there in scope. Those are
latent faults on the SimpleOS WM's own baremetal engine; they have not fired
because the WM chrome reaches `draw_text_bg` only through the early
vector-font return. Fixing them is a mechanical
`emu_<op>(self.backend, ...)` → `emu_<op>(vg, ...)` / `emu_<op>(bm, ...)`
substitution, deliberately left out of this change to keep it reviewable and
because it needs its own boot verification.

Related: `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`,
`native_with_trait_impl_no_vtable_duck_trap_2026-07-28.md`.
