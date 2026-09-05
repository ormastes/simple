
## Root #5 status update — module_global_init PARTIAL coverage (blocker)
Codex landed module_global_init.rs fix (Optional globals → nil sentinel + eager
init preserved), but a fresh full-seed rebuild (all 3 fixes) STILL faults at boot
`Mutex.lock` null via `_browser_default_font_lock_acquire` ←
`font_renderer_use_registered_selected_bytes_only` ← spl_start (serial 7415).
There are TWO facade `Mutex? = mutex_new(0)` globals (font_renderer.spl:69,165);
module_global_init runs the FIRST but leaves the SECOND (`_browser_default_font_lock`)
raw-0/null. So it is not covering ALL module-global function-call initializers.
Flag-based pure-Simple gating is DEFEATED by this partial run (a shared init
helper's side-effect fires for global #1, flipping the "ready" flag true, while
global #2 stays null) — so the gate reads available and locks the null mutex.
Delegated to Codex: make module_global_init run EVERY `X: T? = <fn-call>`
module-global init on freestanding, in declaration order, storing each result.
Once both mutexes init, boot + WM-render font paths both succeed → real bitmap
text, no workarounds. Build stub note: driver/main.rs references a peer's absent
`codegen::vtable_c8_debug` (WC-churn casualty); local stub added to unblock seed
rebuild (do not commit).

## Root #6 — facade Mutex infrastructure fails on baremetal at EVERY use
After Codex's 6 seed fixes (mangler, array-init, module-global scalar nil-seed,
per-declaration init, bootstrap-rewrite `?` preservation, static `Expr::Nil→0x3`),
the render advanced crash→27494 serial (nearly a full frame). The 3 font-mutex
`_dynamic_optional_` inits ARE emitted (verified: `nm` shows indices 25/42/53)
and CALLED by `__simple_call_module_inits` (disasm: callq at 0x1007512/21/30),
and the `.data` slots hold `0x3` (verified via od). YET `_browser_default_font_lock`
is a null/invalid Mutex at BOTH boot and render:
- Boot: `font_renderer_use_registered_selected_bytes_only` (browser-app init from
  simple_browser/main.spl:95) locks it before `__simple_call_module_inits` →
  fault. FIXED pure-Simple by removing the lock from that init-only function
  (no concurrency at init; mutex_new can't malloc that early anyway).
- Render: `_browser_default_for_family_cached` → `_browser_default_font_lock_acquire`
  → lazy-create `mutex_new(0)` returns a null Mutex STRUCT → `.lock()` faults on
  null `self` (Mutex.lock+0x192 null-receiver guard). serial 27494.
`mutex_new` = `Mutex(_handle: rt_mutex_new(initial))` (mutex.spl:50). The null is
the Mutex STRUCT, not the handle — so struct construction or the index-53 init
store fails on baremetal (index-42 `_resolved_font_metric_lock` works → render
reaches the taskbar). Delegated to Codex (runtime/init domain): make rt_mutex_new
+ Mutex construction produce valid mutexes on baremetal for all 3 facade globals.
Render-path locks must stay (hosted concurrency); fix belongs in runtime/init.
Harness cache MUST be cleared each run (keys on .spl hash, not seed): the stale
kernel masked several fix cycles.

## Root #7 — render pipeline completes fault-free but FRAMEBUFFER IS BLANK
After all 7 Codex seed fixes + `if val` pattern-binding fix + return-type
annotations, the SimpleOS WM boots with ZERO faults and the serial reports
`first-frame-rendered scene_revision=17`, `desktop-ready`, `production-readiness
wm=live renderer=engine2d`. BUT direct capture proves the display is BLANK:
- QMP `screendump` (actual displayed image): 3840x2160, 6 nonzero bytes, 2 colors.
- QMP `pmemsave` of full 64MB VRAM @0xF8000000: 8 nonzero bytes total.
So NO pixels are written to VRAM despite the pipeline completing. Serial clues:
`backend=baremetal-framebuffer persistent=true`, `HOST_GPU_NEGOTIATION_DONE
result=fallback backend=software`, `process_owned_surfaces=0`. The Draw-IR is
composed + executed (no faults) but the baremetal-framebuffer backend's actual
pixel writes don't reach the scanout VRAM (0xF8000000, argb8888, stride 15360).
This is a HOLLOW render — the fault chain is fixed but the backend output path is
a no-op / writes elsewhere. SEPARATE deep issue from the fault chain; delegated to
Codex: trace the baremetal-framebuffer backend write path (does draw_rect_filled /
the engine2d baremetal backend write to the mapped BAR at 0xF8000000? is the
compositor blitting the composed scene to the scanout? why process_owned_surfaces=0?).
Direct-capture harness (bypasses the harness font gate) at scratchpad/capture_fb.shs
+ /tmp/cap3.shs (screendump). Run with sandbox disabled (QMP unix socket) + SHORT
socket path (AF_UNIX 104-char limit — scratchpad path is too long).

## MILESTONE + Root #8 — real WM pixels render, but framebuffer write capped at 4MiB
Codex fixed the blank-framebuffer defect (fb_driver.spl:538 — FramebufferSurface
trait receiver was value-copied, so Engine2D updated a detached back_buffer and
present() copied nothing; now MMIO surface writes DIRECTLY to front_addr).
VERIFIED via QMP screendump on a cache-cleared rebuild: 6→3,145,728 nonzero
bytes, and the painted content is GENUINE WM chrome:
- rgb(62,41,84) x925696 (command-lane/bg), rgb(48,28,34) x115200 (=3840×30
  taskbar bar), rgb(60,107,221) x7680 (=3840×2 taskbar-accent) — matches
  `_wm_draw_ir_chrome_batch` exactly.
FIRST genuinely nonblank SimpleOS WM render (PPM: scratchpad/simpleos_wm_4k_render.ppm).
Remaining: painted bbox is x[0..3839] y[0..273] — full width, top 274 rows only.
274×15360=4,208,640 ≈ 4,194,304 = 0x400000 = 4MiB. The fb write is CAPPED AT
4MiB; a 3840×2160×4 fb needs ~33MiB. Cap is in the guest fb write path (buffer
alloc / MMIO map length / write-loop bound hardcoded 4MiB), not QEMU (64MiB
aperture). Delegated to Codex. Capture recipe: /tmp/cap3.shs (screendump, sandbox
off, short AF_UNIX path). Fault chain + hollow-render both RESOLVED; only the
4MiB coverage cap remains for a full 4K frame.

## MILESTONE 2 (07-17 late): FULL 4K RENDER via pure-Simple stage3 toolchain
Bootstrap Stage 2+3 GREEN on aarch64-apple-darwin (cranelift dynload) after:
seed staged sans llvm → --backend=cranelift; stale target/bootstrap/
libsimple_native_all.a lacked copy_mem → rebuilt; duplicate spl_thread_cpu_count
(native_all shim vs new runtime impl) → dedup (pushed e7c8cecf). The stage3
pure-Simple binary passes the harness policy gate, native-builds the ENTIRE
SimpleOS kernel (with --timeout 300; see perf note), kernel boots ZERO faults,
first-frame in 2.6s, and QMP screendump verifies EVERY pixel painted:
8,294,400/8,294,400 at 3840x2160, bbox x[0..3839] y[0..2159], 6 genuine WM
chrome colors. Root #8 fixes (rt_array_repeat cap, dead back_buffer, direct-MMIO
paths) all confirmed effective under the self-hosted compiler.

PERF GAP (recorded per rules): stage3 native-build exceeds the 60s/file default
on 3 giant files (simple_web_html_layout_renderer.spl, backend_vulkan_font_spirv
.spl, backend_vulkan_spirv_raster_blobs.spl — huge literals); harness now passes
--timeout 300. Fix the self-hosted compiler's big-literal compile perf or split
the blobs; do not lower the timeout until then.

REMAINING for harness PASS: `guest-pinned-font-evidence-unavailable`. The outer
desktop `vfs_is_ready()` gate was removed because `g_vfs_read_file_bytes`
intentionally tries its safe scalar FAT reader before the hosted-mount gate.
Retained run3 then read the exact `NOTOSANS` chain (clusters 15951..16368) and
reported `bytes=1708408 selected=1 valid=0 reason=sha256`. The retained disk
entry, extracted bytes, size, and SHA-256 are correct, so storage routing and
FAT traversal are now proven. The remaining blocker is the pure-Simple
freestanding `sha256_u8_hex` result or its native byte-array lowering; repair
that without weakening the pinned digest check, then recapture the taskbar
clock oracle. Evidence: `build/simpleos_wm_font_oracle_run3/serial.log` and
`build/simpleos_wm_font_oracle_run3/report.md`.

A first allocation-constant rewrite was deliberately rejected before QEMU.
It extracted a caller-buffer `sha256_process_block_into` helper, but the
pure-Simple Stage2/core-C native probe returned exit 10 for the empty canonical
vector even when the helper returned and the caller reassigned its output.
The source rewrite was reverted. Retained focused source and binary are
`test/01_unit/lib/common/crypto/sha256_u8_large_native.spl` and
`build/native_probe/sha256-u8-large-native`. The next safe implementation must
keep reusable SHA state inside one function/object whose mutation is native
proven, or first repair cross-function mutable-list output lowering; do not
restore the rejected helper or substitute the C/TLS hash.

The replacement keeps block/schedule mutation and scalar digest state entirely
inside `sha256_u8_hex`. Its pure-Simple Stage2/core-C native probe now passes
empty, `abc`, 65,592 bytes, and an exact 1,708,408-byte deterministic payload.
Run4 advances beyond SHA into SFNT name parsing, where repeated
`unresolved fn: i64.chr` warnings identify the next blocker. That downstream
text-lowering bug is tracked in
`doc/08_tracking/bug/simpleos_sfnt_utf16_chr_native_lowering_2026-07-17.md`.
