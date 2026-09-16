# Showcase lane regressions and toolchain gaps (2026-07-18 verification sweep)

Found while re-verifying the 3 showcase apps × standalone/host-WM lanes on
current main with the deployed `bin/simple` (v1.0.0-beta, self-hosted).

## Fixed in this sweep
1. **Module-count blowup via `app.io.mod` hub (host-WM lane hard-fail).**
   `wm_*_showcase_gui` adapters + `app.play.wm_daemon_client` imported single
   helpers from the hub, whose re-export chain (`cli_ops → run_commands →
   compiler.driver → hir`) loads the ENTIRE compiler in the interpreter →
   "Module count limit (800) exceeded" before main(). Proven by RUST_LOG
   module trace. Fixed with direct defining-module imports (998293f5).
2. **`rt_cli_arg_count`/`rt_cli_arg_at` externs in `std.io_runtime`** are
   unregistered on the deployed binary (#159): an unknown extern DECLARATION
   fails the whole module load, killing every importer (standalone widget
   crashed in 1s). Routed through `sys_get_args()` (a157afe8).
3. **`Engine2D.create_offscreen` named nonexistent ctor fields**
   (`software_backend`/`cpu_backend`/`directx_backend`, from the 07-16
   pin-everything workaround) — interpreter rejects unknown named args,
   crashing every hosted-lane caller. Fixed; declared defaulted fields stay
   pinned (a157afe8).
4. **AOT ambiguous-method guard on erased `if val Some(x)` bindings** in
   `Engine2D.draw_image_scaled` / `draw_image_blend` (26–28 candidates)
   blocked `bin/simple compile` of every Engine2D user. Typed receivers
   (e4f74739, dec098c1).
5. **`wm_web_standards_showcase_gui` had a 96x96 placeholder canvas**
   (copy-paste from the 808x632 graphics host) — web host-WM window could
   never render its page (998293f5).

## Root causes isolated after the first sweep (2026-07-18 late)
9. **Class-param paint detach (interpreter):** paints made through an
   `Engine2D` function parameter are lost to the caller (checkpoint bisect:
   every section healthy inside the callee, caller reads all-zero; `mut`
   alone does not write back). Workaround: thread the engine through the
   return value (landed for graphics_2d_showcase: 320x240 now renders
   76789/76800 nonzero, semantic gate 4/4, 217s interpret). The widget
   showcase's ~15 `w_*(b: Engine2D, ...)` helpers have the same exposure.
10. **JIT SIGSEGV on the 2D showcase** (exit 101 via isolated child; direct:
   SIGSEGV KERN_INVALID_ADDRESS at 0x890 inside JIT-generated code, frame
   `simple_compiler::codegen::jit::JitCompiler::call_i64_void` — macOS
   .ips report 2026-07-18-084220). This is the long-standing "graphics apps
   need SIMPLE_EXECUTION_MODE=interpret or JIT panics" class, now with a
   precise backtrace. Consequence: the fast lane for showcase apps is JIT,
   and it cannot run them; the 07-14 96s widget pass was therefore an
   interpreter run — meaning the interpreter itself slowed 3-4x since
   (item 6) and BOTH must be fixed for 720p-class showcase evidence.

## Open
6. **Interpreter throughput regression ~3-4x since 2026-07-14.** Widget
   standalone: 96s (07-14 PASS) → >280s timeout now; 2D 640x480: >280s
   (after fix #3; 07-14 had 320x240 self-gate passing); WM-client child
   never posts its bridge within 420s. Blocks all interpreter-lane showcase
   evidence at useful resolutions. Needs bisection of interpreter perf
   between 07-14 and 07-18 mains (deployed binary itself unchanged since
   Jul 5 — the regression is in the LIBRARY code the apps interpret, or in
   the grown module graph).
7. **`bin/simple compile --native` on macOS: linker selection + runtime
   symbol gaps.** Default linker invokes lld with ld64-only flags
   (`-force_load` rejected, Mach-O main.o "unknown file type");
   `--linker ld` reaches ld64 but link fails on undefined
   `_rt_alloc` (from engine2d readback/text helpers) and
   `_DIRECTX_FRAME_HEADER_WORDS_dot_to_u32` (const-method mangling on a
   module-global). Native standalone showcase binaries unavailable until
   the hosted native runtime bundle exports rt_alloc and the const-method
   mangling is fixed.
8. **Web showcase HTML/CSS layout is interpreter-bound** (>280s at every
   resolution, no completion) — unchanged from 07-14; the compiled lane
   (#7) is its unblocking dependency.

## SimpleOS lane (context)
In-guest showcase apps remain hard-gated on the open C8 BlockDevice-dispatch
codegen bug (FAT32 mount disabled at `vfs_boot_init.spl` "hosted fat32 mount
skipped"); see the 2026-07-17 native-build defect doc. Additional gaps: no
app staging env in the WM-harness disk build, showcase sources unproven under
the freestanding lane, guest→WM content protocol is text-only
(`COMP_UPDATE_TREE`), no SimpleOS adapter exists (host_wm bridge is
file-based). Shortest credible path: after C8, stage the proven
fs_exec_ring3 + WindowClient text app as `/sys/apps/graphics_2d_showcase.smf`
to prove the pipeline, then design a pixel-frame IPC (`COMP_UPDATE_FRAME`).
