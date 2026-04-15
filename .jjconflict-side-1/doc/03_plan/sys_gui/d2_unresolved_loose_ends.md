# D2 Glass Subtrait — Unresolved Loose Ends

Date: 2026-04-14
Scope: triage two open items blocking D2 (glass subtrait split + rt_winit
buffer migration) — `src/os/compositor/dual_backend.spl` disposition, and
locating the runtime-side `rt_gui_*` definitions referenced by the parent
contract-fix plan.

All file:line below verified against `origin/main` unless flagged.

---

## Part A — `dual_backend.spl` disposition

### A.1 What it is

`src/os/compositor/dual_backend.spl` (tip revision on origin/main, 183 lines
per `git show origin/main:... | wc -l`). Head comment:

> "Dual-Backend Runner — Native vs Browser Engine Comparison.
> Renders the same compositor scene through two different backends and
> compares the pixel output for visual consistency verification.
> Backend A: HostedCompositorBackend (winit pixel buffer, Rust FFI).
> Backend B: BrowserCompositorBackend (Simple [u32] buffer, software).
> Uses a backend-swap approach: single compositor, render twice."

It is a **visual-consistency harness**, not production code.

Structure (`origin/main:src/os/compositor/dual_backend.spl`):
- L11-15 — imports: `Compositor`, `HostedCompositorBackend`,
  `BrowserCompositorBackend`, `HostedInputBackend`, `screenshot_compare.*`.
- L18 — `extern fn rt_winit_buffer_save_bmp(buf: i64, path: text) -> bool`
- L19 — `extern fn rt_winit_buffer_get_pixels(buf: i64) -> [i64]`
- L20 — `extern fn rt_winit_save_pixels_bmp(path: text, width: i64,
  height: i64, pixels: [u32]) -> bool`
- L26 — `class DualBackendRunner:` (holds `native_backend`, `browser_backend`,
  `input`, `sw`, `sh`, `threshold`).
- L39 — `impl DualBackendRunner:` — `new(...)`, `set_threshold`,
  `run_comparison(output_dir)` which (1) renders via native, (2) extracts
  pixels at L83 via `rt_winit_buffer_get_pixels`, saves BMP at L93 via
  `rt_winit_buffer_save_bmp`, (3) renders via browser, (4) compares, (5)
  generates diff via `rt_winit_save_pixels_bmp`.

No `rt_gui_*` references — confirmed by `git grep 'rt_gui_' ...
dual_backend.spl`.

### A.2 Who imports it

`git grep -n 'dual_backend' origin/main -- src/ test/ doc/`: **zero source-
or test-side imports.** Only references are:

- `doc/03_plan/sys_gui/rt_winit_buffer_caller_catalog.md:40,73-75,142,178,190`
- `doc/03_plan/v2_hosted_engine2d_rewiring.md:208,221,305`

`git grep -n 'DualBackend'` returns only the class decl and the `impl`
inside the file itself — **no external constructor call, no test.**

Effectively **orphan code** — planned infrastructure that no harness wires up.

### A.3 History

```
71058d9b67 2026-04-07 feat(os): shared input event + shortcut modules for WM/compositor/UI
```

`git log --oneline origin/main -- src/os/compositor/dual_backend.spl` returns
exactly one commit (2026-04-07). The file is seven days old as of today
(2026-04-14) and has never been touched since introduction. The commit
message suggests it rode in on a larger input-event refactor, not as a
deliberately scheduled comparison harness.

### A.4 Recommendation — **migrate** (not delete, not gut)

Functional tool solving a real problem (cross-backend pixel diff) D2 makes
more urgent. Orphan today (no callers/tests) so it's ideal for a proof-of-
migration PR under recipe R6 — exercises `HostedCompositorBackend.get_pixels`
/ `.save_bmp` additions and leaves a working harness. Gutting or keep-as-is
both cement the bypass the caller catalog flagged.

### A.5 Action list

Applies **recipe R6** from
`doc/03_plan/sys_gui/rt_winit_buffer_caller_catalog.md:142,178`.

- [ ] Add `save_bmp(path: text) -> bool` method on
      `HostedCompositorBackend` (`src/os/compositor/hosted_backend.spl`)
      that wraps `rt_winit_buffer_save_bmp(self.buffer_id, path)`.
- [ ] Confirm `HostedCompositorBackend.get_pixels() -> [i64]` already
      exists (catalog says it does, at `hosted_backend.spl:202`).
- [ ] Edit `dual_backend.spl`:
  - Delete `extern fn rt_winit_buffer_save_bmp` (L18) and
    `extern fn rt_winit_buffer_get_pixels` (L19).
  - L83 → `self.native_backend.get_pixels()`.
  - L93 → `self.native_backend.save_bmp(native_path)`.
  - Keep `rt_winit_save_pixels_bmp` (L20, L99, L105) — this is a
    *write-path for the browser buffer*, not a winit-buffer call; it
    takes a `[u32]`, not a `buffer_id`, so it is a distinct FFI family
    and out of scope for R6.
- [ ] Add a smoke test at `test/system/compositor/dual_backend_smoke.spl`
      that constructs `DualBackendRunner.new(...)` and runs one
      `run_comparison` pass to a tmp dir — without this the migration is
      still unverified.
- [ ] After the migration merges, flip the R6 checklist item in
      `rt_winit_buffer_caller_catalog.md:190` to `[x]`.

---

## Part B — `rt_gui_*` Rust-side location

### B.1 Actual file(s) on origin/main

**Finding: `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` /
`rt_gui_read_pixel` are NOT defined anywhere under `src/runtime/` or
`src/compiler_rust/`.**

`git grep -l 'rt_gui_blend_fill\|rt_gui_box_blur\|rt_gui_gradient_v'
origin/main -- src/runtime/` → empty.
`git grep 'rt_gui_' origin/main -- '*.rs'` → one hit:

- `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs:134` —
  `pub fn rt_gui_get_glyph_8x16_fn(...)` (unrelated — this is the text-
  rendering glyph lookup, dispatched at
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:404`).

No Rust dispatch for `rt_gui_blend_fill` / `_box_blur` / `_gradient_v` /
`_read_pixel` exists. Instead, the **hosted** path has
functionally-equivalent externs under a different name in
`src/compiler_rust/compiler/src/interpreter_extern/winit_ffi.rs`:

- `rt_winit_buffer_blend_rect` — `winit_ffi.rs:1507-1508`
- `rt_winit_buffer_blur` — `winit_ffi.rs:1551-1552`
- `rt_winit_buffer_gradient_v` — `winit_ffi.rs:1646-1647`
- `rt_winit_buffer_read_pixel` — `winit_ffi.rs:1487-1488`

The **baremetal** `rt_gui_*` symbols live in C, not Rust:

- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c:5586,5602,5613,5642`
- `examples/simple_os/arch/x86_64/boot/glass_render.c` (e.g. L80, L90, ...)
- `examples/simple_os/arch/arm64/boot/baremetal_stubs.c:1930-1974`
- `examples/simple_os/arch/riscv64/boot/baremetal_stubs.c:1838-1841`

These are architecture-specific C stubs compiled into the baremetal ELF.

### B.2 Crate structure

`src/runtime/Cargo.toml` exposes only `spl_memtrack_rust` (`[lib] name =
"spl_memtrack_rust"`, `path = "runtime_memtrack_rust.rs"`). `src/runtime/`
contains exactly two tracked files: `Cargo.toml` and
`runtime_memtrack_rust.rs`. **There is no `src/runtime/gui/` tree at all.**

The "Rust runtime" side of hosted FFI lives inside
`src/compiler_rust/compiler/src/interpreter_extern/` (40+ `.rs` files).
For baremetal, it's C in `examples/simple_os/arch/*/boot/`.

### B.3 Test coverage

- Interpreter side: `conversion.rs:209-210` has
  `test_rt_gui_get_glyph_8x16_returns_16_rows` — the only `rt_gui_*`
  unit test, and it does not cover the glass family.
- No Rust unit tests for `rt_winit_buffer_blend_rect` / `_blur` /
  `_gradient_v` / `_read_pixel` in `winit_ffi.rs`
  (`git grep '#\[test\].*rt_winit_buffer' -- '*.rs'` is empty over the
  slice inspected; none of the terms in the searchable index hit a
  `#[test]`).
- Simple side: `examples/simple_os/arch/x86_64/gpu_render_test_entry.spl`
  and `wm_test_entry.spl` exercise `rt_gui_blend_fill` end-to-end on
  baremetal — these are integration tests, not unit.

**Gap:** the hosted blend/blur/gradient/read_pixel path has zero unit-test
coverage on the Rust side.

### B.4 Update to D2 Phase 2 — proposed diff

Do **not** edit `doc/03_plan/sys_gui/d2_glass_subtrait_migration.md` from
this doc — this is a triage note, not a plan edit. Propose:

```diff
--- a/doc/03_plan/sys_gui/d2_glass_subtrait_migration.md
+++ b/doc/03_plan/sys_gui/d2_glass_subtrait_migration.md
@@ §6 Phase 3 bullet
-- Delete the `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v`
-  / `rt_gui_read_pixel` extern declarations in Simple and the Rust shim
-  registration (location TBD during impl — `git grep` on origin/main
-  confined these externs to `display_backend.spl` +
-  `compositor_engine2d.spl`; the Rust-side definition file should be
-  located at impl time and marked deprecated in Phase 1, deleted in
-  Phase 3).
+- Delete the `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v`
+  / `rt_gui_read_pixel` extern *declarations* in Simple
+  (`src/os/compositor/display_backend.spl:43-45`,
+  `src/os/compositor/compositor_engine2d.spl:58-60`,
+  `src/os/compositor/glass_effects.spl:11-13`). There is **no Rust-side
+  definition to delete**: no `src/runtime/gui/glass.rs` exists on
+  origin/main, and `git grep 'rt_gui_blend_fill' -- '*.rs'` returns
+  zero hits. The baremetal side is C:
+  `examples/simple_os/arch/{x86_64,arm64,riscv64}/boot/baremetal_stubs.c`
+  and `arch/x86_64/boot/glass_render.c`. Delete the C symbols alongside
+  the Simple decls in Phase 3 once `FbCompositorBackend`'s native glass
+  impl lands.
@@ §10 File existence audit
-- No `src/runtime/gui/glass.rs` hit on `origin/main`; the Rust-side
-  `rt_gui_*` definition file is not in the path suggested by the parent
-  plan — flag to locate during impl.
+- `src/runtime/gui/glass.rs` does not exist and the parent contract-fix
+  plan's reference at `gui_layer_contract_fix_plan.md:98` is stale. The
+  Rust shim for hosted glass is a *different* FFI family —
+  `rt_winit_buffer_{blend_rect,blur,gradient_v,read_pixel}` at
+  `src/compiler_rust/compiler/src/interpreter_extern/winit_ffi.rs:
+  1487, 1507, 1551, 1646`. Baremetal glass is C
+  (`examples/simple_os/arch/*/boot/{baremetal_stubs,glass_render}.c`).
+  Phase 2's "native per-backend glass" for `HostedCompositorBackend`
+  already routes through the `rt_winit_buffer_*` path — no Rust-side
+  `rt_gui_*` work is required for hosted.
```

### B.5 Spec doc status

`git grep -l 'rt_gui_blend_fill\|rt_gui_box_blur\|rt_gui_gradient_v'
origin/main -- doc/` returns:

- `doc/03_plan/sys_gui/d2_glass_subtrait_migration.md` (the plan)
- `doc/03_plan/sys_gui/gui_layer_contract_fix_plan.md` (parent plan)
- `doc/04_architecture/gui_layer_contract.md` (contract)

`gui_layer_contract.md` is the canonical contract and mentions the subtrait
but does **not** pin a signature/semantics for the `rt_gui_*` C externs
themselves (packing, alpha range, coordinate origin). Combined with the
fact that the symbols only exist in three C stub copies (x86_64, arm64,
riscv64) with drifting signatures — e.g. arm64 `rt_gui_blend_fill` has no
return type, x86_64 returns `RuntimeValue` — **a contract doc for the
`rt_gui_*` C family does not exist and should be written** if Phase 2 keeps
any of them alive after `FbCompositorBackend` migrates to
`FramebufferDriver`. Recommended: a short `doc/04_architecture/
rt_gui_c_contract.md` listing each symbol, the three arch implementations,
and the packing convention from `glass_render.c:22`.

---

## Cross-part interaction

`dual_backend.spl` is glass-independent. It uses `rt_winit_buffer_save_bmp`
/ `_get_pixels` / `rt_winit_save_pixels_bmp` only — no `rt_gui_*`, no
`blend_rect` / `blur_region` / `gradient_v` calls (verified:
`grep -nE 'fill_rect|glass|blend_fill|box_blur|gradient_v'` returns empty).
The harness renders whatever the compositor draws; if the underlying
`HostedCompositorBackend` gains a `CompositorGlassCapable` impl in Phase 2,
the dual runner will pick it up transparently. Its R6 migration is
independent of D2 Phase 2 and can land in either order. No native-glass
work is needed for `dual_backend.spl` itself.
