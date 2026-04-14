# rt_winit_buffer Caller Migration Catalog

**Date:** 2026-04-14
**Companion plan:** `doc/03_plan/sys_gui/rt_winit_buffer_caller_migration.md`
  *(NOTE: that plan doc is NOT on `origin/main` as of this date — flagged. This
  catalog anticipates its landing.)*
**Reference backend:** `src/os/compositor/hosted_backend.spl` on `origin/main`.

---

## 1. Scope

Every code-layer caller of the `rt_winit_buffer_*` FFI family (10 externs,
listed by `src/compiler_rust/compiler/src/interpreter_extern/winit_ffi.rs:1330-1701`)
is enumerated below and classified as *legitimate*, *migrate*, or
*test-fixture-ok*. The migration goal is to funnel all pixel-drawing traffic
through the `HostedCompositorBackend` (`src/os/compositor/hosted_backend.spl`)
trait methods so that `examples/`, app layers, and system tests stop knowing
about raw winit buffer handles. Only the backend internals and a single
bootstrap site in `src/os/hosted/hosted_entry.spl` are allowed to keep calling
the FFI directly.

---

## 2. Legitimate vs. illegitimate callers

**Legitimate (may keep raw FFI calls):**
- `src/os/compositor/hosted_backend.spl` — this IS the backend; FFI is its body.
- `src/os/hosted/hosted_entry.spl` — bootstrap site that owns window+buffer
  lifecycle and hands them to the backend via `HostedCompositorBackend.create(...)`
  or `HostedCompositorBackend.new(...)`. The sole legitimate external
  `rt_winit_buffer_create` call.
- `src/compiler_rust/compiler/src/interpreter_extern/winit_ffi.rs` — the Rust
  definition side (not a caller).

**Illegitimate (must migrate):**
- Anything in `examples/simple_os/hosted/` that re-declares `extern fn rt_winit_buffer_*`
  and draws pixels outside the backend.
- Anything in `src/os/compositor/` **other than** `hosted_backend.spl` that
  bypasses the backend (e.g. `dual_backend.spl` currently re-enters the FFI for
  BMP/pixel-dump — migrate).
- App-layer code (`src/app/ui.*`) — must never touch winit buffer directly.

**Test-fixture-ok (case-by-case):**
- System tests under `test/system/os/` that explicitly validate the FFI surface
  may keep raw calls, but anything that is *only* rendering a WM mock should
  migrate to `HostedCompositorBackend` to prove the trait path works end-to-end.

---

## 3. Full call-site catalog

All line numbers verified against `origin/main` via `git grep`. Symbols that
are purely `extern fn` declarations are grouped as "decl".

| File:line | FFI called | Kind | Classification | Recipe |
|-----------|------------|------|----------------|--------|
| `src/os/compositor/hosted_backend.spl:19-27` | (decls) | decl | legitimate | keep (backend owns externs) |
| `src/os/compositor/hosted_backend.spl:71` | `rt_winit_buffer_fill_rect` | clear | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:80` | `rt_winit_buffer_fill_rect` | fill | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:109` | `rt_winit_buffer_fill_rect` | glyph pixel | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:118` | `rt_winit_buffer_fill_rect` | put_pixel | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:122` | `rt_winit_buffer_present` | present | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:126` | `rt_winit_buffer_present` | present | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:136` | `rt_winit_buffer_blend_rect` | blend | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:145` | `rt_winit_buffer_blur` | blur | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:155` | `rt_winit_buffer_gradient_v` | gradient | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:157` (method body) | `rt_winit_buffer_read_pixel` | read_pixel | legitimate | keep |
| `src/os/compositor/hosted_backend.spl:181` (static create) | `rt_winit_buffer_create` | create | legitimate | keep (only used through `HostedCompositorBackend.create`) |
| `src/os/compositor/hosted_backend.spl:202` (get_pixels) | `rt_winit_buffer_get_pixels` | snapshot | legitimate | keep |
| `src/os/hosted/hosted_entry.spl:17` | (decl) | decl | legitimate | keep |
| `src/os/hosted/hosted_entry.spl:59` | `rt_winit_buffer_create` | create | legitimate | keep — this is the bootstrap site feeding `HostedCompositorBackend.new(win, buf, …)`. (If we accept the `new` vs `create` split, prefer `HostedCompositorBackend.create(win, w, h, BG_COLOR)` and delete this call — see recipe R5.) |
| `src/os/compositor/dual_backend.spl:18-19` | (decls) | decl | **migrate** | R6 — delete decls after body migrates |
| `src/os/compositor/dual_backend.spl:83` | `rt_winit_buffer_get_pixels` | snapshot | **migrate** | R6 — `self.native_backend.get_pixels()` |
| `src/os/compositor/dual_backend.spl:93` | `rt_winit_buffer_save_bmp` | snapshot-to-disk | **migrate** | R6 — add `save_bmp(path)` method to `HostedCompositorBackend`, then `self.native_backend.save_bmp(native_path)` |
| `examples/simple_os/hosted/hosted_wm_compare.spl:26-28` | (decls) | decl | **migrate** | R1 — delete decls |
| `examples/simple_os/hosted/hosted_wm_compare.spl:62` | `rt_winit_buffer_create` | create | **migrate** | R1 — already has `HostedCompositorBackend.create(win, w32, h32, bg_u32)` at :73; drop the raw `buf` handle |
| `examples/simple_os/hosted/hosted_wm_compare.spl:91` | `rt_winit_buffer_present` | present | **migrate** | R2 — `native.present()` |
| `examples/simple_os/hosted/hosted_wm_compare.spl:123` | `rt_winit_buffer_free` | free | **migrate** | R3 — `native.free()` (or drop; backend owns lifetime) |
| `examples/simple_os/hosted/hosted_wm_verify.spl:23-26` | (decls) | decl | **migrate** | R1 — delete decls |
| `examples/simple_os/hosted/hosted_wm_verify.spl:113` | `rt_winit_buffer_create` | create | **migrate** | R1 — route via `HostedCompositorBackend.create(...)` (already used at :117) |
| `examples/simple_os/hosted/hosted_wm_verify.spl:141` | `rt_winit_buffer_save_bmp` | save_bmp | **migrate** | R4 — `backend.save_bmp(bmp_path)` |
| `examples/simple_os/hosted/hosted_wm_verify.spl:146` | `rt_winit_buffer_free` | free | **migrate** | R3 |
| `examples/simple_os/hosted/hosted_wm_verify.spl:163` | `rt_winit_buffer_free` | free | **migrate** | R3 |
| `test/system/os/hosted_wm_system_test.spl:32-36` | (decls) | decl | test-fixture-ok → **migrate** | R1 (test is a WM smoke — should prove trait path) |
| `test/system/os/hosted_wm_system_test.spl:111` | `rt_winit_buffer_fill_rect` | fill | **migrate** | R7 — `backend.fill_rect(x,y,w,h,color)` |
| `test/system/os/hosted_wm_system_test.spl:264` | `rt_winit_buffer_create` | create | **migrate** | R1 |
| `test/system/os/hosted_wm_system_test.spl:279,289,296,303` | `rt_winit_buffer_present` | present | **migrate** | R2 |
| `test/system/os/hosted_wm_system_test.spl:324,398` | `rt_winit_buffer_save_bmp` | save_bmp | **migrate** | R4 |
| `test/system/os/hosted_wm_system_test.spl:576` | `rt_winit_buffer_free` | free | **migrate** | R3 |
| `test/system/os/simpleos_capabilities_test.spl:31-35` | (decls) | decl | test-fixture-ok | keep (explicit FFI capability probe) |
| `test/system/os/simpleos_capabilities_test.spl:104` | `rt_winit_buffer_fill_rect` | fill | test-fixture-ok | keep (probe of FFI) |
| `test/system/os/simpleos_capabilities_test.spl:175` | `rt_winit_buffer_create` | create | test-fixture-ok | keep |
| `test/system/os/simpleos_capabilities_test.spl:181,186,189` | `rt_winit_buffer_present` | present | test-fixture-ok | keep |
| `test/system/os/simpleos_capabilities_test.spl:194` | `rt_winit_buffer_save_bmp` | save | test-fixture-ok | keep |
| `test/system/os/simpleos_capabilities_test.spl:811` | `rt_winit_buffer_free` | free | test-fixture-ok | keep |

**Not found on `origin/main` (flag for plan-doc alignment):**
- `examples/simple_os/hosted/gui_test.spl`
- `examples/simple_os/hosted/hosted_fb.spl`
- `examples/simple_os/hosted/hosted_input.spl`
- `examples/simple_os/hosted/hosted_main.spl`
- `src/app/ui.chromium/main.spl` (referenced by `doc/01_research/domain/v3_shell_choice_2026-04-14.md:159` but not yet present)
- `src/app/ui.browser/**`, `src/app/ui.electron/**` — present but contain **zero** `rt_winit_buffer_*` references. No migration needed there.

**Already migrated (no FFI, uses trait):**
- `examples/simple_os/hosted/hosted_wm.spl` — uses `HostedCompositorBackend.create` at :42, no raw FFI. Good reference.

---

## 4. Migration recipes

**R1 — create/bootstrap**
Replace `val buf = rt_winit_buffer_create(w, h, bg)` *plus* any surrounding
`extern fn rt_winit_buffer_create` decl with:
```
use os.compositor.hosted_backend.{HostedCompositorBackend}
var backend = HostedCompositorBackend.create(win, w32, h32, bg_u32)
```
The backend now owns `buffer_id` internally; callers no longer see it.

**R2 — present**
Replace `rt_winit_buffer_present(win, buf)` with `backend.present()`.

**R3 — free**
Replace `rt_winit_buffer_free(buf)` with `backend.free()` (add this method to
`HostedCompositorBackend` if absent; it wraps the FFI and clears
`_hosted_buffer_id`). If the window itself outlives the backend, call
`rt_winit_window_free` separately — that is out of scope here.

**R4 — save_bmp**
Add `fn save_bmp(path: text) -> bool` to `HostedCompositorBackend` (wraps
`rt_winit_buffer_save_bmp(self.buffer_id, path)`) and migrate callers to
`backend.save_bmp(path)`.

**R5 — fold `hosted_entry.spl:59` create into the static constructor**
Delete `val buf = rt_winit_buffer_create(...)` in `hosted_entry.spl`; have
`HostedCompositorBackend.create(win, WINDOW_WIDTH, WINDOW_HEIGHT, BG_COLOR)`
allocate the buffer. Removes the one remaining external `_create` caller and
makes hosted_backend the sole site that knows the buffer exists.

**R6 — dual_backend snapshot**
- Replace `rt_winit_buffer_get_pixels(self.native_backend.buffer_id)` with
  `self.native_backend.get_pixels()` (trait method already exists at
  `hosted_backend.spl:202`).
- Replace `rt_winit_buffer_save_bmp(...)` with `self.native_backend.save_bmp(...)`
  once R4 lands.

**R7 — fill_rect passthrough (test)**
Replace `rt_winit_buffer_fill_rect(g_buf, x, y, w, h, color)` with
`backend.fill_rect(x, y, w, h, color)`.

---

## 5. Examples/simple_os/hosted migration

This directory is the bulk of the work. Files that actually exist on
`origin/main`:

| File | Status | Action |
|------|--------|--------|
| `hosted_wm.spl` | clean (uses `HostedCompositorBackend.create` already) | **keep** as reference |
| `hosted_wm_compare.spl` | 3 externs + 3 call sites (`create`, `present`, `free`) | **migrate in place** — it already instantiates `HostedCompositorBackend` at :73, so just reroute `buf`-typed calls at :62/:91/:123 through `native.*` and delete the extern block at :26-28. Consider merging into `hosted_wm.spl` once migrated — compare mode can be a flag. |
| `hosted_wm_verify.spl` | 4 externs + 5 call sites (`create`, `save_bmp`, 2× `free`) | **migrate in place**; depends on R4 (`save_bmp` method on backend). Keeps its own module — verify harness is distinct from wm demo. |
| `gui_test.spl`, `hosted_fb.spl`, `hosted_input.spl`, `hosted_main.spl` | **missing on origin/main** | FLAG to plan author: either the plan's file list is stale, or these files land together with the migration commit. No migration work until they appear. |

None of the existing example files should be deleted — they are distinct
entry points (`bin/simple run examples/simple_os/hosted/hosted_wm.spl` etc.).
Do **not** merge them into `src/os/hosted/hosted_entry.spl`; that file is the
production entry and must stay minimal.

---

## 6. Ordering

1. **App-layer callers** — none on `origin/main` today (verified: `src/app/ui.browser/**` and `src/app/ui.electron/**` have zero `rt_winit_buffer_*` hits). Skip.
2. **Example callers** — migrate `hosted_wm_compare.spl`, then `hosted_wm_verify.spl` (blocked on R4: add `save_bmp` to `HostedCompositorBackend` first).
3. **`src/os/compositor/dual_backend.spl`** — migrate the two call sites at :83 and :93 via R6 (depends on R4).
4. **Tests** — migrate `hosted_wm_system_test.spl` (WM smoke should ride the trait). Leave `simpleos_capabilities_test.spl` on raw FFI (it explicitly probes the FFI capability surface).
5. **Optional tightening** — apply R5 to `hosted_entry.spl` so `rt_winit_buffer_create` has exactly one caller (`HostedCompositorBackend.create`).
6. **FFI deletion check** — do NOT delete any `rt_winit_buffer_*` extern. All 10 are still reachable via `HostedCompositorBackend` internals after migration. Only the Simple-side `extern fn` re-declarations in migrated files are deleted.

---

## 7. Acceptance

- [ ] Zero `rt_winit_buffer_*` references outside `src/os/compositor/hosted_backend.spl`, `src/os/hosted/hosted_entry.spl`, `src/compiler_rust/**/winit_ffi.rs`, and `test/system/os/simpleos_capabilities_test.spl` (intentional FFI probe) — verify with `git grep -nE 'rt_winit_buffer_' | grep -v hosted_backend.spl | grep -v 'hosted_entry.spl' | grep -v winit_ffi | grep -v simpleos_capabilities_test`.
- [ ] `HostedCompositorBackend` exposes `fill_rect`, `present`, `free`, `save_bmp`, `get_pixels`, `blend_rect`, `blur_region`, `gradient_v`, `read_pixel` as trait methods; no caller needs `buffer_id` or `window_id` directly.
- [ ] `examples/simple_os/hosted/hosted_wm_compare.spl` and `hosted_wm_verify.spl` run green under `SIMPLE_GUI=1 bin/simple run ...` with no `extern fn rt_winit_buffer_*` in their source.
- [ ] `dual_backend.spl` no longer declares `extern fn rt_winit_buffer_*`; its two call sites at `:83` and `:93` route through `self.native_backend.*`.
- [ ] `test/system/os/hosted_wm_system_test.spl` renders the same BMP as before (byte-identical or pixel-diff < 1), proving the trait path is behavior-preserving vs. the raw-FFI path.
