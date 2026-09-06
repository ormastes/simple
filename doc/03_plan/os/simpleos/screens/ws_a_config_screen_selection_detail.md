# Workstream A — Config-selectable boot screen type (detail plan)

**Campaign:** `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` (Workstream A)
**Design:** `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` §2.1
**SPipe state:** `.spipe/simpleos-screens-render-lane/state.md` AC-1, AC-2
**Scope:** make the SimpleOS boot screen selectable across `wm` (default, = today), `2d`, `web`, `gui`.
**Non-goal:** `ScreenHost` refactor (Workstream B), showcase content (WS C), SIMD (WS D).

---

## 0. Ground truth (verified 2026-08-06)

| Fact | Location |
|---|---|
| rc.conf reader is boolean-only; `rc_conf_service_enabled` returns **true** when file or key absent | `src/os/kernel/boot/rc_conf.spl:18-30` |
| `rc_conf_hostname()` is the *only* string accessor today, defaults `"simpleos"` | `rc_conf.spl:32-37` |
| `_rc_conf_lookup(key) -> text?` — private, already returns quote-stripped `text?` | `rc_conf.spl:57-79` |
| `_is_known_key` whitelist = `hostname` or `*_enable` | `rc_conf.spl:81-84` |
| `_strip_quotes` handles `"…"` only | `rc_conf.spl:86-89` |
| `init_all_services()` calls display at `svc_display_ok = _init_display_service()` | `src/os/kernel/boot/init_services.spl:114` (fn at :63) |
| `_init_display_service()` hardcodes `bga_init_framebuffer(1024, 768, 32)` and returns `true` unconditionally | `init_services.spl:179-190` |
| `CompositorBackend` trait: `width/height/clear/fill_rect/draw_text/draw_char_8x16/put_pixel/blit_pixels/present/present_rect/as_glass_capable` | `src/os/compositor/display_backend_core.spl:7-18` |
| `CompositorGlassCapable`: `blend_rect/blur_region/gradient_v/read_pixel` | `display_backend_core.spl:1-5` |
| `FramebufferBackend.create(fb: FramebufferDriver, keyboard: Ps2Keyboard)` (impls `RenderBackend`, not `CompositorBackend`) | `src/os/compositor/fb_backend.spl:108-131` |
| `GpuCompositorBackend.new(driver: VirtioGpuDriver)` | `src/os/compositor/display_backend.spl:12-20` |
| `Engine2dCompositorBackend.create(engine)` / `.create_named(w,h,backend_name)` / `.create_from_env(w,h)`; env key `SIMPLE_GUI_BACKEND` via `host_wm_render_backend_key()` | `src/os/compositor/compositor_engine2d.spl:44,81,110,114` |
| `browser_compositor_backend(width, height) -> BrowserCompositorBackend` impls `CompositorBackend` | `src/os/compositor/browser_compositor_backend.spl:37,48` |
| `select_hosted_backend(window_id, w, h, title, fill_color) -> CompositorBackend?` — probes SDL2/Cocoa/Win32, **nil when no real window** | `src/os/compositor/hosted_backend.spl:328` |
| `BaremetalEngine2dOverlayBackend` + `baremetal_engine2d_overlay_backend(engine, screen_w, screen_h)` | `src/os/desktop/shell_baremetal.spl:19,65` |
| `create_fb_engine_sized(fb, w, h) -> Engine2D`, `create_virtio_gpu_engine(gpu)` | `src/os/compositor/engine2d_display.spl:46,73` |
| `compositor_render_html_artifact_with_backend(req, html, backend_name)` | `src/os/compositor/web_render_surface.spl:28` |
| `SimpleGuiHostedWm` / `SimpleGuiHostedWindow` classes | `src/os/compositor/simple_gui_hosted_wm.spl:13,31` |
| `SimpleOsRuntimeProfile` fields incl. `supports_framebuffer/supports_wm/supports_simple2d_engine2d/requires_vulkan`; capability lookup `profile_supports_capability(profile, capability)` with keys `framebuffer`,`wm`,`simple2d-engine2d`,`vulkan`,`gpu` | `src/os/simpleos_config_matrix.spl:1-15, 373-395` |
| Image builder stages rc.conf from `_rc_conf_template()` = `hostname="simpleos"\nsshd_enable="NO"\nsimpleos_desktop="YES"\n` | `src/os/installer/image_builder.spl:210, 975-976` |
| `SIMPLE_2D_BACKEND` is the **renderer** (software/vulkan/cpu_simd) env, orthogonal to screen type | `src/lib/gc_async_mut/gpu/engine2d/bridge_game2d.spl:6`, `.../simple_web_html_layout_renderer_paint_tiles_gpu.spl:45-48` |
| Existing `"auto"` resolver worth mirroring: `simple_web_resolved_engine2d_backend_name(width, height, "auto")` | `src/app/wm_showcase/session.spl:66, 334` |
| Evidence checker parses `key=value` lines via `line_value`/`evidence_value`, statuses `pass`/`missing` | `scripts/check/check_simpleos_multiconfig_live_evidence.spl:43-74` |
| Required-key lists live in `simpleos_multiconfig_live_required_evidence_keys()` | `simpleos_config_matrix.spl:594` |

**Key architectural constraint:** `SimpleOsRuntimeProfile` is the *test-gating* contract. It must **feed** selection (as an input value passed in) and never **become** runtime policy — the factory takes a profile as a parameter and never imports/constructs one itself.

---

## A1 — rc.conf string-valued keys

**Objective:** accept `screen_type`, `screen_res`, `screen_simd` as string keys; keep `*_enable` boolean semantics and default-true-when-absent byte-identical.

**Files:** `src/os/kernel/boot/rc_conf.spl` (edit), `test/01_unit/os/kernel/boot/rc_conf_spec.spl` (new).

**Changes:**

1. Promote the lookup to public, unchanged body:
```
pub fn rc_conf_value(key: text) -> text?:
    """Raw quote-stripped value for any rc.conf key, or nil when the file is
    absent or the key is not present. String-valued counterpart to
    rc_conf_service_enabled; performs NO validation."""
    _rc_conf_lookup(key)
```
   Keep `_rc_conf_lookup` as the implementation (do not delete or rename — `rc_conf_service_enabled:27`, `rc_conf_hostname:34`, `rc_conf_service_marker:47` call it).

2. Extend the whitelist at `rc_conf.spl:81`:
```
val RC_CONF_STRING_KEYS: [text] = ["hostname", "screen_type", "screen_res", "screen_simd"]

fn _is_known_key(key: text) -> bool:
    if key.ends_with("_enable"):
        return true
    for k in RC_CONF_STRING_KEYS:
        if key == k:
            return true
    false
```
   Do **not** use a `Dict` here (see Traps §T1). Array scan of 4 entries is the right cost.

3. Validated accessors, fail-closed, each logging its reason:
```
val SCREEN_TYPES: [text] = ["wm", "2d", "web", "gui"]

pub fn rc_conf_screen_type() -> text:
    """Configured boot screen type, normalized. Fails closed to "wm" (today's
    behavior) on absent, empty, or unrecognized values — never a blank screen."""
    val found = rc_conf_value("screen_type")
    if found == nil:
        return "wm"
    val raw = found.unwrap().trim().to_lower()
    if raw == "":
        serial_println("[rc] screen_type empty -> wm")
        return "wm"
    for t in SCREEN_TYPES:
        if raw == t:
            return raw
    serial_println("[rc] screen_type={raw} unrecognized -> wm")
    "wm"

pub fn rc_conf_screen_res(default_w: i32, default_h: i32) -> (i32, i32):
    """Parse `screen_res="WxH"`. Fails closed to the passed defaults, which the
    kernel supplies as 1024x768 (today's hardcoded BGA mode)."""
    # split on "x"; both parts must parse >0 and <= 8192 else log + defaults

pub fn rc_conf_screen_simd() -> text:
    """`screen_simd="auto|on|off"`, default "auto"; unrecognized -> "auto" + log."""

pub fn rc_conf_screen_type_marker() -> text:
    """Boot-log marker mirroring rc_conf_service_marker's shape."""
    val found = rc_conf_value("screen_type")
    val source = if found == nil: "default" else: "rc.conf"
    "[rc] screen_type={rc_conf_screen_type()} ({source})"
```
   `screen_res` parsing must not use `.to_i64()` on a chained call (Traps §T2): bind an intermediate typed `val` first.

4. `image_builder.spl:975` `_rc_conf_template()` gains a commented default so staged images document the key without changing behavior:
```
"hostname=\"simpleos\"\nsshd_enable=\"NO\"\nsimpleos_desktop=\"YES\"\nscreen_type=\"wm\"\n"
```
   Update the `_manifest_file("/etc/rc.conf", ...)` row only if its content hash is recorded (check `image_builder.spl:223`).

**Acceptance:**
```
bin/simple test test/01_unit/os/kernel/boot/rc_conf_spec.spl --no-cache --no-cover-check
```
Expected: verdict line naming a nonzero example count, `0 failed`. Spec must cover: absent file → `wm`; `screen_type="2d"` → `2d`; `screen_type="  GUI "` → `gui`; `screen_type="quake"` → `wm` + marker says `rc.conf`; `screen_type=` (empty) → `wm`; `screen_res="1920x1080"` → `(1920,1080)`; `screen_res="junk"` → defaults; unchanged: `sshd_enable="NO"` → false, missing `foo_enable` → true.

**Deps:** none. **Model:** sonnet.

---

## A2 — `src/os/compositor/backend_factory.spl`

**Objective:** one registry keyed by screen type that constructs the matching `CompositorBackend` + screen app shell, fail-closed against a *passed-in* profile.

**Files:** new `src/os/compositor/backend_factory.spl`; new `test/01_unit/os/compositor/backend_factory_spec.spl`. Add the module to `src/os/compositor/mod.spl`.

**API:**
```
use os.compositor.display_backend_core.*
use os.simpleos_config_matrix.{SimpleOsRuntimeProfile, profile_supports_capability}

enum ScreenType:
    Wm
    Two D          # spelled TwoD
    Web
    Gui

pub fn screen_type_from_text(name: text) -> ScreenType    # unknown -> Wm (already normalized by A1)
pub fn screen_type_name(t: ScreenType) -> text            # "wm"|"2d"|"web"|"gui"

class ScreenSelection:
    requested: text        # what rc.conf / env asked for
    effective: text        # what we actually built
    reason: text           # "" when requested == effective, else why we fell back
    backend: CompositorBackend?
    shell: text            # app-shell entrypoint key the desktop launcher dispatches on

pub fn screen_capability_key(t: ScreenType) -> text
    # Wm -> "wm"; TwoD -> "simple2d-engine2d"; Web -> "framebuffer"; Gui -> "framebuffer"

pub fn resolve_screen_type(
    requested: text,
    profile: SimpleOsRuntimeProfile
) -> (text, text)
    """Pure. Returns (effective, reason). Consults ONLY
    profile_supports_capability(profile, screen_capability_key(t)). Fallback
    chain: requested -> "2d" (if simple2d-engine2d supported) -> "wm" ->
    "wm" unconditionally (wm is the never-blank floor). reason is "" on a
    clean hit, else "unsupported:<requested>:<capability>"."""

pub fn create_screen_backend(
    requested: text,
    width: i32,
    height: i32,
    profile: SimpleOsRuntimeProfile
) -> ScreenSelection
    """Impure: resolves, then constructs. Never returns nil backend for "wm"
    unless the framebuffer itself failed, in which case effective="wm" and
    backend=nil and reason="fb-init-failed" — caller logs and continues headless
    rather than blanking."""
```
`resolve_screen_type` is the whole testable core; `create_screen_backend` is a thin constructor switch so specs can assert selection without any device.

**Registry shape:** a `match` in `create_screen_backend` over `ScreenType` — **not** a `Dict<text, fn>`. Rationale: 4 entries, and dicts of struct/closure values are unsafe under native codegen (Traps §T1). If a data-driven table is wanted later it is `[(text, text)]` pairs scanned linearly.

**Per-type construction:**

| type | guest (baremetal) construction | host construction | reachable on baremetal today? |
|---|---|---|---|
| `wm` | `bga_init_framebuffer(w,h,32)` → `FramebufferDriver` → existing WM path; keeps `_init_display_service` behavior exactly | `select_hosted_backend(window_id, w, h, title, fill)` (`hosted_backend.spl:328`) | **yes** — this is today's path |
| `2d` | `create_fb_engine_sized(fb, w, h)` (`engine2d_display.spl:46`) → `baremetal_engine2d_overlay_backend(engine, w, h)` (`shell_baremetal.spl:65`); with VirtIO-GPU present, `create_virtio_gpu_engine(gpu)` (`engine2d_display.spl:73`) | `Engine2dCompositorBackend.create_named(w, h, backend_name)` where `backend_name` comes from the renderer env (`SIMPLE_2D_BACKEND`, resolved "auto"-style like `session.spl:334`) | **yes** |
| `web` | `browser_compositor_backend(w, h)` (`browser_compositor_backend.spl:37`) blitted onto the fb backend; page pixels via `compositor_render_html_artifact_with_backend` (`web_render_surface.spl:28`) | same `browser_compositor_backend` | **partial** — backend is pure-pixel so it composes on the guest fb, but the HTML engine + net stack are host-side today. Guest story: guest renders a **static local page** from the rootfs; remote fetch stays host-only until the netstack lands. Record that limit in the fallback reason. |
| `gui` | none — `SimpleGuiHostedWm` (`simple_gui_hosted_wm.spl:31`) needs a host window server | `select_hosted_backend(...)` + `SimpleGuiHostedWm` window/tab model | **no** — host-only. On baremetal `gui` resolves to `2d` with `reason="unsupported:gui:host-window-server"`, and the guest-side plan is that `gui` becomes reachable only once WS-B's `ScreenHost` gives `gui` an in-guest surface impl. Do not fake it. |

**Log line format** (single line, greppable, emitted once at selection):
```
[screen] requested=<r> effective=<e> profile=<profile.name> reason=<reason-or-none> res=<w>x<h>
```

**Acceptance:**
```
bin/simple test test/01_unit/os/compositor/backend_factory_spec.spl --no-cache --no-cover-check
```
Spec asserts, using `fpga_riscv64_serial_profile()` (all caps false, `simpleos_config_matrix.spl:353`) and `qemu_riscv64_desktop_profile()` (all true, :335):
- desktop profile + `"2d"` → `("2d", "")`
- desktop profile + `"gui"` → `("gui", "")`
- fpga profile + `"2d"` → `("wm", "unsupported:2d:simple2d-engine2d")`
- fpga profile + `"web"` → `("wm", …)`
- any profile + `"wm"` → `("wm", "")`
- unknown text `"quake"` → `("wm", "")` (A1 already normalized; factory re-normalizes defensively)

**Deps:** A1. **Model:** sonnet.

---

## A3 — Rewrite `_init_display_service()`

**Objective:** route boot display through the factory; absent `screen_type` reproduces today's boot byte-for-byte.

**Files:** `src/os/kernel/boot/init_services.spl` (fn at :179, call site :114).

**Change:**
```
use os.kernel.boot.rc_conf.{rc_conf_screen_type, rc_conf_screen_res, rc_conf_screen_type_marker}
use os.compositor.backend_factory.{create_screen_backend, ScreenSelection}
use os.simpleos_config_matrix.{boot_runtime_profile}   # see note

fn _init_display_service() -> bool:
    """Initialize the boot display for the rc.conf-selected screen type.

    Absent/`wm` screen_type reproduces the historical path exactly:
    BGA 1024x768x32 via bga_init_framebuffer.
    """
    val requested = rc_conf_screen_type()
    val res = rc_conf_screen_res(1024, 768)   # today's hardcoded BGA mode
    val w = res.0
    val h = res.1
    log_raw_println(rc_conf_screen_type_marker())
    if requested == "wm":
        log_raw_println("[display] Attempting BGA framebuffer init...")
        val fb_info = bga_init_framebuffer(w, h, 32)
        log_raw_println("[display] BGA framebuffer: {w}x{h}x32bpp initialized")
        log_raw_println("[screen] requested=wm effective=wm profile=boot reason=none res={w}x{h}")
        return true
    val sel = create_screen_backend(requested, w, h, boot_runtime_profile())
    log_raw_println("[screen] requested={sel.requested} effective={sel.effective} profile=boot reason={_reason_or_none(sel.reason)} res={w}x{h}")
    sel.backend != nil
```
The `requested == "wm"` early return is deliberate: it guarantees zero behavior drift for existing images and gates on nothing. Do not "simplify" it into the factory path.

`boot_runtime_profile()` does not exist yet — add a small kernel-side profile provider (in `init_services.spl` or a new `src/os/kernel/boot/boot_profile.spl`) that constructs a `SimpleOsRuntimeProfile` from what the kernel actually detected (pcimgr GPU presence, fb availability). **Do not** call `qemu_riscv64_desktop_profile()` from the kernel — that would turn the test contract into runtime policy. The kernel builds its own profile value and passes it in; the test profiles remain test-only inputs to the same pure function.

**Acceptance:** boot QEMU with no `screen_type` in rc.conf and diff the serial transcript against a pre-change capture — the `[display] BGA framebuffer: 1024x768x32bpp initialized` line must be present and identical; the only addition is the two `[rc]`/`[screen]` lines.
```
sh scripts/check/check-simpleos-multiconfig-live-evidence.shs   # or the wrapper A4 extends
grep -c '\[display\] BGA framebuffer: 1024x768x32bpp initialized' <serial-log>   # == 1
```

**Deps:** A2. **Model:** sonnet.

---

## A4 — Host parity: `SIMPLE_SCREEN_TYPE`

**Objective:** host showcases select the same screen type by env, with the same normalization and fallback code path.

**Files:** `src/os/compositor/backend_factory.spl` (add), host showcase entry (`src/app/wm_showcase/session.spl` and the WS-C mains once they exist).

```
pub fn screen_type_from_env_or(default_type: text) -> text:
    """Host mirror of rc_conf_screen_type(). Reads SIMPLE_SCREEN_TYPE, applies
    the identical normalization + fail-closed-to-wm rule. Guest reads rc.conf,
    host reads env; BOTH then call resolve_screen_type, so the decision logic
    exists once."""
```
**Relationship to `SIMPLE_2D_BACKEND`:** orthogonal, two axes.
- `SIMPLE_SCREEN_TYPE` = *which screen* (`wm|2d|web|gui`) — chooses the `CompositorBackend` + shell.
- `SIMPLE_2D_BACKEND` = *which renderer* inside the 2d/engine2d lane (`software|vulkan|cpu_simd|auto`) — consumed by `Engine2dCompositorBackend.create_named` / `create_from_env` (`compositor_engine2d.spl:110,114`).
`SIMPLE_2D_BACKEND` keeps its current meaning and precedence; the factory reads it **only** for the `2d` and `web` arms, resolving `"auto"` the way `session.spl:334` already does via `simple_web_resolved_engine2d_backend_name(w, h, "auto")`. Do not overload one env into the other. Note `compositor_engine2d.spl:44` also reads `SIMPLE_GUI_BACKEND` for host-WM keying — leave it alone.

**Acceptance:**
```
SIMPLE_SCREEN_TYPE=2d bin/simple run src/app/wm_showcase/main.spl 2>&1 | grep '^\[screen\] '
```
Expected exactly one line with `requested=2d effective=2d`. And `SIMPLE_SCREEN_TYPE=bogus …` → `requested=bogus effective=wm reason=…`.

**Deps:** A2. Parallel with A3. **Model:** sonnet.

---

## A5 — QEMU evidence for all four screen types

**Objective:** captured (not asserted) proof each screen type boots and paints.

**Files to extend (do not create a new lane):**
- `scripts/check/check_simpleos_multiconfig_live_evidence.spl` — the parser/verdict logic (`line_value:43`, `evidence_value:50`, `status_or_default:58`).
- `src/os/simpleos_config_matrix.spl:594` `simpleos_multiconfig_live_required_evidence_keys()` — add the new required keys so a missing row is a **fail**, not a silent pass.
- the `check-simpleos-*` shell wrapper that produces the evidence file, plus the QMP screendump helper already used by `check-simpleos-arm64-qmp-input-evidence.shs`.

**Evidence rows, per type `T ∈ {wm,2d,web,gui}`:**
```
simpleos_screen_<T>_boot_status=pass|fail|skipped:<reason>
simpleos_screen_<T>_selected_effective=<wm|2d|web|gui>
simpleos_screen_<T>_serial_marker_count=<n>          # count of "[screen] effective=<T>" in serial log
simpleos_screen_<T>_screendump_path=<abs path to .ppm>
simpleos_screen_<T>_screendump_bytes=<n>
simpleos_screen_<T>_screendump_distinct_colors=<n>   # nonblank proof
simpleos_screen_<T>_fallback_reason=<reason|none>
```
Pass rule per type: `serial_marker_count >= 1` **and** `selected_effective == T` **and** `screendump_distinct_colors > 1` (a blank screen has exactly 1). Reuse `evidence_gt_four_text`-style predicates (`check_simpleos_multiconfig_live_evidence.spl:70`) for the color count; add `evidence_gt_one_text`.

**Fail-closed default:** every new key defaults to `missing` in `status_or_default`, and `missing` maps to overall `fail`. `gui` on a baremetal guest is expected to report `simpleos_screen_gui_boot_status=skipped:host-window-server-unavailable` with `selected_effective=2d` — a *declared* skip with a reason, recorded in the plan and the evidence, never an unexplained pass. Do not mark the AC green while any type is `skipped`; AC-2 requires all four.

**Acceptance:**
```
bin/simple run scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence <file>
```
Expected last line: a verdict naming the number of keys checked; deleting any one `simpleos_screen_*` row must flip it to `fail` (prove the gate by deleting a row, per "evidence must be captured, not asserted").

**Deps:** A3, A4. **Model:** sonnet.

---

## Traps

- **T1 — Native dict pitfalls.** Under native codegen `Dict.len()` returns `-1` and `.get()` on struct/class/enum values is corrupt (`.claude/rules/code-style.md`; `doc/07_guide/language/dict_native_pitfalls.md`). The backend registry must be a `match` or an array of pairs — **never** `Dict<text, ScreenBackend>`. If a dict is unavoidable, use `contains_key(k)` + index read `d[k]`, and `keys().len()`.
- **T2 — Chained methods on erased receivers.** `.trim().to_i64()` returns garbage under JIT (memory: `jit_chained_method_to_i64_returns_garbage`). In `rc_conf_screen_res`, bind each split part to a typed `val` before parsing.
- **T3 — Evidence must be captured, not asserted.** A spec that asserts "the screendump is nonblank" without a real `.ppm` on disk is vacuous. A4's gate must be provable by deleting an evidence row and watching the verdict flip.
- **T4 — Never skip a failing test.** If `gui` cannot boot on the guest, that is a **declared skip with a reason in the evidence file** plus an open item — not a removed assertion and not a green AC.
- **T5 — Never a blank screen.** Every fallback edge terminates at `wm`; `wm` itself never gates on a capability flag. A selection that yields a nil backend must log and continue, not blank.
- **T6 — Profile is a test contract.** `SimpleOsRuntimeProfile` is consumed as a *parameter* of a pure function. The kernel constructs its own profile from detected hardware. Never import `qemu_riscv64_desktop_profile()` into `src/os/kernel/**`.
- **T7 — Verdict buried under lint noise.** `bin/simple test` output can bury the verdict; read the last line explicitly and use `--no-cache --no-cover-check` (concurrent runs race a shared manifest → "0 tests found").
- **T8 — Text interpolation with braces.** `"{w}x{h}"` is fine, but any literal `{` in a log format string is parsed as interpolation (memory: `text_literal_css_braces_parse_as_interpolation`). Keep the `[screen]` line brace-free apart from real substitutions.
- **T9 — SSpec house style.** Follow `test/01_unit/os/simpleos_config_matrix_spec.spl`: `# @tag:` first line, module docstring with Feature IDs / Category / Status / Plan, `use std.spec.*`, then explicit `use` of the symbols under test. See `.claude/skills/spipe`.

## Dependency graph

```
A1 ──> A2 ──┬──> A3 ──┐
            └──> A4 ──┴──> A5
```
