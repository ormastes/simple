# Simple Browser CLI (`src/app/browser/`)

Hosted `app.ui.render`-contract browser app. Renders a page through the real
DOM/CSS/layout/paint engine (`render_html_to_pixel_array`) and reports a
render receipt ("Rendered by Simple Browser engine: 64x36px, N pixels
painted") so output is provably engine-backed, not a placeholder.

## Usage

```bash
bin/simple run src/app/browser/main.spl                # text mode
bin/simple run src/app/browser/main.spl --log-mode=json # HTML-in-JSON mode
bin/simple run src/app/browser/main.spl --open         # real GUI window
bin/simple run src/app/browser/main.spl --help
```

- Default page: `simple://home` (real Hello World page). Pass a URL as the
  positional argument to override.
- Shared log options (`--log-mode`, `--progress`, ...) follow
  `std.cli.log_modes`, same as sibling apps.

## `--open` (real GUI window)

Opens a real OS window via the `GuiRenderer` winit facade
(`src/lib/nogc_sync_mut/ui/gui_renderer.spl`), presents one engine-rendered
frame, and blocks until the window is closed (idle poll sleeps 16ms).

Requirements:
- `build/sffi/libspl_winit.<so|dylib|dll>` — build with
  `scripts/build/build_spl_winit.shs`.
- A reachable display. Linux: X11/Wayland; macOS additionally needs
  `SIMPLE_GUI=1` (winit must run on the main thread).
- Headless verification: run under Xvfb (e.g. a container). Verified recipe
  (2026-08-06): Ubuntu 24.04 + `xvfb imagemagick x11-apps libxkbcommon-x11-0
  libxkbcommon0`, `Xvfb :99`, then
  `DISPLAY=:99 bin/simple run src/app/browser/main.spl --open`; window
  `"Simple Browser - simple://home"` appears in ~60s; screenshot with
  `xwd -id <win> | convert` shows real glyph pixels.

Window/render size is capped at 64x36 (`GUI_WINDOW_WIDTH/HEIGHT` in
`main.spl`) because the engine runs interpreted on this path; see the
ponytail note there before raising it.

## Pitfall: caller-frame silent interpreter fallback

Do NOT move the `browser_engine_pixels_at(...)` call into
`gui_window.spl` (or any module importing extern-heavy modules like
`gui_renderer`): JIT lowering fails silently for that caller frame and the
ENTIRE engine call tree runs tree-walk, ~10-50x slower — a 45-60s render
stops finishing 1800s budgets, with no diagnostic. `main()` renders and
passes ready pixels into `run_browser_window_gui(url, w, h, pixels)` on
purpose. Details and isolation matrix:
`doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`.

## Tests

- `test/01_unit/app/browser/browser_render_adapter_spec.spl` — pure
  dispatch/content logic (engine calls deliberately excluded: one engine
  call alone exceeds the spec runner's 10M-op budget).
- `test/02_integration/app/browser_cli_log_modes_spec.spl` — spawns the real
  CLI (`--help`, `--version`, unknown-option rejection, `--open` parse).

## Renderer sandbox (seccomp allow-list)

Check the jail with:

```bash
sh scripts/check/check-browser-renderer-sandbox-seccomp.shs
```

It builds and runs `src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`,
which forks a child into the **real** jail via `rt_browser_renderer_sandbox_enter`
and proves both directions: allow-listed `read`/`write` on inherited pipe fds
still work, and a non-allow-listed `socket()` is killed with `SIGSYS` by
`SECCOMP_RET_KILL_PROCESS` — not merely refused with `EPERM`, which is what the
pre-2026-08-15 deny-list did. Verdict is the last stdout line; `ERROR — nothing
was checked` (exit 2) covers a kernel without seccomp/Landlock and a host
without a C compiler, and is never a pass.

Two operational notes that cost time otherwise:

- The build **requires** `-ffunction-sections -fdata-sections -Wl,--gc-sections`.
  `runtime_process.c` also defines spawn/fork paths referencing the wider
  runtime's value helpers (`rt_array_len`, `rt_string_data`, `rt_fork_*`) that a
  single-TU build does not link; the self-check never calls them, so they must be
  dead-stripped or the link fails on undefined references.
- The jail sets `RLIMIT_NOFILE=4`, so the in-jail Landlock ruleset fd only
  allocates when the worker holds fds 0..3 only. A worker holding a higher fd
  fails `sandbox_enter`.

### Namespace posture

The jail also unshares the user, network and IPC namespaces and drops to an
unprivileged identity, so the renderer loses its *route* to the network instead
of relying on every socket-creating syscall staying denied. The gate prints:

```
sandbox_namespaces=active        # netns genuinely isolated
sandbox_namespaces=unavailable   # host forbids it, reported honestly
```

`unavailable` is a legitimate result, not a failure. Ubuntu 24.04 ships
`kernel.apparmor_restrict_unprivileged_userns=1`, which permits `CLONE_NEWUSER`
but strips its capabilities so `CLONE_NEWNET` returns `EPERM`. Hard-failing
there would turn a working seccomp+Landlock jail into **no jail** on every
default Ubuntu host. Read the posture with
`rt_browser_renderer_namespaces_active()`; never infer it from a successful
`sandbox_enter()`. Only a false claim — posture `active` while
`/proc/self/ns/net` is unchanged — fails the self-check.

Ordering is load-bearing: namespaces (need `openat` + writable `/proc`) →
Landlock (no allow rules, so all writes die, including `/proc/self/uid_map`) →
seccomp (allow-list has neither `unshare` nor `openat`). PID namespace is
deliberately not unshared: `CLONE_NEWPID` only affects children created after
the unshare, and `RLIMIT_NPROC=0` means the worker cannot fork.

To see the active path, run under a permissive kernel —
`docker run --privileged` flips the same binary to `active` with the netns
identity actually moving. Default Docker and `--security-opt
apparmor=unconfined` both still report `unavailable`.

Still open (see
`doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md`):
the in-process browsers under `src/app/browser/**` evaluate page script in the
host process without entering the jail at all. The gate proves the jail's
syscall and namespace contract, not that every browser surface uses it.

## Related

- Feature expert: `doc/00_llm_process/feature_expert/browser/skill.md`
- Sandbox system scenario: `test/03_system/browser_engine/browser_renderer_sandbox_spec.spl`
  (manual: `doc/06_spec/03_system/browser_engine/browser_renderer_sandbox_spec.md`)
- Engine internals: `doc/07_guide/ui/browser_engine_implementation.md`
- Don't confuse with `src/app/ui.browser/` (standalone winit widget-tree
  app) or `src/os/apps/simple_browser/` (baremetal).
