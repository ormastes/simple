# Breakout real window capture (W5b, G3.3)

> Opens a real window (via `SdlBackend` -> `rt_winit_*`), presents a scripted

<!-- sdn-diagram:id=breakout_window_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakout_window_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakout_window_capture_spec -> std
breakout_window_capture_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakout_window_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakout real window capture (W5b, G3.3)

Opens a real window (via `SdlBackend` -> `rt_winit_*`), presents a scripted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| Runtime \| Game2D |
| Status | Active |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3) |
| Source | `test/03_system/game2d/breakout_window_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Opens a real window (via `SdlBackend` -> `rt_winit_*`), presents a scripted
autopilot session, then sleeps so an external `xwd` capture (run by
`scripts/check/check-game2d-breakout.shs`) can grab the live X11 window.

HOST GATE: the window scenario only runs when `SIMPLE_BREAKOUT_WINDOW=1`
(exported by the check script after probing that the binary actually
implements the window externs). Without it, the spec records
`window_backend=blocked_host` and asserts the tracked gap doc exists.
The deployed self-hosted `bin/simple` still lacks `rt_winit_*`; the existing
gui-feature Rust driver binary (`src/compiler_rust/target/debug/simple`,
built with `cargo build -p simple-driver --bin simple --features gui`) exposes
the real winit path and is selected by `scripts/check/check-game2d-breakout.shs`
for this window leg when present. See
doc/08_tracking/bug/game2d_no_window_externs_in_host_binaries_2026-07-03.md.
Same recorded-block convention as the G5.2 Android-emulator gate.

SAFETY: when the window scenario does run, it creates a real on-screen
window. It must only ever run with `DISPLAY` pointed at a private Xvfb
display — never the live desktop session (`scripts/gui/linux-gui-run.shs`
documents the 2026-07-02 incident that motivated this). The check script is
the only sanctioned caller; it starts its own Xvfb and exports `DISPLAY`.

Runs via the test runner in interpreter mode, not `simple run` — see
doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md.

## Scenarios

### Breakout real window (G3.3)

#### presents an autopilot session in a real window, or records the host block

- assert true
- var backend = SdlBackend create
- assert true
- var app = Game new game
- var driver = LoopDriver new
- driver step
- driver step
- rt sleep ms
- backend gb shutdown
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: `return` does not exit an `it` block — use if/else.
if rt_env_get("SIMPLE_BREAKOUT_WINDOW") != "1":
    print "window_backend=blocked_host reason=no_window_externs_in_binary tracked_gap={GAP_DOC}"
    assert_true(file_exists(GAP_DOC))
else:
    var backend = SdlBackend.create()
    val cfg = WindowConfig(
        title: "Simple Breakout",
        width: 320,
        height: 240,
        fullscreen: false,
        vsync: true,
        pixel_scale: 1
    )
    val win = backend.gb_create_window(cfg)
    assert_true(win.raw != 0)

    var app = Game.new_game()
    var driver = LoopDriver.new(60)
    var events: [Event] = []
    val _ = backend.poll_native_events(events)
    driver.step(app, backend, start_snap(), 16_666_667)

    var i: i64 = 0
    while i < 12:
        val _ = backend.poll_native_events(events)
        driver.step(app, backend, chase_snap(app), 16_666_667)
        i = i + 1
    print "window_frames_presented={i} score={app.score} state={app.state}"

    # Hold the window open so an external xwd/import capture can run.
    rt_sleep_ms(10000)

    backend.gb_shutdown()
    assert_true(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3))


</details>
