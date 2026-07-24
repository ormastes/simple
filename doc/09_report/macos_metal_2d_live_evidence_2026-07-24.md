# macOS Metal 2D Live Evidence

- status: **FAIL**
- reason: no admissible pure-Simple GUI runtime artifact
- source base: `576be2a487176a6ee299be78aa057ada087305aa`
- live cycles consumed: `2/3`
- passing frozen adapter emitted: no
- durable 4K capture emitted: no
- ordered event receipt emitted: no

## Manual

1. launch backend
2. render deterministic scene
3. deliver input events
4. capture framebuffer
5. compare evidence

## Cycle evidence

Cycle 1 used the available GUI-enabled Rust seed diagnostically. It remained in
the 3840x2160 render/font path until the bounded launch timeout and failed with
`render-ready-timeout`. It produced no window receipt, framebuffer capture, or
event receipt.

Cycle 2 replaced the 17.7 MB variable CJK face with the pinned static Bungee
face while retaining the canonical `FontRenderer -> FontRenderBatch -> Metal`
path. The 3840x2160/300-DPI render reached `ready.env` after approximately five
minutes, so a native winit window existed, but the wrapper did not discover the
overlong process name before its deadline. No input was injected and no capture
or event receipt was accepted. This cycle is diagnostic only: its launcher
printed:

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

Neither diagnostic cycle is represented as PASS evidence.

## Pure-Simple native-build gate

The qualified pure-Simple Stage2 compiler was:

`/Users/ormastes/simple/build/worktrees/simple-wm-e3e0c5c4/build/bootstrap-wm-qualified-e3e0c5c4/stage2/aarch64-apple-darwin/simple`

The bounded build used:

```text
SIMPLE_NO_STUB_FALLBACK=1
native-build --source src/lib --source test/02_integration/rendering
--entry-closure
--entry test/02_integration/rendering/macos_metal_2d_live_harness.spl
--runtime-path /Users/ormastes/simple/src/compiler_rust/target/gui/release
--runtime-bundle core-c-bootstrap --backend cranelift --clean --threads 1
--timeout 120 -o build/metal_live_native/macos_metal_2d_live
```

Source/type/code generation completed. Final linking failed closed because the
runtime archive does not define the native GUI ABI, including:

```text
_rt_winit_event_free
_rt_winit_event_get_type
_rt_winit_event_keyboard_input
_rt_winit_event_loop_free
_rt_winit_event_loop_new
_rt_winit_event_loop_poll_events
_rt_winit_event_mouse_button
_rt_winit_window_free
_rt_winit_window_new
_rt_winit_window_present_rgba
```

The same strict link also exposed optional non-Metal backend externs retained by
the common `Engine2D` closure. No native executable was produced. The third
live-cycle slot was intentionally not spent on an inadmissible Rust seed.

## Implemented fail-closed evidence surfaces

- `test/02_integration/rendering/macos_metal_2d_live_harness.spl`
  renders a deterministic 3840x2160 scene at 300 DPI, validates exact pinned
  vector-font identity and cold/warm cache behavior, requires Metal font
  execution, consumes ordered focus/pointer down-up/key down-up events, keeps
  the same Metal framebuffer handle, measures non-background bounds, and writes
  a P6 device-readback capture.
- `scripts/check/check-macos-metal-2d-live-evidence.shs`
  accepts only `METAL_LIVE_NATIVE_BIN` under this worktree's `build/` tree,
  records its SHA-256 in `source_revision`, rejects missing Metal linkage,
  validates the runtime receipt, hashes raw PPM pixel bytes, creates a durable
  PNG derivative, and emits only the frozen adapter fields.

## Reusable host flow

The launcher/event/capture sections can be reused for host `cpu_simd` with:

- `METAL_LIVE_NATIVE_BIN` generalized to a backend native executable path;
- receipt, ready, capture, source-revision, build-directory, report, and timeout
  paths supplied through environment variables;
- the app-bundle launcher, short process name, window discovery, ordered
  `cliclick`/System Events injection, receipt wait, PPM payload hash, PNG
  conversion, and frozen adapter emission retained unchanged;
- backend-specific runtime validation kept outside the generic section.

No shared evidence structs, common Engine2D files, CPU files, Vulkan files, or
QEMU files were modified.
