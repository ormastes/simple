<!-- codex-design -->

# Browser WASM WebGPU Infra GUI Design

The user-facing GUI surface is browser canvas behavior rather than a new app
screen.

## Browser Scene

Simple2D commands produce a bounded canvas command list: fills, text, dimensions,
and WebGPU render submission counters. Simple3D commands produce a bounded scene
record: clear color, camera, mesh count, payload bytes, checksum, and WebGPU
scene submission counters.

## Chrome Evidence

Chrome/Electron helper apps remain evidence tools, not production UI. They
should render a minimal page that:

- Creates a secure browser context.
- Requests a WebGPU adapter/device when available.
- Builds WGSL shader modules and pipelines.
- Submits draw or compute work.
- Returns structured JSON with explicit status and readback fields.

Host-unavailable states are valid GUI evidence when they are explicit and do
not substitute software execution.

## Visual Capture Policy

Pixel screenshots are optional for this lane. Required GUI evidence is structured
object state and WebGPU readback/status JSON. Future hardware-oriented options
may add screenshot or texture readback baselines under `doc/06_spec/image/...`.

