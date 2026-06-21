# SPipe Guide

The canonical testing guide lives at:

**[doc/07_guide/testing/testing.md](../../07_guide/testing/testing.md)**

This file (formerly `doc/06_spec/app/compiler/spipe_guide.md`) is kept as a
pointer because the SPipe rename (2026-04-26) consolidated all skill+doc
material under `doc/00_llm_process/spipe/`.

For test-writing skill details see [`skill.md`](skill.md).
For the continuous-check loop see [`loop.md`](loop.md).

For GUI/web/2D tests that claim Vulkan-backed rendering, pair SPipe assertions
with the macOS-first RenderDoc workflow in
`doc/07_guide/tooling/renderdoc_capture_infra.md`. The canonical setup command
is:

```bash
SIMPLE_BIN=src/compiler_rust/target/release/simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc
```

Completion requires Electron Chromium, original Chrome, and pure-Simple
Engine2D evidence from the same fixture plus RenderDoc `.rdc` files with `RDOC`
magic. Browser bitmaps with `vulkan-angle-unavailable` are fallback evidence,
not a Vulkan pass.
