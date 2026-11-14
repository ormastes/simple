# Simple RenderDoc Feature Expert

## Role

Own SPipe/LLM process knowledge for **Simple RenderDoc**, the repo-native
**Simple 2D RenderDoc Backend Equivalence** capsule. It is Simple's counterpart
for deterministic render records, validation, field-level diff, exact
equivalence, guest/board receipts, and external capture inspection. It is not a
RenderDoc fork and is broader than the `capture-simple` wrapper.

## Implemented Core

```sh
bin/simple test test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl --mode=interpreter
bin/simple test test/02_integration/rendering/backend_render_equivalence_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/renderdoc_replay_inspect_spec.spl --mode=interpreter
```

These cover the pure record model, fail-closed validation, canonical form,
first/all differences, exact equivalence policy, and pure-Simple parsing of
RenderDoc XML conversion. Focused verification passed 6/6, 5/5, and 5/5 on
2026-07-27.

## External Capture Bridge

```sh
scripts/tool/renderdoc-evidence.shs capture-simple
RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
  sh scripts/check/check-renderdoc-simple-gate.shs
```

External `.rdc` replay-open/action evidence corroborates the Simple record; it
does not replace the record, exact pixel oracle, or independent producer. The
producer emits a lowercase SHA-256 and the Simple gate recomputes it before and
after replay so substituted or concurrently changed capture bytes fail closed.

## Current Gaps

- Fresh native Windows/macOS, physical-board, and live RenderDoc evidence
  remains external to a Linux-only run.
- A host-matched deployed pure-Simple release binary is mandatory; a Rust seed
  is rejected rather than accepted as capture or SSpec evidence.
- QEMU and full bootstrap qualification must run in a fresh environment after
  their bounded retry caps are exhausted.

Until these are implemented, report the counterpart as **core implemented,
aggregate incomplete**.

## Aggregate

```sh
sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --self-test
sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --profile=focused
```

The wrapper reports all focused, QEMU, and external rows, rejects non-Stage-4
Simple binaries, preserves leaf logs/artifacts, measures elapsed time and RSS,
and exposes every explicit fail helper as a blocker. Its SSpec contract is
`test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl`.
The 2026-07-27 focused lane remains blocked where a deployed pure-Simple runner
or live RenderDoc/native-host artifact is unavailable.

## Owners

- Requirements: `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- Architecture: `doc/04_architecture/simple_2d_renderdoc_backend_equivalence.md`
- Design: `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- Core: `src/lib/common/renderdoc/backend_render_record.spl`
- RDC inspector: `src/app/test/renderdoc_replay_inspect.spl`
- QEMU/board schemas: `src/lib/common/renderdoc/simpleos_render_target_evidence.spl`,
  `src/lib/common/renderdoc/simpleos_simd_render_evidence.spl`
- Guide: `doc/07_guide/tooling/renderdoc_capture_infra.md`
- Shared tool: `scripts/tool/renderdoc-evidence.shs`
- Shared capture/schema helper: `scripts/lib/renderdoc-evidence-common.shs`
- Glossary: `doc/glossary.md`

## Update Rule

When record schema, facade capture, QEMU receipts, external bridges, or
acceptance rules change, update this entry and the canonical guide in the same
SPipe lane. Never replace explicit fail placeholders with false-green passes.

## Linux aarch64, no root — 2026-11-14

- RenderDoc v1.36 builds without root (clang/lld 23, Ninja; only
  `libx11-xcb-dev` and `libxcb-keysyms1-dev` needed `apt-get download` +
  `dpkg-deb -x`; lld 23 needs `-Wl,--undefined-version`). `renderdoccmd` then
  drives `scripts/check/check-renderdoc-web-capture-lane.shs`.
- **The lanes expect an INSTALLED tree.** `rdoc_capture_simple_vulkan` sets
  `VK_LAYER_PATH`, which replaces loader discovery, from
  `$RDOC_HOME/etc/vulkan/implicit_layer.d/renderdoc_capture.json`. A build tree
  has no `etc/`, the layer never loads, and the in-app API still answers
  `available=1 start=1` — the run ends `num_captures=0` with no cause named.
  The helper now reports `missing-renderdoc-layer-manifest:<path>`.
- **Start the capture after the device exists.** A start issued before the
  first `vkCreateDevice` returns 1 and captures nothing (re-verified with the
  layer loaded: original program `num_captures=0`). Dropping the warm-up
  engine afterwards is harmless — the shared session keeps the device.
  `renderdoc_web_page_capture.spl` now follows `renderdoc_vulkan_capture.spl`.
- **NVIDIA GB10 (driver 580.173) rejects `vkCreateDevice` with the RenderDoc
  layer in the chain** (5 of 5 attempts, `VK_ERROR_INITIALIZATION_FAILED`);
  llvmpipe accepts it. Capture with `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`.
  Measured: `overview.simple.rdc` 486756 bytes at 900x760.
- `RDOC_WEB_CHROME_BIN` was honoured only in `RDOC_WEB_TOOL_SEARCH=isolated`
  mode; fixed. The Chrome side still ends `vulkan-angle-unavailable` on a host
  with no display and no Xvfb.
- **The replay inspector reads command names from `<chunk …>` opening tags
  only** (`_chunk_tags`, one `split` pass). It used to count `name="vkCmd…"`
  anywhere, so `<metadata name="vkCmdDispatch">` passed as a dispatch.
  Real capture check (web7 `overview.simple.rdc` → 1.8 MB XML, 1637 chunks):
  pass, 205 dispatches, 5 pipelines, 5 shaders, 33 resources, 8.8 s wall.
- `renderdoc_simple_gate_spec` needs a runnable inspector binary: in a
  worktree with no `bin/simple` set `RDOC_REPLAY_SIMPLE_BIN`, otherwise every
  replay reason is `simple-replay-inspector-missing`.
