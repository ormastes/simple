# Chromium Primitive Oracle Dynload Fixture

This directory builds `libsimple_chromium_primitive_oracle` **only as a native
ABI fixture**. It does not link or execute Chromium, Blink, Viz, Electron, a
GPU driver, or the scripts under `tools/web-render-backend/`.

The repository's current Chromium helpers are process-level Electron/Node
tools, not a stable embeddable C ABI. Binding them as a dynamic component would
violate the frozen design. The fixture instead proves that the five ABI-v1
symbols, caller-owned bounded buffers, error extraction, opaque exact-once
handle, and primitive trace envelope work through a real platform `dlopen`.

Its response is deliberately marked:

```
oracle_identity=fixture-not-chromium
device_identity=unavailable
device_origin_readback=false
error_class=fixture-no-gpu
```

Therefore it cannot satisfy Chromium comparison, CPU-pixel, GPU-offload,
Vulkan readback, or no-fallback promotion requirements. A future real bridge
must be built from a pinned Chromium checkout and retain this same C ABI while
changing the manifest identity and producing a genuine independent receipt.

## Prepared real-host broker

`tools/web-render-backend/chromium_primitive_oracle_broker.js` is the
test-only, real-browser child-process endpoint intended for the C ABI bridge.
It uses only Electron's public `BrowserWindow`/`WebContents` API and emits a
receipt only after Electron reports its real Chrome and GPU identities. It
executes the primitive subset (rect/background/border, text, image, pointer,
Ctrl+Alt keyboard, scroll, resize) in a visible Xvfb BrowserWindow so trusted
wheel and viewport-resize delivery can be observed, records CPU-visible `capturePage` pixels,
and explicitly reports GPU receipt **unavailable** because `capturePage` is
not a device-origin readback. It has no fixture response path.

Use the worktree-pinned Electron only:

```sh
sh test/fixtures/chromium_primitive_oracle/run_real_chromium_prepared_host.shs
```

If the pinned `tools/electron-shell/node_modules/.bin/electron` is absent, the
runner exits `2` with `REAL_CHROMIUM_ORACLE_UNAVAILABLE`; install it with the
pinned `npm ci` in that directory. A successful runner receipt is browser
evidence, but still cannot satisfy GPU/no-fallback promotion until a genuine
device-origin readback is added.

Run the fixture on Linux/macOS:

```sh
sh test/fixtures/chromium_primitive_oracle/run_dynload_fixture.shs
```
