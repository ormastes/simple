<!-- codex-design -->
# Chromium Web Renderer Primitive Differential — Detail Design

## Execution flow

1. `make_chromium_primitive_fixture` validates the v1 bounded primitive subset
   and emits canonical fixture JSON.
2. `chromium_oracle_load` validates explicit manifest identity, SHA-256, ABI
   version and complete symbol list once. It returns a structured unavailable
   result rather than a fabricated observation.
3. `run_chromium_primitive_reference` creates a bridge session, executes the
   fixture/event script, copies bounded JSON, and always releases the opaque
   handle.
4. `ChromiumPrimitiveTraceConverter` produces only `TraceEvent` and
   `NormalizedTrace`; `SimplePrimitiveTraceConverter` projects the existing
   Simple semantic/layout/DrawIR/Engine2D facts into the same schema.
5. `assert_chromium_primitive_trace` first calls existing environment-profile
   admission, then semantic comparison and CPU RGBA8 oracle. For GPU tests,
   `assert_chromium_gpu_readback` additionally requires a Simple Vulkan
   fence/device identity/device readback/no fallback receipt.

## Fixture matrix

| Fixture | Required outputs |
|---|---|
| `primitive_rect_border` | DOM/style/layout/paint and exact CPU pixels for fill/background/uniform border |
| `primitive_text_metrics` | text digest, selected font digest, ascent/descent/advance, baseline and pixels |
| `primitive_image` | intrinsic image size/digest, clipped placement, paint order and pixels |
| `primitive_pointer_click` | pointer target, click default action/focus, Ctrl/Alt left/right combinations |
| `primitive_scroll_resize` | scroll offset/target and viewport/relayout box changes |
| `primitive_linear_path` | only if both capabilities advertise `linear-path-v1`; otherwise explicit unsupported outcome |
| `primitive_gpu_receipt` | DrawIR submit/fence/device-readback digest and no CPU fallback, independently of Chrome GPU state |

## Failure rules

- Input JSON accepts no external network/font/image URL; fixtures package every
  resource by digest and reject a mismatch.
- The bridge has one output record for every input event plus stage boundaries;
  duplicate/out-of-order/missing records invalidate `NormalizedTrace`.
- Semantic match with mismatched pixels is failure. Pixel match with missing
  semantic stage or source is failure.
- Device-like screenshots, `source="synthetic"`, cache readback, or no fence
  are not a GPU receipt. `fallback_used=true` fails strict GPU profile.
- Chrome missing on Linux, macOS, QEMU, or UNO Q is an unavailable test
  environment. It does not change Simple runtime selection or test result to
  pass.

## Ownership and error conversion

`ChromiumOracleHandle` is the sole Simple representation of the native session
and has `released` state. A wrapper releases it in the same call path that
consumes output. The caller provides buffers and retains their allocation/free
responsibility; the plugin retains no request pointer after return and returns
no borrowed output pointer. Non-OK native codes become the frozen text classes
from architecture and bounded, redacted detail. The converter rejects unknown
status/layer/primitive rather than preserving opaque native payload.

The unit-test loader seam calls only
`chromium_oracle_validate_library_probe(request, probe)` with a constructed
`ChromiumOracleLibraryProbe`. It validates exact ABI/symbol/hash classes but
never invokes native code or returns a fixture trace. Integration and system
tests use `chromium_oracle_load` and a real explicit plugin path; fake loader,
fixture, response, or synthetic Chrome mode is prohibited.

## Non-overlap

This detail design owns only the test oracle and its converters. It does not
modify `simple_web_html_layout_renderer*`, `DrawIrComposition`, Engine2D,
Vulkan/Venus transport, keyboard parsing, sound, or production Chrome/Electron
wrappers. Those owners expose observations through their existing contracts.
