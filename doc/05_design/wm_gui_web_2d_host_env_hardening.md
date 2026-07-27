<!-- codex-design -->
# WM/GUI/Web/2D Host Environment Hardening Detail Design

## Data

| Type | Key fields |
|---|---|
| `HostCapabilityRow` | `name`, `status`, `reason`, `evidence_path`, `resume_command` |
| `TestHostEnv` | schema `simple-test-host-env-v1`, ordered capability rows |
| `HostedWebContentTarget` | window ID, local content coordinates, dimensions, authoritative HTML |
| `HostedWebContentSession` | window ID, source revision, dimensions, `BrowserSession`, focused DOM target |
| extended `HostWmInputReceipt` | event ID, host kind, WM target, semantic target, callback, mutation status |
| SimpleOS pending pointer step | screen point, content window, content-local point, captured window |
| `COMP_INPUT_EVENT` | stable event code, window, key, local point, modifier bits |

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.design hash=sha256:auto render=ascii
@layout dag
@direction TB

HostEvent -> ResolveContentTarget
ResolveContentTarget -> EnsureBrowserSession
EnsureBrowserSession -> LayoutHitTest
LayoutHitTest -> DispatchDomEvent
DispatchDomEvent -> UpdateWindowContent
UpdateWindowContent -> RenderCanonicalFrame
RenderCanonicalFrame -> ValidateCorrelatedReceipt
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.design hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Interfaces

```simple
fn test_host_env() -> TestHostEnv
fn validate_test_host_env(env: TestHostEnv) -> text
fn validate_render_pipeline_receipt(receipt: RenderPipelineReceipt) -> text

fn host_compositor_content_target(comp: HostCompositor, x: i32, y: i32) -> HostedWebContentTarget?
fn host_compositor_update_window_content(comp: HostCompositor, window_id: i64, body_html: text) -> HostCompositor

class HostedWebContentSessionRegistry:
    fn dispatch_pointer(target: HostedWebContentTarget, event_id: text, kind: text) -> HostedWebDispatchResult
    fn dispatch_text(window_id: i64, event_id: text, value: text) -> HostedWebDispatchResult
```

`HostedWebDispatchResult` returns target/callback/mutation/body HTML but never
pixels. The compositor remains the only owner that turns mutated content into a
frame. `callback_count` is the number of executed DOM listener/author actions;
default focus, text edits, checkbox toggles, and other browser mutations advance
`mutation_revision` without manufacturing a callback. BrowserSession's shared
DOM dispatch counter includes nested focus, blur, input, change, and submit
dispatches; each hosted receipt reports the operation-local counter delta.

## Pointer and Text Algorithm

Pointer coordinates are translated to the top non-minimized window’s content
rect. The registry opens or refreshes a `BrowserSession`, runs the existing
layout tree and deepest-node hit-test, derives the stable DOM event identity,
dispatches pointer/click semantics, and records editable focus. Text updates the
focused input through `set_dom_text_input`. Dispatch-result actions supply the
callback count. A successful mutation replaces authoritative window content and
marks damage.

## Receipt Validation

Pure validators return `""` for valid evidence or one stable reason slug.
Production acceptance rejects empty/mismatched IDs, missing target/callback,
non-increasing revision after mutation, compatibility renderer, fallback, zero
handle, incomplete submission, CPU mirror/cache readback, invalid dimensions or
stride, blank output, checksum zero, and absent/invalid RenderDoc artifacts.
Display/input admission also requires exact `pass` values for the retained
focus, pointer, keyboard, move, maximize, and restore status rows. Missing,
malformed, or non-pass values fail closed before framebuffer admission.
The live wrapper resolves the input receipt's WM target against the same
snapshot's compositor window list, requires exactly one match, and retains the
matched ID separately. The pure aggregate requires both retained IDs to be
positive and equal.
The host aggregate also re-hashes the retained RenderDoc capture path and
replay XML path, failing when either current artifact no longer matches its
exact-one gate binding or is a symlink/non-regular path.
Framebuffer admission requires both correlated backend values to be `vulkan`;
matching CPU fallback values in retained evidence fail validation.
The input frame must also retain `composition_id=wm-composite` and a positive
count of executed `wm.content` image commands from the same executor snapshot.
That snapshot must report completed `1024x720` ARGB8888 readback with stride
`4096`; the host gate rejects missing or inconsistent receipt geometry.
The strict Vulkan probe requires 256 pixels and the canonical clear/rectangle
checksums; empty, short, overlong, or correlated forged checksums fail closed.
Its Windows scalar receipt is admissible because the producer compares every
pixel and verifies post-present cache equality; retained pixel files remain
mandatory only for browser, correlated framebuffer, and RenderDoc rows.
The host aggregate resolves duplicate-safe baseline/input capture bindings and
requires regular no-follow paths before re-hashing both current PPMs and
admitting `framebuffer_readback`.

Capability-row classification is uniform: valid and present evidence is `pass`; an existing
required evidence file set that is malformed, stale, or otherwise invalid is
`fail`; and an absent required evidence file set is `blocked` with its resume
command. The Vulkan set is present only when the readback, direct-run, and
browser-backing env files all exist. RenderDoc, SIMD, and framebuffer artifacts
referenced by an existing env file are validation inputs, so missing, changed,
or substituted referenced artifacts make that retained row `fail`, not
`blocked`.

For the SimpleOS remote-client row, validation also rejects owner port `0`,
resident placeholder apps, missing focus/input IPC sends, missing
`WindowClient` receipt, unchanged application content, non-increasing frame
generation, or unchanged pre/post content-click framebuffer hashes.

## Failure Handling

An event outside client content remains a valid WM-only event. A content event
with missing session, layout target, or dispatch fails closed in live evidence
mode and retains its reason. Normal hosted operation keeps WM chrome behavior
but does not fabricate semantic success.

## Observability

Use one correlation ID in `dbg_event_hop` for host, WM, DOM, mutation, submit,
and readback. Time session refresh, hit-test/dispatch, composition, and backend
readback independently; no diagnostic work runs unless its existing facet is
enabled.

## Retained Performance Boundary

The 4K/8K showcase probe draws one canonical frame, warms the backend, and then
measures 200 retained static `Engine2D.present()` calls. Its
`retained-static-frame`/`redraw_frames=1` result is present-path evidence only;
it is not WM damage, dirty-region redraw, or full-frame repaint throughput.
The content revision binds this measurement to the direct Engine2D owners
`engine.spl` and `backend_software.spl` as well as the probe sources, so changes
to the measured present path invalidate retained rows before aggregation.

## Coverage Collection

The evaluator uses each AST expression ID as the stable decision ID. Existing
interpreter externs forward decision/condition probes to the runtime collector,
and the existing coverage dump appends that decision SDN to line/function SDN.
The test runner remains the sole merger, reporter, and threshold owner.

## Browser Vulkan And Pixel-Parity Admission

The existing `vulkan` capability row has two independent evidence inputs. The
Simple readback receipt proves direct Vulkan device pixels. The setup receipts
prove Electron and Chrome Vulkan backing plus three-way Electron/Chrome/Simple
ARGB parity. `host_browser_vulkan_parity_evidence_passes` accepts the browser
backing and direct-run envs separately because the setup producer intentionally
writes them in different modes and both contain common viewport metadata.

Every admitted scalar is duplicate-safe. Browser source proofs must be regular,
nonempty producer artifacts; direct-run ARGB paths must be nonempty and their
width/height must equal the requested viewport, format must be `argb-u32`, and
pixel count must equal width times height with `0 < nonblank <= pixel_count`.
The producer and comparator reject coerced dimensions and any pixel outside the
integer u32 range before comparison. All three diff paths must be bound, all
three pairwise statuses must be `pass`, all mismatch counts must be `0`, and the
aggregate must be `pass` in `pairwise-argb-diff` mode. The existing row passes
only when this classifier and `host_vulkan_evidence_passes` both pass.

Current-file hash revalidation is outside this bounded classifier because the
setup producer does not emit ARGB/diff SHA-256 bindings. That provenance
follow-up remains explicit in the external-host TODO; nonempty artifact paths
alone must not be described as cryptographic freshness proof.
