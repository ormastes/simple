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
frame.

## Pointer and Text Algorithm

Pointer coordinates are translated to the top non-minimized window’s content
rect. The registry opens or refreshes a `BrowserSession`, runs the existing
layout tree and deepest-node hit-test, derives the stable DOM event identity,
dispatches pointer/click semantics, and records editable focus. Text updates the
focused input through `set_dom_text_input`. A successful mutation replaces
authoritative window content and marks damage.

## Receipt Validation

Pure validators return `""` for valid evidence or one stable reason slug.
Production acceptance rejects empty/mismatched IDs, missing target/callback,
unchanged revision after mutation, compatibility renderer, fallback, zero
handle, incomplete submission, CPU mirror/cache readback, invalid dimensions or
stride, blank output, checksum zero, and absent/invalid RenderDoc artifacts.

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

## Coverage Collection

The evaluator uses each AST expression ID as the stable decision ID. Existing
interpreter externs forward decision/condition probes to the runtime collector,
and the existing coverage dump appends that decision SDN to line/function SDN.
The test runner remains the sole merger, reporter, and threshold owner.
