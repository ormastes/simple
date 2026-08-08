# Browser renderer attachment boundary

> A top-level attachment response never gains document activation authority.
> Until a download subsystem exists, both the hosted parent and BrowserSession
> reject it while retaining the committed page.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 0 | 0 | 1 |

## Scope and evidence boundary

The executable scenario is
`test/03_system/security/browser_renderer_attachment_boundary_spec.spl`.
It traces REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-010,
REQ-WEB-BROWSER-012, and REQ-WEB-BROWSER-021.

This checked-in manual records the intended executable evidence while target
execution and doc generation are held. No runtime, bootstrap, seed, stale
artifact, download implementation, rendering, latency, RSS, or passing-runner
claim is made.

## Scenario

### should preserve the committed document when navigation is an attachment

1. **Install a safe document and attachment authority**
   - `setup_hosted_attachment_navigation_fixture`
   - Install one committed HTTPS document, history/CSP authority, cookie, and
     unchanged worker/frame witnesses.

2. **Navigate through the hosted parent**
   - `submit_attachment_navigation`
   - Start the target navigation through `HostedBrowserRendererProcess`.
   - Require the parent command to use capability-bound SBR2.

3. **Deliver an attachment document response**
   - `deliver_attachment_document_response`
   - Supply duplicate `Content-Disposition` fields whose later mixed-case,
     OWS-padded value is `Attachment` with a quoted filename parameter.
   - Carry hostile HTML, script, cookie, title, and global mutations in the
     response body.

4. **Preserve the committed document and reject activation**
   - `check_attachment_navigation_not_activated`
   - Require deterministic `document-attachment-unsupported` rejection from
     both the hosted parent and BrowserSession.
   - Preserve URL, history, CSP, DOM/body, title, cookie, frame/resource, and
     outbound-worker state.
   - Prove no attachment body enters the pending SBR2 wire and no hostile
     global is created.

<details>
<summary>Executable SSpec</summary>

The complete four-step scenario and all helper implementations are retained at
`test/03_system/security/browser_renderer_attachment_boundary_spec.spl`.

</details>
