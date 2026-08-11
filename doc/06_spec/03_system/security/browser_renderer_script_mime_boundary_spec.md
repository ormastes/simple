# Browser renderer script MIME boundary

> Final script responses cross the capability-bound SBR2 worker boundary, but
> gain execution authority only after the selected script mode admits their
> normalized MIME type.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 0 | 0 | 1 |

## Scope and evidence boundary

The executable scenario is
`test/03_system/security/browser_renderer_script_mime_boundary_spec.spl`.
It traces REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-010,
REQ-WEB-BROWSER-012, and REQ-WEB-BROWSER-021.

This checked-in manual records the intended executable evidence while target
execution and doc generation are held. No runtime, bootstrap, seed, stale
artifact, rendering, latency, RSS, or passing-runner claim is made.

## Scenario

### should admit only response MIME types authorized for the script mode

1. **Admit canonical JavaScript MIME**
   - `make_script_mime_boundary_fixture`
   - `encode_script_mime_network_response`
   - Admit mixed-case, parameterized canonical JavaScript MIME for classic and
     module scripts.
   - Preserve legacy classic sniffing when `nosniff` is absent.
   - Observe each admitted external script mutate the document.

2. **Reject nosniff classic-script MIME**
   - Route `text/plain` plus case-insensitive `nosniff` through SBR2.
   - Produce one deterministic warning and advance the loader.
   - Execute none of the hostile response body.

3. **Reject redirected module MIME**
   - Accept the correlated redirect and its broker-selected final URL.
   - Reject the final `text/html` module response before redirect alias or
     module source-cache publication.

4. **Preserve runtime state after MIME rejection**
   - `accept_script_mime_network_response`
   - `expect_script_mime_state_unchanged`
   - Preserve DOM markers, cookies, module cache, and redirect aliases while
     retaining the deterministic warning.

<details>
<summary>Executable SSpec</summary>

The complete four-step scenario and all helper implementations are retained at
`test/03_system/security/browser_renderer_script_mime_boundary_spec.spl`.

</details>
