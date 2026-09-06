# Browser Sandbox Worker Routing: Fail-Closed Capability Probe

> Routing the in-process browser's page rendering through the jailed renderer

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Sandbox Worker Routing: Fail-Closed Capability Probe

Routing the in-process browser's page rendering through the jailed renderer

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Security |
| Status | Active |
| Source | `test/01_unit/app/browser/browser_sandbox_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Routing the in-process browser's page rendering through the jailed renderer
worker needs a worker-capable executable to re-exec. This app's own binary is
not one: the worker arg is dispatched only by
`src/os/hosted/hosted_entry.spl:285`, and importing that into the CLI would
drag `os.hosted.*` into the closure of every `simple` invocation. So the
executable is operator-supplied via `SIMPLE_BROWSER_RENDERER_WORKER` and the
capability is PROBED.

The contract this spec defends is that every probe failure keeps the honest
refusal. There must be no path from "probe failed" to "rendered unjailed",
and no path from "render failed inside the jail" to "re-rendered in this
process".

The render route is now wired: `app.browser.sandbox_render` drives
broker -> jailed worker -> Draw IR -> software raster -> pixels. So the
remaining risk this spec guards is the quiet downgrade — a sandboxed render
that fails and gets silently replaced by an in-process one, which the caller
cannot distinguish from success.

## Scope

Covers `src/app/browser/sandbox_routing.spl` and the routing half of
`src/app/browser/sandbox_status.spl`. The jail itself is proven natively by
`scripts/check/check-browser-renderer-sandbox-seccomp.shs`.
Tracking: doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md

## Scenarios

### browser sandbox worker routing fails closed

#### reports a precise reason instead of a bare false

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a precise reason instead of a bare false
- Read the configured worker executable and the derived reason
- The reason is one of the three declared states, never empty
   - Expected: known is true
- An unset knob reports exactly the unset state
   - Expected: reason equals `BROWSER_SANDBOX_ROUTING_UNSET`
   - Expected: browser_sandbox_routing_probe() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a precise reason instead of a bare false")
"""
An operator who asks for a sandbox and does not get one needs to know
which of two very different things went wrong: they never pointed the
browser at a worker binary, or the browser cannot route pages yet no
matter what they configure. A bare `false` conflates those and sends
them debugging the wrong thing.
"""
step("Read the configured worker executable and the derived reason")
val configured = browser_sandbox_worker_executable()
val reason = browser_sandbox_routing_reason()

step("The reason is one of the three declared states, never empty")
val known = (reason == BROWSER_SANDBOX_ROUTING_UNSET or
             reason == BROWSER_SANDBOX_ROUTING_MISSING or
             reason == BROWSER_SANDBOX_ROUTING_READY)
expect(known).to_equal(true)

step("An unset knob reports exactly the unset state")
if configured.trim().len() == 0:
    expect(reason).to_equal(BROWSER_SANDBOX_ROUTING_UNSET)
    expect(browser_sandbox_routing_probe()).to_equal(false)
```

</details>

#### never claims jailed without a configured worker executable

- never claims jailed without a configured worker executable
- The render route is wired, so code capability is present
   - Expected: browser_sandbox_render_route_wired() is true
- With no worker executable configured, routing stays unavailable
   - Expected: browser_sandbox_worker_routing_available() is false
- And the posture never claims jailed, whatever was requested
   - Expected: browser_sandbox_status().jailed is false
- The reason names the missing configuration, not the code


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never claims jailed without a configured worker executable")
"""
This is the load-bearing guarantee. The render route is now wired, so
the browser CAN hand pages to the jailed worker — but only if an
operator actually supplied a worker-capable binary. If capability and
configuration were conflated, a browser with the code present but no
worker configured would claim a sandbox it never entered.
"""
step("The render route is wired, so code capability is present")
expect(browser_sandbox_render_route_wired()).to_equal(true)

step("With no worker executable configured, routing stays unavailable")
if not browser_sandbox_routing_probe():
    expect(browser_sandbox_worker_routing_available()).to_equal(false)

    step("And the posture never claims jailed, whatever was requested")
    expect(browser_sandbox_status().jailed).to_equal(false)

    step("The reason names the missing configuration, not the code")
    expect(browser_sandbox_unavailable_reason())
        .to_equal(browser_sandbox_routing_reason())
```

</details>

#### refuses rather than falling back when the jail cannot render

- refuses rather than falling back when the jail cannot render
- A sandboxed render against a non-existent worker must fail
- A missing worker binary must never yield pixels
   - Expected: false is true
- The failure is reported, with a reason, and no pixels
   - Expected: reason.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses rather than falling back when the jail cannot render")
"""
The dangerous failure is not a crash, it is a quiet downgrade. If a
sandboxed render fails and the browser silently re-rendered the page
in this process, the caller would receive perfectly good pixels and
have no way to know page script had just run unconfined. So the
sandboxed path reports failure instead of substituting an in-process
render.
"""
step("A sandboxed render against a non-existent worker must fail")
match browser_sandbox_render_pixels(
    "/nonexistent/worker-binary", "<html><body>x</body></html>", 8, 8
):
    Ok(_):
        step("A missing worker binary must never yield pixels")
        expect(false).to_equal(true)
    Err(reason):
        step("The failure is reported, with a reason, and no pixels")
        expect(reason.len() > 0).to_equal(true)
```

</details>

#### requires both halves before routing is available

- requires both halves before routing is available
- Compute both halves independently
- Availability equals their conjunction, with no third path
   - Expected: browser_sandbox_worker_routing_available() equals `probe and wired`
- A false half is sufficient to make routing unavailable
   - Expected: browser_sandbox_worker_routing_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires both halves before routing is available")
"""
Availability is the conjunction of an operator-supplied worker binary
and a wired render route. Either half missing must keep the refusal,
so a future edit that satisfies only one half cannot quietly enable a
half-built jail.
"""
step("Compute both halves independently")
val probe = browser_sandbox_routing_probe()
val wired = browser_sandbox_render_route_wired()

step("Availability equals their conjunction, with no third path")
expect(browser_sandbox_worker_routing_available()).to_equal(probe and wired)

step("A false half is sufficient to make routing unavailable")
if not probe or not wired:
    expect(browser_sandbox_worker_routing_available()).to_equal(false)
```

</details>

#### names the env knob so the capability is discoverable

- names the env knob so the capability is discoverable
- The exported env name is the documented one
   - Expected: BROWSER_SANDBOX_WORKER_ENV equals `SIMPLE_BROWSER_RENDERER_WORKER`
- Reading it through the facade agrees with the module accessor
   - Expected: browser_sandbox_worker_executable() equals `env_get(BROWSER_SANDBOX_WORKER_ENV)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("names the env knob so the capability is discoverable")
"""
A security knob nobody can find is a knob nobody uses. The environment
variable name is exported rather than spelled inline at call sites, so
docs, tests and the app cannot drift apart.
"""
step("The exported env name is the documented one")
expect(BROWSER_SANDBOX_WORKER_ENV).to_equal("SIMPLE_BROWSER_RENDERER_WORKER")

step("Reading it through the facade agrees with the module accessor")
expect(browser_sandbox_worker_executable()).to_equal(env_get(BROWSER_SANDBOX_WORKER_ENV))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-014`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4250ac1318cdbc33fe25b01bfb7964f65ceba8fe67748104878b3652715a94d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4250ac1318cdbc33fe25b01bfb7964f65ceba8fe67748104878b3652715a94d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4250ac1318cdbc33fe25b01bfb7964f65ceba8fe67748104878b3652715a94d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/browser/browser_sandbox_routing_spec.spl
mirror: doc/06_spec/01_unit/app/browser/browser_sandbox_routing_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/browser/browser_sandbox_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/browser/browser_sandbox_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/browser/browser_sandbox_routing_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/browser/browser_sandbox_routing_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a precise reason instead of a bare false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/browser/browser_sandbox_routing_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never claims jailed without a configured worker executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/browser/browser_sandbox_routing_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses rather than falling back when the jail cannot render' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
