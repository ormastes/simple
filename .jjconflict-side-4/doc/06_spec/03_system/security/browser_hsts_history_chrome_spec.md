# HSTS-safe hosted history chrome

Status: **DRAFT / EVIDENCE-BLOCKED**

Executable source:
`test/03_system/security/browser_hsts_history_chrome_spec.spl`.
No runtime result is claimed until an admitted current pure-Simple runner
executes the scenario.

## Scope

Back and Forward must bind the HSTS-upgraded traversal ledger to the SBR2
command capability. The parent keeps the committed ledger unchanged while the
command is pending and publishes the off-side ledger only after accepting the
final capability-bound renderer proposal.

The exercised host route is
`HostedBrowserRendererRegistry.dispatch_chrome_pointer` press/release into
`HostedBrowserRendererProcess.begin_go_back`, `begin_go_forward`,
`begin_stop`, and `begin_go_home`. No synthetic BrowserSession-only shortcut is
used.

## Scenario: bind upgraded traversal history to hosted chrome

### 1. Commit HTTP history before learning HSTS

`setup_hsts_history_chrome_fixture` creates window `901` with an active parent
renderer, canonical CSP state, and committed ledger:

```text
index 0: http://secure.test/legacy
index 1: https://current.test/page  (current)
```

It commits `Strict-Transport-Security: max-age=600` from authenticated
`https://secure.test/policy`, synchronizes Back/Forward projections, installs
the renderer in a ready `HostedBrowserRendererRegistry` entry, and retains the
real software Engine2D raster owner used by that registry entry.

### 2. Learn HSTS and activate Back through hosted chrome

`activate_back_through_hosted_chrome` sends Back down/up through
`dispatch_chrome_pointer`.

Exact receipt and protocol oracles:

- down: reason `chrome-pressed`, callback count `0`;
- up: empty reason, callback count `1`;
- the pending wire decodes as an SBR2 capability message;
- action is `back`;
- command URL is `https://secure.test/legacy`;
- nested history snapshot action is `N`, current index is `1`, and URLs are
  exactly `[https://secure.test/legacy, https://current.test/page]`;
- snapshot capability equals the renderer's active command capability;
- permit and pending traversal target are the same upgraded HTTPS URL;
- pending traversal index is `0`;
- committed history is still the original HTTP ledger at index `1`.

### 3. Commit one upgraded traversal ledger atomically

`check_upgraded_history_commit` stages the final HTTPS document URL/CSP and an
admitted history authority using the exact active command capability. It
submits a traversal proposal with index `0` and the exact upgraded two-entry
ledger.

Exact validator and publication oracles:

- candidate is accepted;
- candidate document URL is `https://secure.test/legacy`;
- candidate URLs are exactly the upgraded ledger;
- one `_commit_history_candidate` publishes it;
- document/current URL becomes the upgraded HTTPS URL;
- Back is empty and Forward is `https://current.test/page`;
- committed index becomes `0`;
- pending traversal index/URL are cleared.

`_assert_committed_history` is the shared exact ledger/index checker.

### 4. Preserve Stop retry and Forward projections

`check_stop_retry_forward_projection` activates Forward through registry
press/release. The pending target/index become
`https://current.test/page`/`1`, while the committed upgraded ledger remains at
index `0`. `_assert_forward_pending_wire` decodes the actual pending SBR2 wire
and requires action `forward`, HTTPS URL `https://current.test/page`, nested
snapshot action `N`, current index `0`, and exact URLs
`[https://secure.test/legacy, https://current.test/page]`. The outer issued
command capability, nested snapshot authority capability, and renderer active
command capability must all be equal.

Stop then clears the pending traversal but preserves that committed ledger and
its truthful Forward projection. A second Forward press/release stages the
same exact target/index without changing committed history; the same full wire
and capability oracle runs again, proving the stopped traversal is retryable.
A final Stop clears that retry.

Two independent controls run in the same visible step:

- `_check_replacement_preserves_commit` stages upgraded Back, then activates
  Home through registry press/release. The Home permit becomes
  `https://home.test/`, traversal pending state clears, and the original
  committed HTTP ledger/index remain unchanged.
- `_check_rejected_candidate_preserves_commit` stages upgraded Back, then
  presents a capability-bound traversal proposal containing the stale HTTP
  slot. The candidate is rejected with exact reason
  `history-ledger-mismatch`, and the original committed ledger/index remain
  unchanged.

Every registry raster is shut down after its final oracle.

## Helper parity

The executable helper vocabulary is frozen:

- `setup_hsts_history_chrome_fixture`
- `activate_back_through_hosted_chrome`
- `check_upgraded_history_commit`
- `check_stop_retry_forward_projection`
- `_assert_committed_history`
- `_shutdown_history_registry`
- `_assert_forward_pending_wire`
- `_check_replacement_preserves_commit`
- `_check_rejected_candidate_preserves_commit`

The four visible steps are exactly:

1. `Commit HTTP history before learning HSTS`
2. `Learn HSTS and activate Back through hosted chrome`
3. `Commit one upgraded traversal ledger atomically`
4. `Preserve Stop retry and Forward projections`
