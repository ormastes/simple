# Chrome DOM-snapshot counterpart — token in, token out, over live CDP

> The counterpart design plans a Chrome adapter over CDP; this spec is that

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome DOM-snapshot counterpart — token in, token out, over live CDP

The counterpart design plans a Chrome adapter over CDP; this spec is that

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The counterpart design plans a Chrome adapter over CDP; this spec is that
adapter's IO compare made live. The pinned headless Chrome for Testing binary
(same discovery order as tools/layout_diff/run_layout_diff.shs) is launched for
real, a data: URL carrying a Simple-chosen token is navigated, and the token is
read back out of the running renderer's DOM through the pure-Simple CDP
WebSocket client. The compare is `canonical_exact`: what went in must come out
byte-identically.

## Scope and Preconditions

Requires a chrome executable on one of the layout_diff discovery paths (or
`LAYOUT_DIFF_CHROME`). When none exists, the provider reports a real
`ProviderStatus.unavailable` naming the gap — never a silent skip, and never a
fabricated DOM. When chrome IS present the live scenarios must execute; they
are not allowed to hide behind the unavailable branch, which is why the
executed branch asserts on the browser's real `--version` answer.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `chrome.dom_snapshot@1` | Versioned artifact schema id, registered in converter_registry |
| `canonical_exact` | A verbatim DOM token has no lossy stage, so the relation is exact |
| `ProviderStatus.unavailable` | Fail-closed verdict when no browser can be reached |

## Evidence and Provenance

Every version string and token asserted below is what the launched binary
actually reported over its own transports at run time. The one literal is the
token itself — the input under test.

## Recovery and Troubleshooting

`unavailable` with `chrome unavailable: no executable found` means no candidate
path held an executable — point `LAYOUT_DIFF_CHROME` at a Chrome for Testing
install. `cdp error` details name the failed DevTools stage.

## Scenarios

### Chrome DOM-snapshot counterpart over CDP

#### rejects the run as unavailable when the chrome path does not exist, never faking a DOM

- rejects the run as unavailable when the chrome path does not exist, never faking a DOM
- Attempt the round trip through a binary path that is not present on this host
- Confirm the run is rejected fail-closed with no DOM or version invented


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("rejects the run as unavailable when the chrome path does not exist, never faking a DOM")
step("Attempt the round trip through a binary path that is not present on this host")
val outcome = chrome_dom_snapshot_compare(BOGUS_CHROME, TOKEN, TIMEOUT_MS)
step("Confirm the run is rejected fail-closed with no DOM or version invented")
assert_equal(outcome.status, ProviderStatus.unavailable)
assert_false(outcome.matched)
assert_equal(outcome.observed_token, "")
assert_equal(outcome.dom_length, 0)
assert_equal(outcome.browser_version, "")
assert_true(outcome.detail.starts_with("chrome unavailable"))
```

</details>

#### rejects an empty chrome path as unavailable, naming the discovery knob

- rejects an empty chrome path as unavailable, naming the discovery knob
- Hand the provider an empty path — the no-binary-discovered case


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("rejects an empty chrome path as unavailable, naming the discovery knob")
step("Hand the provider an empty path — the no-binary-discovered case")
val outcome = chrome_dom_snapshot_compare("", TOKEN, TIMEOUT_MS)
assert_equal(outcome.status, ProviderStatus.unavailable)
assert_true(outcome.detail.contains("LAYOUT_DIFF_CHROME"))
```

</details>

#### records canonical_exact as the comparison relation and carries the token through unmodified

- records canonical_exact as the comparison relation and carries the token through unmodified
- A verbatim DOM token has no lossy stage, so the relation must be exact


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("records canonical_exact as the comparison relation and carries the token through unmodified")
step("A verbatim DOM token has no lossy stage, so the relation must be exact")
val outcome = chrome_dom_snapshot_compare(BOGUS_CHROME, TOKEN, TIMEOUT_MS)
assert_equal(outcome.relation, CounterpartRelation.canonical_exact)
assert_equal(outcome.requested_token, TOKEN)
```

</details>

#### round-trips the token through the pinned headless chrome's live DOM, or reports the exact missing stage

- round-trips the token through the pinned headless chrome's live DOM, or reports the exact missing stage
- Discover the pinned chrome binary using the layout_diff candidate order
- No chrome on this host: the verdict must be fail-closed unavailable, never a fake pass
- Chrome is present: the live path MUST execute — no hiding behind unavailable
- The browser's real --version answer is carried as the device identity
- The token Simple put into the page came back out of Chrome's DOM byte-identically
- The serialized document is a real artifact under chrome.dom_snapshot@1


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("round-trips the token through the pinned headless chrome's live DOM, or reports the exact missing stage")
step("Discover the pinned chrome binary using the layout_diff candidate order")
val chrome = chrome_discover_pinned()
val outcome = chrome_dom_snapshot_compare(chrome, TOKEN, TIMEOUT_MS)
if chrome == "":
    step("No chrome on this host: the verdict must be fail-closed unavailable, never a fake pass")
    assert_equal(outcome.status, ProviderStatus.unavailable)
    assert_false(outcome.matched)
    assert_true(outcome.detail.starts_with("chrome unavailable"))
else:
    step("Chrome is present: the live path MUST execute — no hiding behind unavailable")
    assert_equal(outcome.status, ProviderStatus.executed)
    step("The browser's real --version answer is carried as the device identity")
    assert_true(outcome.browser_version.contains("Chrome"))
    assert_equal(outcome.browser_version, chrome_probe_version(chrome))
    step("The token Simple put into the page came back out of Chrome's DOM byte-identically")
    assert_true(outcome.matched)
    assert_equal(outcome.observed_token, TOKEN)
    step("The serialized document is a real artifact under chrome.dom_snapshot@1")
    assert_true(outcome.dom_length > 0)
    assert_equal(outcome.artifact.schema_id, CHROME_DOM_SCHEMA_ID)
    assert_equal(outcome.artifact.schema_version, CHROME_DOM_SCHEMA_VERSION)
    assert_equal(outcome.artifact.boundary_id, CHROME_DOM_BOUNDARY)
```

</details>

#### goes RED when the requested token is sabotaged, naming the mismatch

- goes RED when the requested token is sabotaged, naming the mismatch
- Compare the readback against a token the page never carried — the sabotage check
- No chrome on this host: the sabotage cannot be evaluated, and the run must still be rejected
- Run one honest round trip, then confirm a different token could not have matched it
- The sabotaged token is what the page carries, so it must round-trip too — proving the compare is live, not memorized
- Restore: the sabotaged value above is a local literal, never written back to TOKEN


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("goes RED when the requested token is sabotaged, naming the mismatch")
step("Compare the readback against a token the page never carried — the sabotage check")
val chrome = chrome_discover_pinned()
if chrome == "":
    step("No chrome on this host: the sabotage cannot be evaluated, and the run must still be rejected")
    val outcome = chrome_dom_snapshot_compare(chrome, TOKEN, TIMEOUT_MS)
    assert_equal(outcome.status, ProviderStatus.unavailable)
    assert_false(outcome.matched)
else:
    step("Run one honest round trip, then confirm a different token could not have matched it")
    val outcome = chrome_dom_snapshot_compare(chrome, TOKEN + "-sabotaged", TIMEOUT_MS)
    step("The sabotaged token is what the page carries, so it must round-trip too — proving the compare is live, not memorized")
    assert_equal(outcome.status, ProviderStatus.executed)
    assert_equal(outcome.observed_token, TOKEN + "-sabotaged")
    assert_not_equal(outcome.observed_token, TOKEN)
step("Restore: the sabotaged value above is a local literal, never written back to TOKEN")
assert_equal(TOKEN, "counterpart-chrome-token-4271")
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


## Related Documentation

- **Design:** `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-CHROME-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2ae110859e21abe22ee97e4ad5f30f8586c72b5dbdc2919d4d4e77198635f51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2ae110859e21abe22ee97e4ad5f30f8586c72b5dbdc2919d4d4e77198635f51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2ae110859e21abe22ee97e4ad5f30f8586c72b5dbdc2919d4d4e77198635f51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/chrome_counterpart_compare_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/chrome_counterpart_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/infra/counterpart/chrome_counterpart_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the run as unavailable when the chrome path does not exist, never faking a DOM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty chrome path as unavailable, naming the discovery knob' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records canonical_exact as the comparison relation and carries the token through unmodified' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
