# Claude Full RemoteCallout

> Pure Simple/TUI-compatible remote control first-run dialog.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full RemoteCallout

Pure Simple/TUI-compatible remote control first-run dialog.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/remote_callout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple/TUI-compatible remote control first-run dialog.

## Scenarios

### Claude full RemoteCallout

#### gates first-run visibility

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gates first-run visibility
- Check config, bridge, and token gates
   - Expected: shouldShowRemoteCalloutRoute(false, true, true) is true
   - Expected: shouldShowRemoteCallout(false, true, true) is true
   - Expected: shouldShowRemoteCalloutRoute(true, true, true) is false
   - Expected: shouldShowRemoteCalloutRoute(false, false, true) is false
   - Expected: shouldShowRemoteCalloutRoute(false, true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gates first-run visibility")
step("Check config, bridge, and token gates")
expect(shouldShowRemoteCalloutRoute(false, true, true)).to_equal(true)
expect(shouldShowRemoteCallout(false, true, true)).to_equal(true)
expect(shouldShowRemoteCalloutRoute(true, true, true)).to_equal(false)
expect(shouldShowRemoteCalloutRoute(false, false, true)).to_equal(false)
expect(shouldShowRemoteCalloutRoute(false, true, false)).to_equal(false)
```

</details>

#### renders the remote control dialog model

- renders the remote control dialog model
- Check title and body
   - Expected: view.title equals `Remote Control`
   - Expected: view.marksSeenOnMount is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders the remote control dialog model")
step("Check title and body")
val view = RemoteCallout()
expect(view.title).to_equal("Remote Control")
expect(view.body[0]).to_contain("claude.ai/code")
expect(view.body[1]).to_contain("/remote-control")
expect(view.marksSeenOnMount).to_equal(true)
```

</details>

#### exposes enable and dismiss options

- exposes enable and dismiss options
- Check select options and callbacks
   - Expected: options.len() equals `2`
   - Expected: options[0].label equals `Enable Remote Control for this session`
   - Expected: options[0].description equals `Opens a secure connection to claude.ai.`
   - Expected: options[0].value equals `enable`
   - Expected: options[1].label equals `Never mind`
   - Expected: options[1].value equals `dismiss`
   - Expected: remoteCalloutCancelSelection() equals `dismiss`
   - Expected: handleCancel() equals `dismiss`
   - Expected: remoteCalloutSelect("enable") equals `enable`
   - Expected: handleSelect("enable") equals `enable`
   - Expected: handleSelect("dismiss") equals `dismiss`
   - Expected: remoteCalloutSelect("bad") equals `dismiss`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes enable and dismiss options")
step("Check select options and callbacks")
val options = remoteCalloutOptions()
expect(options.len()).to_equal(2)
expect(options[0].label).to_equal("Enable Remote Control for this session")
expect(options[0].description).to_equal("Opens a secure connection to claude.ai.")
expect(options[0].value).to_equal("enable")
expect(options[1].label).to_equal("Never mind")
expect(options[1].value).to_equal("dismiss")
expect(remoteCalloutCancelSelection()).to_equal("dismiss")
expect(handleCancel()).to_equal("dismiss")
expect(remoteCalloutSelect("enable")).to_equal("enable")
expect(handleSelect("enable")).to_equal("enable")
expect(handleSelect("dismiss")).to_equal("dismiss")
expect(remoteCalloutSelect("bad")).to_equal("dismiss")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `155b3e65e1b4174d512f996fbb428664d87baedbb96b290ca8e6b4722fda76a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `155b3e65e1b4174d512f996fbb428664d87baedbb96b290ca8e6b4722fda76a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `155b3e65e1b4174d512f996fbb428664d87baedbb96b290ca8e6b4722fda76a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/components/remote_callout_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/remote_callout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/remote_callout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/remote_callout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/remote_callout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/remote_callout_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates first-run visibility' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/remote_callout_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the remote control dialog model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/remote_callout_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes enable and dismiss options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
