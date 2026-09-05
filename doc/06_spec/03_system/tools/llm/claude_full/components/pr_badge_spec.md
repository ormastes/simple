# Claude Full PrBadge

> Pure Simple/TUI-compatible PR badge rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PrBadge

Pure Simple/TUI-compatible PR badge rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/pr_badge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple/TUI-compatible PR badge rendering.

## Scenarios

### Claude full PrBadge

#### maps review states to colors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps review states to colors
- Check GitHub review state color parity
   - Expected: prStatusColorRoute("approved") equals `success`
   - Expected: getPrStatusColor("approved") equals `success`
   - Expected: prStatusColorRoute("changes_requested") equals `error`
   - Expected: prStatusColorRoute("pending") equals `warning`
   - Expected: prStatusColorRoute("merged") equals `merged`
   - Expected: prStatusColorRoute("unknown") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps review states to colors")
step("Check GitHub review state color parity")
expect(prStatusColorRoute("approved")).to_equal("success")
expect(getPrStatusColor("approved")).to_equal("success")
expect(prStatusColorRoute("changes_requested")).to_equal("error")
expect(prStatusColorRoute("pending")).to_equal("warning")
expect(prStatusColorRoute("merged")).to_equal("merged")
expect(prStatusColorRoute("unknown")).to_equal("")
```

</details>

#### renders a dim unreviewed badge

- renders a dim unreviewed badge
- Check fallback label and link target
   - Expected: badge.text equals `PR #42`
   - Expected: badge.url equals `https://github.test/pr/42`
   - Expected: badge.fallbackLabel equals `#42`
   - Expected: badge.linkBody equals `#42`
   - Expected: badge.statusColor equals ``
   - Expected: badge.dimPrLabel is true
   - Expected: badge.dimNumber is true
   - Expected: badge.underline is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders a dim unreviewed badge")
step("Check fallback label and link target")
val badge = PrBadge(42, "https://github.test/pr/42", "", false)
expect(badge.text).to_equal("PR #42")
expect(badge.url).to_equal("https://github.test/pr/42")
expect(badge.fallbackLabel).to_equal("#42")
expect(badge.linkBody).to_equal("#42")
expect(badge.statusColor).to_equal("")
expect(badge.dimPrLabel).to_equal(true)
expect(badge.dimNumber).to_equal(true)
expect(badge.underline).to_equal(true)
```

</details>

#### renders a bold approved badge

- renders a bold approved badge
- Check bold disables dimming
   - Expected: badge.text equals `PR #7`
   - Expected: badge.statusColor equals `success`
   - Expected: badge.dimPrLabel is false
   - Expected: badge.dimNumber is false
   - Expected: badge.bold is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders a bold approved badge")
step("Check bold disables dimming")
val badge = renderPrBadgeRoute(7, "https://github.test/pr/7", "approved", true)
expect(badge.text).to_equal("PR #7")
expect(badge.statusColor).to_equal("success")
expect(badge.dimPrLabel).to_equal(false)
expect(badge.dimNumber).to_equal(false)
expect(badge.bold).to_equal(true)
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

- Canonical SPipe generation for source `15863c9bc8a018359a1ecc291e13ac5265626f13c933dcf5fabcf2386f6f80ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `15863c9bc8a018359a1ecc291e13ac5265626f13c933dcf5fabcf2386f6f80ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `15863c9bc8a018359a1ecc291e13ac5265626f13c933dcf5fabcf2386f6f80ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/components/pr_badge_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/pr_badge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/pr_badge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/pr_badge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/pr_badge_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps review states to colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/pr_badge_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a dim unreviewed badge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/pr_badge_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a bold approved badge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
