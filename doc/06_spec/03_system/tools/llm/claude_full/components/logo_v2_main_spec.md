# Claude Full LogoV2 Main Component

> Modern SSpec coverage for LogoV2 render mode, feeds, notices, and modeled source floor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full LogoV2 Main Component

Modern SSpec coverage for LogoV2 render mode, feeds, notices, and modeled source floor.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for LogoV2 render mode, feeds, notices, and modeled source floor.

## Scenarios

### Claude full LogoV2 main component

#### should render condensed mode when no full-logo triggers are active

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should render condensed mode when no full-logo triggers are active
- Build default condensed input
   - Expected: render.mode equals `condensed`
   - Expected: render.logo equals `CondensedLogo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render condensed mode when no full-logo triggers are active")
step("Build default condensed input")
val input = logoV2DefaultInput()
val render = LogoV2(input)
expect(render.mode).to_equal("condensed")
expect(render.logo).to_equal("CondensedLogo")
expect(render.summary()).to_contain("Claude Code")
```

</details>

#### should render compact mode with sandbox and tmux notices

- should render compact mode with sandbox and tmux notices
- Build compact input
   - Expected: render.mode equals `compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render compact mode with sandbox and tmux notices")
step("Build compact input")
val config = LogoV2Config.new("Ada", "Acme", 2, "1.0.0", "dark", ["Deploy window"])
val display = LogoDisplayData.new("1.2.0", "/repo/simple", "team", "ops")
val flags = LogoV2Flags.new(true, false, true, false, false, false, true, true, false, false, false, false, "work", "C-a", true)
val input = LogoV2Input.new(60, config, display, flags, ["compile"], ["new-ui"], [], "opus", "Claude Opus", "high", "", "/tmp/debug.log", "/tmp/prompts", "/tmp/startup",)
val render = LogoV2(input)
expect(render.mode).to_equal("compact")
expect(render.welcome).to_contain("Ada")
expect(render.summary()).to_contain("sandboxed")
expect(render.summary()).to_contain("ChannelsNotice")
```

</details>

#### should render full feed names and effects

- should render full feed names and effects
- Build horizontal full input
   - Expected: render.mode equals `horizontal`
   - Expected: render.feed_names[0] equals `recent-activity:2`
   - Expected: render.feed_names[1] equals `guest-passes`
   - Expected: render.increment_guest_passes_seen is true
   - Expected: render.increment_overage_credit_seen is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render full feed names and effects")
step("Build horizontal full input")
val config = LogoV2Config.new("Grace", "Research", 3, "1.0.0", "system", ["Announcement"])
val display = LogoDisplayData.new("1.3.0", "/home/work/project", "enterprise", "mentor")
val flags = LogoV2Flags.new(true, false, false, true, true, true, false, false, false, true, false, false, "", "", false)
val input = LogoV2Input.new(140, config, display, flags, ["a", "b"], ["c"], ["setup"], "sonnet", "Claude Sonnet", "medium", "coder", "/tmp/debug.log", "/tmp/prompts", "/tmp/startup",)
val render = LogoV2(input)
expect(render.mode).to_equal("horizontal")
expect(render.feed_names[0]).to_equal("recent-activity:2")
expect(render.feed_names[1]).to_equal("guest-passes")
expect(render.increment_guest_passes_seen).to_equal(true)
expect(render.increment_overage_credit_seen).to_equal(false)
```

</details>

#### should check modeled TypeScript source floor

- should check modeled TypeScript source floor
- Read source line helper
   - Expected: logoV2SourceLinesModeled() equals `542`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check modeled TypeScript source floor")
step("Read source line helper")
expect(logoV2SourceLinesModeled()).to_equal(542)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `d2afb2cf93e846112ee595b8e7d37895e52b45dc9d53bd09ee734d4106f69f5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2afb2cf93e846112ee595b8e7d37895e52b45dc9d53bd09ee734d4106f69f5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2afb2cf93e846112ee595b8e7d37895e52b45dc9d53bd09ee734d4106f69f5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/logo_v2_main_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/logo_v2_main_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/logo_v2_main_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render condensed mode when no full-logo triggers are active' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render condensed mode when no full-logo triggers are active' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render compact mode with sandbox and tmux notices' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render compact mode with sandbox and tmux notices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render full feed names and effects' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render full feed names and effects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/logo_v2_main_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check modeled TypeScript source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
