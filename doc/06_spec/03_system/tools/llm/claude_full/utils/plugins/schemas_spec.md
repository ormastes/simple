# Claude Full Plugin Schemas Slice

> Focused Simple coverage for marketplace trust-gate helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Schemas Slice

Focused Simple coverage for marketplace trust-gate helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for marketplace trust-gate helpers from
utils/plugins/schemas.ts.

## Scenarios

### Claude full plugin schemas parity

#### should model marketplace auto update defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model marketplace auto update defaults
- Check auto update defaulting
   - Expected: marketplaceAutoUpdateDefaultRoute("claude-code-marketplace", false, false) is true
   - Expected: marketplaceAutoUpdateDefaultRoute("knowledge-work-plugins", false, false) is false
   - Expected: marketplaceAutoUpdateDefaultRoute("claude-code-marketplace", true, true) is true
   - Expected: marketplaceAutoUpdateDefaultRoute("claude-code-marketplace", true, false) is false
   - Expected: marketplaceAutoUpdateDefaultRoute("custom-market", true, true) is true
   - Expected: marketplaceAutoUpdateDefaultRoute("custom-market", true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model marketplace auto update defaults")
step("Check auto update defaulting")
expect(marketplaceAutoUpdateDefaultRoute("claude-code-marketplace", false, false)).to_equal(true)
expect(marketplaceAutoUpdateDefaultRoute("knowledge-work-plugins", false, false)).to_equal(false)
expect(marketplaceAutoUpdateDefaultRoute("claude-code-marketplace", true, true)).to_equal(true)
expect(marketplaceAutoUpdateDefaultRoute("claude-code-marketplace", true, false)).to_equal(false)
expect(marketplaceAutoUpdateDefaultRoute("custom-market", true, true)).to_equal(true)
expect(marketplaceAutoUpdateDefaultRoute("custom-market", true, false)).to_equal(false)
```

</details>

#### should model reserved names and source validation

- should model reserved names and source validation
- Check reserved trust gates
   - Expected: isBlockedMarketplaceNameRoute("claude-code-marketplace") is false
   - Expected: isBlockedMarketplaceNameRoute("claude-official") is true
   - Expected: isBlockedMarketplaceNameRoute("my-claude-marketplace") is false
   - Expected: hasOnlyAsciiMarketplaceNameRoute("market") is true
   - Expected: validateMarketplaceNameWithAsciiRoute("market", false) equals `invalid marketplace name`
   - Expected: validateReservedMarketplaceSourceRoute("claude-code-marketplace", "github", "evil/repo") equals `reserved marketplace source must be anthropics`
   - Expected: validateReservedMarketplaceSourceRoute("claude-code-marketplace", "github", "anthropics/repo") equals `source valid`
   - Expected: validateReservedMarketplaceSourceRoute("claude-code-marketplace", "git", "https://github.com/anthropics/repo") equals `source valid`
   - Expected: validateReservedMarketplaceSourceRoute("custom-market", "github", "evil/repo") equals `source validation skipped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model reserved names and source validation")
step("Check reserved trust gates")
expect(isBlockedMarketplaceNameRoute("claude-code-marketplace")).to_equal(false)
expect(isBlockedMarketplaceNameRoute("claude-official")).to_equal(true)
expect(isBlockedMarketplaceNameRoute("my-claude-marketplace")).to_equal(false)
expect(hasOnlyAsciiMarketplaceNameRoute("market")).to_equal(true)
expect(validateMarketplaceNameWithAsciiRoute("market", false)).to_equal("invalid marketplace name")
expect(validateReservedMarketplaceSourceRoute("claude-code-marketplace", "github", "evil/repo")).to_equal("reserved marketplace source must be anthropics")
expect(validateReservedMarketplaceSourceRoute("claude-code-marketplace", "github", "anthropics/repo")).to_equal("source valid")
expect(validateReservedMarketplaceSourceRoute("claude-code-marketplace", "git", "https://github.com/anthropics/repo")).to_equal("source valid")
expect(validateReservedMarketplaceSourceRoute("custom-market", "github", "evil/repo")).to_equal("source validation skipped")
```

</details>

#### should model marketplace name validation

- should model marketplace name validation
- Check name validation
   - Expected: validateMarketplaceNameRoute("has space") equals `invalid marketplace name`
   - Expected: validateMarketplaceNameRoute("has/slash") equals `invalid marketplace name`
   - Expected: validateMarketplaceNameRoute("..") equals `invalid marketplace name`
   - Expected: validateMarketplaceNameRoute(".") equals `invalid marketplace name`
   - Expected: validateMarketplaceNameRoute("inline") equals `invalid marketplace name`
   - Expected: validateMarketplaceNameRoute("builtin") equals `invalid marketplace name`
   - Expected: validateMarketplaceNameRoute("kebab-case-market") equals `valid marketplace name`
   - Expected: pluginSchemasSourceLinesModeled() equals `1681`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model marketplace name validation")
step("Check name validation")
expect(validateMarketplaceNameRoute("has space")).to_equal("invalid marketplace name")
expect(validateMarketplaceNameRoute("has/slash")).to_equal("invalid marketplace name")
expect(validateMarketplaceNameRoute("..")).to_equal("invalid marketplace name")
expect(validateMarketplaceNameRoute(".")).to_equal("invalid marketplace name")
expect(validateMarketplaceNameRoute("inline")).to_equal("invalid marketplace name")
expect(validateMarketplaceNameRoute("builtin")).to_equal("invalid marketplace name")
expect(validateMarketplaceNameRoute("kebab-case-market")).to_equal("valid marketplace name")
expect(pluginSchemasSourceLinesModeled()).to_equal(1681)
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

- Canonical SPipe generation for source `45abac1d65f191b0e24d7bbeb5fa606ad7614dd853f23144fc3389c9edff3d97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45abac1d65f191b0e24d7bbeb5fa606ad7614dd853f23144fc3389c9edff3d97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45abac1d65f191b0e24d7bbeb5fa606ad7614dd853f23144fc3389c9edff3d97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model marketplace auto update defaults' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model marketplace auto update defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model reserved names and source validation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model reserved names and source validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model marketplace name validation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/schemas_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model marketplace name validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
