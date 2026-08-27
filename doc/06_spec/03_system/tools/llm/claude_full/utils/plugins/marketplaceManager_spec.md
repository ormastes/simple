# Claude Full Marketplace Manager Slice

> Focused coverage for marketplace config, cache, declaration, and plugin lookup

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Marketplace Manager Slice

Focused coverage for marketplace config, cache, declaration, and plugin lookup

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for marketplace config, cache, declaration, and plugin lookup
routes from utils/plugins/marketplaceManager.ts.

## Scenarios

### Claude full marketplace manager parity

#### should model marketplace paths and config loading

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model marketplace paths and config loading
- Check config routes
   - Expected: getMarketplacesCacheDirRoute("/root") equals `/root/plugins/marketplaces`
   - Expected: getKnownMarketplacesFileRoute("/root") equals `/root/plugins/known_marketplaces.json`
   - Expected: loadKnownMarketplacesConfigSafeRoute("missing") equals `empty config`
   - Expected: loadKnownMarketplacesConfigSafeRoute("malformed") equals `empty config`
   - Expected: loadKnownMarketplacesConfigRoute("valid") equals `known marketplaces config`
   - Expected: loadKnownMarketplacesConfigRoute("invalid_shape") equals `schema error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model marketplace paths and config loading")
step("Check config routes")
expect(getMarketplacesCacheDirRoute("/root")).to_equal("/root/plugins/marketplaces")
expect(getKnownMarketplacesFileRoute("/root")).to_equal("/root/plugins/known_marketplaces.json")
expect(loadKnownMarketplacesConfigSafeRoute("missing")).to_equal("empty config")
expect(loadKnownMarketplacesConfigSafeRoute("malformed")).to_equal("empty config")
expect(loadKnownMarketplacesConfigRoute("valid")).to_equal("known marketplaces config")
expect(loadKnownMarketplacesConfigRoute("invalid_shape")).to_equal("schema error")
```

</details>

#### should model declaration source and settings routes

- should model declaration source and settings routes
- Check declaration routes
   - Expected: clearMarketplacesCacheRoute(true) equals `marketplace cache reset`
   - Expected: clearMarketplacesCacheRoute(false) equals `marketplace cache already clear`
   - Expected: getDeclaredMarketplacesRoute(true, true) equals `declared official and configured`
   - Expected: getDeclaredMarketplacesRoute(true, false) equals `declared official marketplace`
   - Expected: getMarketplaceDeclaringSourceRoute(true, true, true) equals `local`
   - Expected: getMarketplaceDeclaringSourceRoute(false, true, true) equals `project`
   - Expected: getMarketplaceDeclaringSourceRoute(false, false, true) equals `user`
   - Expected: saveMarketplaceToSettingsRoute("project", true) equals `save marketplace to project preserving entries`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model declaration source and settings routes")
step("Check declaration routes")
expect(clearMarketplacesCacheRoute(true)).to_equal("marketplace cache reset")
expect(clearMarketplacesCacheRoute(false)).to_equal("marketplace cache already clear")
expect(getDeclaredMarketplacesRoute(true, true)).to_equal("declared official and configured")
expect(getDeclaredMarketplacesRoute(true, false)).to_equal("declared official marketplace")
expect(getMarketplaceDeclaringSourceRoute(true, true, true)).to_equal("local")
expect(getMarketplaceDeclaringSourceRoute(false, true, true)).to_equal("project")
expect(getMarketplaceDeclaringSourceRoute(false, false, true)).to_equal("user")
expect(saveMarketplaceToSettingsRoute("project", true)).to_equal("save marketplace to project preserving entries")
```

</details>

#### should model cache only and plugin lookup routes

- should model cache only and plugin lookup routes
- Check cache lookup routes
   - Expected: getMarketplaceCacheOnlyRoute("absent") equals `marketplace cache null`
   - Expected: getMarketplaceCacheOnlyRoute("valid") equals `marketplace cache object`
   - Expected: getPluginByIdRoute(true, true) equals `plugin from marketplace cache`
   - Expected: getPluginByIdRoute(false, false) equals `plugin null`
   - Expected: marketplaceManagerSourceLinesModeled() equals `2643`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model cache only and plugin lookup routes")
step("Check cache lookup routes")
expect(getMarketplaceCacheOnlyRoute("absent")).to_equal("marketplace cache null")
expect(getMarketplaceCacheOnlyRoute("valid")).to_equal("marketplace cache object")
expect(getPluginByIdRoute(true, true)).to_equal("plugin from marketplace cache")
expect(getPluginByIdRoute(false, false)).to_equal("plugin null")
expect(marketplaceManagerSourceLinesModeled()).to_equal(2643)
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

- Canonical SPipe generation for source `c5c60de4039ae6123770ad542df865ca7bf18147307344fa7866b4d265dc2cf5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5c60de4039ae6123770ad542df865ca7bf18147307344fa7866b4d265dc2cf5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5c60de4039ae6123770ad542df865ca7bf18147307344fa7866b4d265dc2cf5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model marketplace paths and config loading' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model marketplace paths and config loading' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model declaration source and settings routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model declaration source and settings routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model cache only and plugin lookup routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/marketplaceManager_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model cache only and plugin lookup routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
