# Claude Full Plugin Loader Slice

> Focused coverage for plugin cache paths, seed/version lookup, copy/install,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Loader Slice

Focused coverage for plugin cache paths, seed/version lookup, copy/install,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for plugin cache paths, seed/version lookup, copy/install,
and git URL route decisions from utils/plugins/pluginLoader.ts.

## Scenarios

### Claude full plugin loader parity

#### should model plugin cache and versioned path routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model plugin cache and versioned path routes
- Check cache path construction
   - Expected: getPluginCachePathRoute("/home/user/.claude") equals `/home/user/.claude/plugins/cache`
   - Expected: getVersionedCachePathInRoute("/cache", "my plugin", "my-market", "v1.2.3") equals `/cache/my-market/my-plugin/v1.2.3`
   - Expected: getVersionedCachePathRoute("/root", "demo", "acme", "v1.0") equals `/root/plugins/cache/acme/demo/v1.0`
   - Expected: getVersionedZipCachePathRoute("/root", "demo", "acme", "v1.0") equals `/root/plugins/cache/acme/demo/v1.0.zip`
   - Expected: getLegacyCachePathRoute("/root", "my plugin") equals `/root/plugins/cache/my-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model plugin cache and versioned path routes")
step("Check cache path construction")
expect(getPluginCachePathRoute("/home/user/.claude")).to_equal("/home/user/.claude/plugins/cache")
expect(getVersionedCachePathInRoute("/cache", "my plugin", "my-market", "v1.2.3")).to_equal("/cache/my-market/my-plugin/v1.2.3")
expect(getVersionedCachePathRoute("/root", "demo", "acme", "v1.0")).to_equal("/root/plugins/cache/acme/demo/v1.0")
expect(getVersionedZipCachePathRoute("/root", "demo", "acme", "v1.0")).to_equal("/root/plugins/cache/acme/demo/v1.0.zip")
expect(getLegacyCachePathRoute("/root", "my plugin")).to_equal("/root/plugins/cache/my-plugin")
```

</details>

#### should model seed and cache resolution routes

- should model seed and cache resolution routes
- Check seed and cache resolution
   - Expected: probeSeedCacheAnyVersionRoute(1, 1) equals `seed cache version path`
   - Expected: probeSeedCacheAnyVersionRoute(0, 0) equals `no seed cache`
   - Expected: probeSeedCacheAnyVersionRoute(2, 1) equals `ambiguous seed cache`
   - Expected: resolvePluginPathRoute(true, true, true) equals `versioned cache path`
   - Expected: resolvePluginPathRoute(false, true, true) equals `legacy cache path`
   - Expected: resolvePluginPathRoute(false, false, true) equals `computed versioned cache path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model seed and cache resolution routes")
step("Check seed and cache resolution")
expect(probeSeedCacheAnyVersionRoute(1, 1)).to_equal("seed cache version path")
expect(probeSeedCacheAnyVersionRoute(0, 0)).to_equal("no seed cache")
expect(probeSeedCacheAnyVersionRoute(2, 1)).to_equal("ambiguous seed cache")
expect(resolvePluginPathRoute(true, true, true)).to_equal("versioned cache path")
expect(resolvePluginPathRoute(false, true, true)).to_equal("legacy cache path")
expect(resolvePluginPathRoute(false, false, true)).to_equal("computed versioned cache path")
```

</details>

#### should model copy install and url validation routes

- should model copy install and url validation routes
- Check install primitives
   - Expected: copyDirRoute(true, true) equals `copy nested tree`
   - Expected: copyPluginToVersionedCacheRoute(true, false, false) equals `return existing cached path`
   - Expected: copyPluginToVersionedCacheRoute(false, true, false) equals `return seed cache path`
   - Expected: copyPluginToVersionedCacheRoute(false, false, true) equals `empty plugin cache error`
   - Expected: validateGitUrlRoute("https://example.com/repo.git") equals `git url accepted`
   - Expected: validateGitUrlRoute("git@example.com:repo.git") equals `git url accepted`
   - Expected: validateGitUrlRoute("ftp://example.com/repo.git") equals `git url rejected`
   - Expected: installFromNpmRoute(true, true) equals `npm install cached plugin`
   - Expected: installFromNpmRoute(false, true) equals `npm package missing`
   - Expected: pluginLoaderSourceLinesModeled() equals `3302`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model copy install and url validation routes")
step("Check install primitives")
expect(copyDirRoute(true, true)).to_equal("copy nested tree")
expect(copyPluginToVersionedCacheRoute(true, false, false)).to_equal("return existing cached path")
expect(copyPluginToVersionedCacheRoute(false, true, false)).to_equal("return seed cache path")
expect(copyPluginToVersionedCacheRoute(false, false, true)).to_equal("empty plugin cache error")
expect(validateGitUrlRoute("https://example.com/repo.git")).to_equal("git url accepted")
expect(validateGitUrlRoute("git@example.com:repo.git")).to_equal("git url accepted")
expect(validateGitUrlRoute("ftp://example.com/repo.git")).to_equal("git url rejected")
expect(installFromNpmRoute(true, true)).to_equal("npm install cached plugin")
expect(installFromNpmRoute(false, true)).to_equal("npm package missing")
expect(pluginLoaderSourceLinesModeled()).to_equal(3302)
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

- Canonical SPipe generation for source `6b04883814d40650c62447c035e544fe92476ce3af99f6ff57170b4ec4550c32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b04883814d40650c62447c035e544fe92476ce3af99f6ff57170b4ec4550c32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b04883814d40650c62447c035e544fe92476ce3af99f6ff57170b4ec4550c32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model plugin cache and versioned path routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model plugin cache and versioned path routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model seed and cache resolution routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model seed and cache resolution routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model copy install and url validation routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/plugins/pluginLoader_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model copy install and url validation routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
