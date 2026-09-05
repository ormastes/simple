# Claude Full cache paths

> Pure Simple coverage for cache path sanitizing and composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full cache paths

Pure Simple coverage for cache path sanitizing and composition.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/cache_paths_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for cache path sanitizing and composition.

## Scenarios

### Claude full cache paths

#### sanitizes non alphanumeric characters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sanitizes non alphanumeric characters
- Check cache path sanitizer
   - Expected: sanitizeCachePath("/tmp/my project:one", "hash") equals `-tmp-my-project-one`
   - Expected: sanitizeCachePath("abcXYZ123", "hash") equals `abcXYZ123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sanitizes non alphanumeric characters")
step("Check cache path sanitizer")
expect(sanitizeCachePath("/tmp/my project:one", "hash")).to_equal("-tmp-my-project-one")
expect(sanitizeCachePath("abcXYZ123", "hash")).to_equal("abcXYZ123")
```

</details>

#### caps long sanitized names with an injected hash suffix

- caps long sanitized names with an injected hash suffix
- Check long name cap
   - Expected: sanitized.len() equals `211`
   - Expected: sanitized.ends_with("-stablehash") is true
   - Expected: maxSanitizedCachePathLength() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caps long sanitized names with an injected hash suffix")
step("Check long name cap")
val longName = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val sanitized = sanitizeCachePath(longName, "stablehash")
expect(sanitized.len()).to_equal(211)
expect(sanitized.ends_with("-stablehash")).to_equal(true)
expect(maxSanitizedCachePathLength()).to_equal(200)
```

</details>

#### builds base errors and messages paths

- builds base errors and messages paths
- Check cache path composition
   - Expected: cacheBaseLogsPath("/cache", "/repo/simple", "h") equals `/cache/-repo-simple`
   - Expected: cacheErrorsPath("/cache", "/repo/simple", "h") equals `/cache/-repo-simple/errors`
   - Expected: cacheMessagesPath("/cache", "/repo/simple", "h") equals `/cache/-repo-simple/messages`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds base errors and messages paths")
step("Check cache path composition")
expect(cacheBaseLogsPath("/cache", "/repo/simple", "h")).to_equal("/cache/-repo-simple")
expect(cacheErrorsPath("/cache", "/repo/simple", "h")).to_equal("/cache/-repo-simple/errors")
expect(cacheMessagesPath("/cache", "/repo/simple", "h")).to_equal("/cache/-repo-simple/messages")
```

</details>

#### builds sanitized MCP log paths

- builds sanitized MCP log paths
- Check MCP log path
   - Expected: cacheMcpLogsPath("/cache", "/repo/simple", "server:name", "ph", "sh") equals `/cache/-repo-simple/mcp-logs-server-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds sanitized MCP log paths")
step("Check MCP log path")
expect(cacheMcpLogsPath("/cache", "/repo/simple", "server:name", "ph", "sh")).to_equal("/cache/-repo-simple/mcp-logs-server-name")
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

- Canonical SPipe generation for source `8ca5759826a52933cd45beaf7241895a6a983ffa7437ddea108022c4935e4f77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ca5759826a52933cd45beaf7241895a6a983ffa7437ddea108022c4935e4f77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ca5759826a52933cd45beaf7241895a6a983ffa7437ddea108022c4935e4f77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/cache_paths_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/cache_paths_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/cache_paths_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/cache_paths_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/cache_paths_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/cache_paths_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sanitizes non alphanumeric characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/cache_paths_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caps long sanitized names with an injected hash suffix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/cache_paths_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds base errors and messages paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
