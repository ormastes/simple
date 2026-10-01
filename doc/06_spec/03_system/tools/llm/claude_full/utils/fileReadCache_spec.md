# Claude Full FileReadCache

> Checks cache put/read/invalidate/stat behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FileReadCache

Checks cache put/read/invalidate/stat behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/fileReadCache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks cache put/read/invalidate/stat behavior.

## Scenarios

### Claude full FileReadCache

#### should cache reads by path and mtime

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should cache reads by path and mtime
   - Expected: read.content equals `a\nb`
   - Expected: read.encoding equals `utf8`
   - Expected: cache.getStats().size equals `1`
   - Expected: cache.getStats().size equals `0`
   - Expected: fileReadCacheSourceLinesModeled() equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cache reads by path and mtime")
var cache = FileReadCache.new().put("/tmp/a.txt", "a\r\nb", "utf8", 1)
val read = cache.readFile("/tmp/a.txt", "ignored", "utf8", 1)
expect(read.content).to_equal("a\nb")
expect(read.encoding).to_equal("utf8")
expect(cache.getStats().size).to_equal(1)
cache = cache.invalidate("/tmp/a.txt")
expect(cache.getStats().size).to_equal(0)
expect(fileReadCacheSourceLinesModeled()).to_equal(96)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `b962b04f468ebe3b16102597cd775e07738e5a61be785075fe52a7221e11448d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b962b04f468ebe3b16102597cd775e07738e5a61be785075fe52a7221e11448d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b962b04f468ebe3b16102597cd775e07738e5a61be785075fe52a7221e11448d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/fileReadCache_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/fileReadCache_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/fileReadCache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/fileReadCache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/fileReadCache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/fileReadCache_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cache reads by path and mtime' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/fileReadCache_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should cache reads by path and mtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
