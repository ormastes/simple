# Claude Full FileStateCache

> Checks normalized keys, clone, merge, and size accounting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FileStateCache

Checks normalized keys, clone, merge, and size accounting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks normalized keys, clone, merge, and size accounting.

## Scenarios

### Claude full FileStateCache

#### should set get delete and clear normalized file states

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should set get delete and clear normalized file states
   - Expected: cache.has("/tmp/a.txt") is true
   - Expected: cache.get("/tmp/a.txt").content equals `abc`
   - Expected: cache.calculatedSize() equals `3`
   - Expected: cacheKeys(cache)[0] equals `/tmp/a.txt`
   - Expected: cache.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should set get delete and clear normalized file states")
var cache = createFileStateCacheWithSizeLimit(2, defaultMaxCacheSizeBytes())
cache = cache.set("/tmp/./a.txt", FileState.new("abc", 1, 0, 0, false))
expect(cache.has("/tmp/a.txt")).to_equal(true)
expect(cache.get("/tmp/a.txt").content).to_equal("abc")
expect(cache.calculatedSize()).to_equal(3)
expect(cacheKeys(cache)[0]).to_equal("/tmp/a.txt")
cache = cache.delete("/tmp/a.txt")
expect(cache.size()).to_equal(0)
```

</details>

#### should clone and merge newer states

- should clone and merge newer states
   - Expected: cloneFileStateCache(merged).get("/tmp/a.txt").content equals `new`
   - Expected: readFileStateCacheSize() equals `100`
   - Expected: fileStateCacheSourceLinesModeled() equals `142`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clone and merge newer states")
var first = FileStateCache.new(10, 1000).set("/tmp/a.txt", FileState.new("old", 1, 0, 0, false))
var second = FileStateCache.new(10, 1000).set("/tmp/a.txt", FileState.new("new", 2, 0, 0, false))
val merged = mergeFileStateCaches(first, second)
expect(cloneFileStateCache(merged).get("/tmp/a.txt").content).to_equal("new")
expect(readFileStateCacheSize()).to_equal(100)
expect(fileStateCacheSourceLinesModeled()).to_equal(142)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `03767d552a0379554de3699c77019da40dfb8765acb6f7bf0f336af5f2d4947f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03767d552a0379554de3699c77019da40dfb8765acb6f7bf0f336af5f2d4947f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03767d552a0379554de3699c77019da40dfb8765acb6f7bf0f336af5f2d4947f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/fileStateCache_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/fileStateCache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/fileStateCache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should set get delete and clear normalized file states' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should set get delete and clear normalized file states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clone and merge newer states' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/fileStateCache_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should clone and merge newer states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
