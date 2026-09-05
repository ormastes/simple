# Claude Full File Index

> Purpose: should dedupe and index non-empty paths

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full File Index

Purpose: should dedupe and index non-empty paths

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should dedupe and index non-empty paths
Audience: compiler and tooling engineers who maintain this spec

# Claude Full File Index

Checks dedupe, fuzzy search, top-level cache, and scoring behavior.

## Scenarios

### Claude full FileIndex

#### should dedupe and index non-empty paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should dedupe and index non-empty paths
- Verify: should dedupe and index non-empty paths
- Load a file list with duplicates and empties
   - Expected: index.paths equals `["src/App.ts", "test/App.test.ts"]`
   - Expected: index.readyCount equals `2`
   - Expected: index.lowerPaths[0] equals `src/app.ts`
   - Expected: index.pathLens[0] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should dedupe and index non-empty paths")
step("Verify: should dedupe and index non-empty paths")
# @req: REQ-TOOLS-Inde-001
step("Load a file list with duplicates and empties")
val index = FileIndex.new()
index.loadFromFileList(["src/App.ts", "", "src/App.ts", "test/App.test.ts"])
expect(index.paths).to_equal(["src/App.ts", "test/App.test.ts"])
expect(index.readyCount).to_equal(2)  # oracle: value fixed by the spec contract
expect(index.lowerPaths[0]).to_equal("src/app.ts")
expect(index.pathLens[0]).to_equal(10)  # oracle: value fixed by the spec contract
```

</details>

#### should return top-level entries for empty query

- should return top-level entries for empty query
- Verify: should return top-level entries for empty query
- Search with an empty query
   - Expected: results[0].path equals `a`
   - Expected: results[1].path equals `src`
   - Expected: results[2].path equals `docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return top-level entries for empty query")
step("Verify: should return top-level entries for empty query")
# @req: REQ-TOOLS-Inde-001
step("Search with an empty query")
val index = FileIndex.new()
index.loadFromFileList(["src/App.ts", "docs/readme.md", "a/file.txt", "src/main.ts"])
val results = index.search("", 3)
expect(results[0].path).to_equal("a")
expect(results[1].path).to_equal("src")
expect(results[2].path).to_equal("docs")
```

</details>

#### should fuzzy search case-insensitively for lowercase queries

- should fuzzy search case-insensitively for lowercase queries
- Verify: should fuzzy search case-insensitively for lowercase queries
- Search lowercase query against mixed-case paths
   - Expected: results[0].path equals `src/QueryEngine.ts`
   - Expected: results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fuzzy search case-insensitively for lowercase queries")
step("Verify: should fuzzy search case-insensitively for lowercase queries")
# @req: REQ-TOOLS-Inde-001
step("Search lowercase query against mixed-case paths")
val index = FileIndex.new()
index.loadFromFileList(["src/QueryEngine.ts", "src/file_index.ts", "README.md"])
val results = index.search("qe", 2)
expect(results[0].path).to_equal("src/QueryEngine.ts")
expect(results.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should fuzzy search case-sensitively when query has uppercase

- should fuzzy search case-sensitively when query has uppercase
- Verify: should fuzzy search case-sensitively when query has uppercase
- Search uppercase query
   - Expected: results.len() equals `1`
   - Expected: results[0].path equals `src/QueryEngine.ts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fuzzy search case-sensitively when query has uppercase")
step("Verify: should fuzzy search case-sensitively when query has uppercase")
# @req: REQ-TOOLS-Inde-001
step("Search uppercase query")
val index = FileIndex.new()
index.loadFromFileList(["src/queryEngine.ts", "src/QueryEngine.ts"])
val results = index.search("QE", 2)
expect(results.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(results[0].path).to_equal("src/QueryEngine.ts")
```

</details>

#### should apply test path position penalty

- should apply test path position penalty
- Verify: should apply test path position penalty
- Rank non-test result before test result
   - Expected: results[0].path equals `src/App.ts`
   - Expected: results[0].score equals `0`
   - Expected: results[1].score equals `525`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply test path position penalty")
step("Verify: should apply test path position penalty")
# @req: REQ-TOOLS-Inde-001
step("Rank non-test result before test result")
val index = FileIndex.new()
index.loadFromFileList(["src/App.ts", "test/App.test.ts"])
val results = index.search("App", 2)
expect(results[0].path).to_equal("src/App.ts")
expect(results[0].score).to_equal(0)  # oracle: value fixed by the spec contract
expect(results[1].score).to_equal(525)  # oracle: value fixed by the spec contract
```

</details>

#### should expose scoring helpers and constants

- should expose scoring helpers and constants
- Verify: should expose scoring helpers and constants
- Check boundary, camel, bitmap, and top-level helpers
   - Expected: scoreBonusAt("src/App.ts", 4, false) equals `8`
   - Expected: scoreBonusAt("src/fooBar.ts", 7, false) equals `6`
   - Expected: firstPathSegment("native\\file.ts") equals `native`
   - Expected: yieldToEventLoop() equals `yield`
   - Expected: chunkMs() equals `4`
   - Expected: fileIndexSourceLinesModeled() equals `370`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose scoring helpers and constants")
step("Verify: should expose scoring helpers and constants")
# @req: REQ-TOOLS-Inde-001
step("Check boundary, camel, bitmap, and top-level helpers")
expect(scoreBonusAt("src/App.ts", 4, false)).to_equal(8)  # oracle: value fixed by the spec contract
expect(scoreBonusAt("src/fooBar.ts", 7, false)).to_equal(6)  # oracle: value fixed by the spec contract
expect(firstPathSegment("native\\file.ts")).to_equal("native")
expect(yieldToEventLoop()).to_equal("yield")
expect(chunkMs()).to_equal(4)  # oracle: value fixed by the spec contract
expect(fileIndexSourceLinesModeled()).to_equal(370)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Inde-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `945b49866593961600283667f31778b43bf6c2b5141facbf5ef8561ee29c9489`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `945b49866593961600283667f31778b43bf6c2b5141facbf5ef8561ee29c9489`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `945b49866593961600283667f31778b43bf6c2b5141facbf5ef8561ee29c9489`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should dedupe and index non-empty paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should dedupe and index non-empty paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return top-level entries for empty query' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return top-level entries for empty query' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fuzzy search case-insensitively for lowercase queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fuzzy search case-insensitively for lowercase queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fuzzy search case-sensitively when query has uppercase' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply test path position penalty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose scoring helpers and constants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
