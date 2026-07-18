# Claude Full File Index

> Checks dedupe, fuzzy search, top-level cache, and scoring behavior.

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec -> std
index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full File Index

Checks dedupe, fuzzy search, top-level cache, and scoring behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/native-ts/file-index/index_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks dedupe, fuzzy search, top-level cache, and scoring behavior.

## Scenarios

### Claude full FileIndex

#### should dedupe and index non-empty paths

- Load a file list with duplicates and empties
- index loadFromFileList
   - Expected: index.paths equals `["src/App.ts", "test/App.test.ts"]`
   - Expected: index.readyCount equals `2`
   - Expected: index.lowerPaths[0] equals `src/app.ts`
   - Expected: index.pathLens[0] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load a file list with duplicates and empties")
val index = FileIndex.new()
index.loadFromFileList(["src/App.ts", "", "src/App.ts", "test/App.test.ts"])
expect(index.paths).to_equal(["src/App.ts", "test/App.test.ts"])
expect(index.readyCount).to_equal(2)
expect(index.lowerPaths[0]).to_equal("src/app.ts")
expect(index.pathLens[0]).to_equal(10)
```

</details>

#### should return top-level entries for empty query

- Search with an empty query
- index loadFromFileList
   - Expected: results[0].path equals `a`
   - Expected: results[1].path equals `src`
   - Expected: results[2].path equals `docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Search lowercase query against mixed-case paths
- index loadFromFileList
   - Expected: results[0].path equals `src/QueryEngine.ts`
   - Expected: results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Search lowercase query against mixed-case paths")
val index = FileIndex.new()
index.loadFromFileList(["src/QueryEngine.ts", "src/file_index.ts", "README.md"])
val results = index.search("qe", 2)
expect(results[0].path).to_equal("src/QueryEngine.ts")
expect(results.len()).to_equal(1)
```

</details>

#### should fuzzy search case-sensitively when query has uppercase

- Search uppercase query
- index loadFromFileList
   - Expected: results.len() equals `1`
   - Expected: results[0].path equals `src/QueryEngine.ts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Search uppercase query")
val index = FileIndex.new()
index.loadFromFileList(["src/queryEngine.ts", "src/QueryEngine.ts"])
val results = index.search("QE", 2)
expect(results.len()).to_equal(1)
expect(results[0].path).to_equal("src/QueryEngine.ts")
```

</details>

#### should apply test path position penalty

- Rank non-test result before test result
- index loadFromFileList
   - Expected: results[0].path equals `src/App.ts`
   - Expected: results[0].score equals `0`
   - Expected: results[1].score equals `525`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Rank non-test result before test result")
val index = FileIndex.new()
index.loadFromFileList(["src/App.ts", "test/App.test.ts"])
val results = index.search("App", 2)
expect(results[0].path).to_equal("src/App.ts")
expect(results[0].score).to_equal(0)
expect(results[1].score).to_equal(525)
```

</details>

#### should expose scoring helpers and constants

- Check boundary, camel, bitmap, and top-level helpers
   - Expected: scoreBonusAt("src/App.ts", 4, false) equals `8`
   - Expected: scoreBonusAt("src/fooBar.ts", 7, false) equals `6`
   - Expected: firstPathSegment("native\\file.ts") equals `native`
   - Expected: yieldToEventLoop() equals `yield`
   - Expected: chunkMs() equals `4`
   - Expected: fileIndexSourceLinesModeled() equals `370`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check boundary, camel, bitmap, and top-level helpers")
expect(scoreBonusAt("src/App.ts", 4, false)).to_equal(8)
expect(scoreBonusAt("src/fooBar.ts", 7, false)).to_equal(6)
expect(firstPathSegment("native\\file.ts")).to_equal("native")
expect(yieldToEventLoop()).to_equal("yield")
expect(chunkMs()).to_equal(4)
expect(fileIndexSourceLinesModeled()).to_equal(370)
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
