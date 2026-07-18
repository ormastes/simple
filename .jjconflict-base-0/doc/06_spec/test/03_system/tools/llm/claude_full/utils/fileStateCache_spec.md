# Claude Full FileStateCache

> Checks normalized keys, clone, merge, and size accounting.

<!-- sdn-diagram:id=fileStateCache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fileStateCache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fileStateCache_spec -> std
fileStateCache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fileStateCache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks normalized keys, clone, merge, and size accounting.

## Scenarios

### Claude full FileStateCache

#### should set get delete and clear normalized file states

- var cache = createFileStateCacheWithSizeLimit
- cache = cache set
   - Expected: cache.has("/tmp/a.txt") is true
   - Expected: cache.get("/tmp/a.txt").content equals `abc`
   - Expected: cache.calculatedSize() equals `3`
   - Expected: cacheKeys(cache)[0] equals `/tmp/a.txt`
- cache = cache delete
   - Expected: cache.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var first = FileStateCache new
- var second = FileStateCache new
   - Expected: cloneFileStateCache(merged).get("/tmp/a.txt").content equals `new`
   - Expected: readFileStateCacheSize() equals `100`
   - Expected: fileStateCacheSourceLinesModeled() equals `142`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
