# Claude Full FileReadCache

> Checks cache put/read/invalidate/stat behavior.

<!-- sdn-diagram:id=fileReadCache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fileReadCache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fileReadCache_spec -> std
fileReadCache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fileReadCache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks cache put/read/invalidate/stat behavior.

## Scenarios

### Claude full FileReadCache

#### should cache reads by path and mtime

- var cache = FileReadCache new
   - Expected: read.content equals `a\nb`
   - Expected: read.encoding equals `utf8`
   - Expected: cache.getStats().size equals `1`
- cache = cache invalidate
   - Expected: cache.getStats().size equals `0`
   - Expected: fileReadCacheSourceLinesModeled() equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
