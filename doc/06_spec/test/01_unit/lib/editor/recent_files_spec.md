# Editor Recent Files Tests

> @cover src/lib/editor/core/recent.spl 80%

<!-- sdn-diagram:id=recent_files_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=recent_files_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

recent_files_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=recent_files_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Recent Files Tests

@cover src/lib/editor/core/recent.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EDITOR-RECENT-001 |
| Category | Editor \| Core |
| Status | Implemented |
| Source | `test/01_unit/lib/editor/recent_files_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/editor/core/recent.spl 80%

## Scenarios

### recent files creation

#### creates empty recent list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recent = recent_files_new("/tmp/test_recent.txt")
expect(recent.entries.len()).to_equal(0)
expect(recent.max_entries).to_equal(50)
```

</details>

### recent files add

#### adds a file path

1. var recent = recent files new
2. recent = recent files add
   - Expected: recent.entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = recent_files_new("/tmp/test_recent.txt")
recent = recent_files_add(recent, "/home/user/a.spl")
expect(recent.entries.len()).to_equal(1)
```

</details>

#### adds multiple file paths in order

1. var recent = recent files new
2. recent = recent files add
3. recent = recent files add
4. recent = recent files add
   - Expected: recent.entries.len() equals `3`
   - Expected: recent.entries[2] equals `/home/user/c.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = recent_files_new("/tmp/test_recent.txt")
recent = recent_files_add(recent, "/home/user/a.spl")
recent = recent_files_add(recent, "/home/user/b.spl")
recent = recent_files_add(recent, "/home/user/c.spl")
expect(recent.entries.len()).to_equal(3)
expect(recent.entries[2]).to_equal("/home/user/c.spl")
```

</details>

#### deduplicates by moving to end

1. var recent = recent files new
2. recent = recent files add
3. recent = recent files add
4. recent = recent files add
   - Expected: recent.entries.len() equals `2`
   - Expected: recent.entries[0] equals `/b.spl`
   - Expected: recent.entries[1] equals `/a.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = recent_files_new("/tmp/test_recent.txt")
recent = recent_files_add(recent, "/a.spl")
recent = recent_files_add(recent, "/b.spl")
recent = recent_files_add(recent, "/a.spl")
expect(recent.entries.len()).to_equal(2)
expect(recent.entries[0]).to_equal("/b.spl")
expect(recent.entries[1]).to_equal("/a.spl")
```

</details>

#### trims oldest when max_entries exceeded

1. var recent = RecentFiles
2. recent = recent files add
3. recent = recent files add
4. recent = recent files add
5. recent = recent files add
   - Expected: recent.entries.len() equals `3`
   - Expected: recent.entries[0] equals `/2.spl`
   - Expected: recent.entries[2] equals `/4.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = RecentFiles(entries: [], max_entries: 3, storage_path: "/tmp/t.txt")
recent = recent_files_add(recent, "/1.spl")
recent = recent_files_add(recent, "/2.spl")
recent = recent_files_add(recent, "/3.spl")
recent = recent_files_add(recent, "/4.spl")
expect(recent.entries.len()).to_equal(3)
expect(recent.entries[0]).to_equal("/2.spl")
expect(recent.entries[2]).to_equal("/4.spl")
```

</details>

#### handles adding same file repeatedly

1. var recent = recent files new
2. recent = recent files add
3. recent = recent files add
4. recent = recent files add
   - Expected: recent.entries.len() equals `1`
   - Expected: recent.entries[0] equals `/same.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = recent_files_new("/tmp/test_recent.txt")
recent = recent_files_add(recent, "/same.spl")
recent = recent_files_add(recent, "/same.spl")
recent = recent_files_add(recent, "/same.spl")
expect(recent.entries.len()).to_equal(1)
expect(recent.entries[0]).to_equal("/same.spl")
```

</details>

### recent files edge cases

#### handles empty path

1. var recent = recent files new
2. recent = recent files add
   - Expected: recent.entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = recent_files_new("/tmp/test_recent.txt")
recent = recent_files_add(recent, "")
expect(recent.entries.len()).to_equal(1)
```

</details>

#### max_entries of 1 keeps only latest

1. var recent = RecentFiles
2. recent = recent files add
3. recent = recent files add
   - Expected: recent.entries.len() equals `1`
   - Expected: recent.entries[0] equals `/new.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var recent = RecentFiles(entries: [], max_entries: 1, storage_path: "/tmp/t.txt")
recent = recent_files_add(recent, "/old.spl")
recent = recent_files_add(recent, "/new.spl")
expect(recent.entries.len()).to_equal(1)
expect(recent.entries[0]).to_equal("/new.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
