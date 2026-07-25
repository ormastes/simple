# File Manager Unit Tests

> Tests for FileManager: construction, sorting, navigation, and

<!-- sdn-diagram:id=file_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_manager_spec -> std
file_manager_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Manager Unit Tests

Tests for FileManager: construction, sorting, navigation, and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/file_manager/file_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for FileManager: construction, sorting, navigation, and
    show_hidden toggle.

    This describe block exercises the SortField enum used by the file
    manager column-sort selector.

## Scenarios

### SortField

#### has Name variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = SortField.Name
expect(field).to_equal(SortField.Name)
```

</details>

#### has Size variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = SortField.Size
expect(field).to_equal(SortField.Size)
```

</details>

#### has Date variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = SortField.Date
expect(field).to_equal(SortField.Date)
```

</details>

### SortDirection

#### has Ascending variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = SortDirection.Ascending
expect(dir).to_equal(SortDirection.Ascending)
```

</details>

#### has Descending variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = SortDirection.Descending
expect(dir).to_equal(SortDirection.Descending)
```

</details>

### FileEntry

#### constructs with name and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = FileEntry(
    name: "readme.txt",
    kind: FsNodeKind.File,
    size: 1024,
    modified_ns: 0,
    permissions: 0o644
)
expect(entry.name).to_equal("readme.txt")
expect(entry.size).to_equal(1024)
```

</details>

#### constructs directory entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = FileEntry(
    name: "src",
    kind: FsNodeKind.Directory,
    size: 4096,
    modified_ns: 0,
    permissions: 0o755
)
expect(entry.name).to_equal("src")
expect(entry.kind).to_equal(FsNodeKind.Directory)
```

</details>

### FileManager

#### when newly created

#### starts at given path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/home")
expect(fm.current_path).to_equal("/home")
```

</details>

#### starts with empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.entries.len()).to_equal(0)
```

</details>

#### starts with selected_index at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.selected_index).to_equal(0)
```

</details>

#### starts with show_hidden false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.show_hidden).to_equal(false)
```

</details>

#### starts with sort_by Name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.sort_by).to_equal(SortField.Name)
```

</details>

#### starts with sort_dir Ascending

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.sort_dir).to_equal(SortDirection.Ascending)
```

</details>

#### starts with dir_tree_paths containing root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.dir_tree_paths.len()).to_equal(1)
expect(fm.dir_tree_paths[0]).to_equal("/")
```

</details>

#### starts with empty clipboard_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.clipboard_path).to_equal("")
```

</details>

#### starts with empty clipboard_op

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.clipboard_op).to_equal("")
```

</details>

#### starts with nil vfs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.vfs).to_be_nil
```

</details>

#### with different paths

#### respects /home/user path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/home/user")
expect(fm.current_path).to_equal("/home/user")
```

</details>

#### respects root path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fm = FileManager.new("/")
expect(fm.current_path).to_equal("/")
```

</details>

### FileManager sorting

#### _compare_entries sorts by name ascending

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FileEntry(name: "alpha", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "beta", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Name, SortDirection.Ascending)
expect(result).to_be_less_than(0)
```

</details>

#### _compare_entries sorts by name descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FileEntry(name: "alpha", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "beta", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Name, SortDirection.Descending)
expect(result).to_be_greater_than(0)
```

</details>

#### _compare_entries sorts by size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FileEntry(name: "small", kind: FsNodeKind.File, size: 100, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "big", kind: FsNodeKind.File, size: 9999, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Size, SortDirection.Ascending)
expect(result).to_be_less_than(0)
```

</details>

#### _compare_entries sorts by date

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FileEntry(name: "old", kind: FsNodeKind.File, size: 0, modified_ns: 100, permissions: 0)
val b = FileEntry(name: "new", kind: FsNodeKind.File, size: 0, modified_ns: 9999, permissions: 0)
val result = _compare_entries(a, b, SortField.Date, SortDirection.Ascending)
expect(result).to_be_less_than(0)
```

</details>

#### _sort_file_entries sorts list by name

1. FileEntry
2. FileEntry
3. FileEntry
   - Expected: sorted[0].name equals `a.txt`
   - Expected: sorted[1].name equals `b.txt`
   - Expected: sorted[2].name equals `c.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    FileEntry(name: "c.txt", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0),
    FileEntry(name: "a.txt", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0),
    FileEntry(name: "b.txt", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
]
val sorted = _sort_file_entries(entries, SortField.Name, SortDirection.Ascending)
expect(sorted[0].name).to_equal("a.txt")
expect(sorted[1].name).to_equal("b.txt")
expect(sorted[2].name).to_equal("c.txt")
```

</details>

#### _compare_entries returns 0 for equal names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = FileEntry(name: "same", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "same", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Name, SortDirection.Ascending)
expect(result).to_equal(0)
```

</details>

### FileManager navigation

#### navigate_to changes current_path

1. var fm = FileManager new
2. fm navigate to
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.navigate_to("/home")
expect(fm.current_path).to_equal("/home")
```

</details>

#### navigate_to resets selected_index

1. var fm = FileManager new
2. fm navigate to
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.selected_index = 5
fm.navigate_to("/home")
expect(fm.selected_index).to_equal(0)
```

</details>

#### navigate_up goes to parent directory

1. var fm = FileManager new
2. fm navigate up
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/home/user")
fm.navigate_up()
expect(fm.current_path).to_equal("/home")
```

</details>

#### navigate_up from root stays at root

1. var fm = FileManager new
2. fm navigate up
   - Expected: fm.current_path equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.navigate_up()
expect(fm.current_path).to_equal("/")
```

</details>

#### open_selected resolves parent entries in-place

1. var fm = FileManager new
2. FileEntry
3. fm open selected
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/home/user")
fm.entries = [
    FileEntry(name: "..", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
]
fm.open_selected()
expect(fm.current_path).to_equal("/home")
```

</details>

#### open_selected navigates when stat resolves a non-directory entry to a directory

1. var vfs = VfsManager new
   - Expected: mounted.is_ok() is true
2. var fm = FileManager with vfs
3. FileEntry
4. fm open selected
   - Expected: fm.current_path equals `/home/docs`
   - Expected: fs.last_stat_path equals `/home/docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val fs = FileManagerOpenStatFs.new(FsNodeKind.Directory)
val mounted = vfs.mount(path: "/", fs_type: "mock", device: "", read_only: false, fs: fs)
expect(mounted.is_ok()).to_equal(true)
var fm = FileManager.with_vfs("/home", vfs)
fm.entries = [
    FileEntry(name: "docs", kind: FsNodeKind.Symlink, size: 0, modified_ns: 0, permissions: 0)
]
fm.open_selected()
expect(fm.current_path).to_equal("/home/docs")
expect(fs.last_stat_path).to_equal("/home/docs")
```

</details>

### FileManager selection

#### select_next increments selected_index

1. var fm = FileManager new
2. FileEntry
3. FileEntry
4. fm select next
   - Expected: fm.selected_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.entries = [
    FileEntry(name: "a", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0),
    FileEntry(name: "b", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
]
fm.select_next()
expect(fm.selected_index).to_equal(1)
```

</details>

#### select_next does not exceed entries length

1. var fm = FileManager new
2. FileEntry
3. fm select next
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.entries = [
    FileEntry(name: "a", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
]
fm.selected_index = 0
fm.select_next()
expect(fm.selected_index).to_equal(0)
```

</details>

#### select_prev decrements selected_index

1. var fm = FileManager new
2. FileEntry
3. FileEntry
4. fm select prev
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.entries = [
    FileEntry(name: "a", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0),
    FileEntry(name: "b", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
]
fm.selected_index = 1
fm.select_prev()
expect(fm.selected_index).to_equal(0)
```

</details>

#### select_prev does not go below 0

1. var fm = FileManager new
2. fm select prev
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.selected_index = 0
fm.select_prev()
expect(fm.selected_index).to_equal(0)
```

</details>

### FileManager show_hidden toggle

#### toggle_hidden flips from false to true

1. var fm = FileManager new
2. fm toggle hidden
   - Expected: fm.show_hidden is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.toggle_hidden()
expect(fm.show_hidden).to_equal(true)
```

</details>

#### toggle_hidden flips from true to false

1. var fm = FileManager new
2. fm toggle hidden
   - Expected: fm.show_hidden is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.show_hidden = true
fm.toggle_hidden()
expect(fm.show_hidden).to_equal(false)
```

</details>

### FileManager set_sort

#### changes sort field to Size

1. var fm = FileManager new
2. fm set sort
   - Expected: fm.sort_by equals `SortField.Size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.set_sort(SortField.Size)
expect(fm.sort_by).to_equal(SortField.Size)
```

</details>

#### changes sort field to Date

1. var fm = FileManager new
2. fm set sort
   - Expected: fm.sort_by equals `SortField.Date`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fm = FileManager.new("/")
fm.set_sort(SortField.Date)
expect(fm.sort_by).to_equal(SortField.Date)
```

</details>

### FileManager format helpers

#### format_size returns bytes for small sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size(512)
expect(result).to_contain("B")
```

</details>

#### format_size returns KB for kilobyte sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size(2048)
expect(result).to_contain("KB")
```

</details>

#### format_size returns MB for megabyte sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_size(2097152)
expect(result).to_contain("MB")
```

</details>

#### format_kind returns File for file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_kind(FsNodeKind.File)
expect(result).to_equal("File")
```

</details>

#### format_kind returns Dir for directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_kind(FsNodeKind.Directory)
expect(result).to_equal("Dir")
```

</details>

#### kind_icon returns folder for directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = kind_icon(FsNodeKind.Directory)
expect(result).to_equal("folder")
```

</details>

### FileManager open path helpers

#### _resolve_open_path keeps current directory for dot entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_resolve_open_path("/home/user", ".")).to_equal("/home/user")
```

</details>

#### _resolve_open_path resolves parent for dot-dot entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_resolve_open_path("/home/user", "..")).to_equal("/home")
```

</details>

#### _should_navigate_in_place prefers stat-resolved directories

1. var vfs = VfsManager new
   - Expected: mounted.is_ok() is true
   - Expected: _should_navigate_in_place("docs", FsNodeKind.Symlink, "/home/docs", vfs) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = VfsManager.new()
val fs = FileManagerOpenStatFs.new(FsNodeKind.Directory)
val mounted = vfs.mount(path: "/", fs_type: "mock", device: "", read_only: false, fs: fs)
expect(mounted.is_ok()).to_equal(true)
expect(_should_navigate_in_place("docs", FsNodeKind.Symlink, "/home/docs", vfs)).to_equal(true)
```

</details>

#### _should_navigate_in_place leaves regular files to the launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_should_navigate_in_place("notes.txt", FsNodeKind.File, "/home/notes.txt", nil)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
