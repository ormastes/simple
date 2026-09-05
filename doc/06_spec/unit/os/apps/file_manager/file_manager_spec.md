# File Manager Unit Tests

> Tests for FileManager: construction, sorting, navigation, and

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
| Source | `test/unit/os/apps/file_manager/file_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for FileManager: construction, sorting, navigation, and
    show_hidden toggle.

    This describe block exercises the SortField enum used by the file
    manager column-sort selector.

## Scenarios

### SortField

#### has Name variant

- has Name variant
   - Expected: field equals `SortField.Name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Name variant")
"""SortField.Name variant exists and equals itself."""
val field = SortField.Name
expect(field).to_equal(SortField.Name)
```

</details>

#### has Size variant

- has Size variant
   - Expected: field equals `SortField.Size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Size variant")
val field = SortField.Size
expect(field).to_equal(SortField.Size)
```

</details>

#### has Date variant

- has Date variant
   - Expected: field equals `SortField.Date`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Date variant")
val field = SortField.Date
expect(field).to_equal(SortField.Date)
```

</details>

### SortDirection

#### has Ascending variant

- has Ascending variant
   - Expected: dir equals `SortDirection.Ascending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Ascending variant")
val dir = SortDirection.Ascending
expect(dir).to_equal(SortDirection.Ascending)
```

</details>

#### has Descending variant

- has Descending variant
   - Expected: dir equals `SortDirection.Descending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Descending variant")
val dir = SortDirection.Descending
expect(dir).to_equal(SortDirection.Descending)
```

</details>

### FileEntry

#### constructs with name and size

- constructs with name and size
   - Expected: entry.name equals `readme.txt`
   - Expected: entry.size equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with name and size")
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

- constructs directory entry
   - Expected: entry.name equals `src`
   - Expected: entry.kind equals `FsNodeKind.Directory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs directory entry")
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

- starts at given path
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts at given path")
val fm = FileManager.new("/home")
expect(fm.current_path).to_equal("/home")
```

</details>

#### starts with empty entries

- starts with empty entries
   - Expected: fm.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty entries")
val fm = FileManager.new("/")
expect(fm.entries.len()).to_equal(0)
```

</details>

#### starts with selected_index at 0

- starts with selected_index at 0
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with selected_index at 0")
val fm = FileManager.new("/")
expect(fm.selected_index).to_equal(0)
```

</details>

#### starts with show_hidden false

- starts with show_hidden false
   - Expected: fm.show_hidden is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with show_hidden false")
val fm = FileManager.new("/")
expect(fm.show_hidden).to_equal(false)
```

</details>

#### starts with sort_by Name

- starts with sort_by Name
   - Expected: fm.sort_by equals `SortField.Name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with sort_by Name")
val fm = FileManager.new("/")
expect(fm.sort_by).to_equal(SortField.Name)
```

</details>

#### starts with sort_dir Ascending

- starts with sort_dir Ascending
   - Expected: fm.sort_dir equals `SortDirection.Ascending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with sort_dir Ascending")
val fm = FileManager.new("/")
expect(fm.sort_dir).to_equal(SortDirection.Ascending)
```

</details>

#### starts with dir_tree_paths containing root

- starts with dir_tree_paths containing root
   - Expected: fm.dir_tree_paths.len() equals `1`
   - Expected: fm.dir_tree_paths[0] equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with dir_tree_paths containing root")
val fm = FileManager.new("/")
expect(fm.dir_tree_paths.len()).to_equal(1)
expect(fm.dir_tree_paths[0]).to_equal("/")
```

</details>

#### starts with empty clipboard_path

- starts with empty clipboard_path
   - Expected: fm.clipboard_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty clipboard_path")
val fm = FileManager.new("/")
expect(fm.clipboard_path).to_equal("")
```

</details>

#### starts with empty clipboard_op

- starts with empty clipboard_op
   - Expected: fm.clipboard_op equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty clipboard_op")
val fm = FileManager.new("/")
expect(fm.clipboard_op).to_equal("")
```

</details>

#### starts with nil vfs

- starts with nil vfs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with nil vfs")
val fm = FileManager.new("/")
expect(fm.vfs).to_be_nil
```

</details>

#### with different paths

#### respects /home/user path

- respects /home/user path
   - Expected: fm.current_path equals `/home/user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects /home/user path")
val fm = FileManager.new("/home/user")
expect(fm.current_path).to_equal("/home/user")
```

</details>

#### respects root path

- respects root path
   - Expected: fm.current_path equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects root path")
val fm = FileManager.new("/")
expect(fm.current_path).to_equal("/")
```

</details>

### FileManager sorting

#### _compare_entries sorts by name ascending

- _compare_entries sorts by name ascending


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_compare_entries sorts by name ascending")
val a = FileEntry(name: "alpha", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "beta", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Name, SortDirection.Ascending)
expect(result).to_be_less_than(0)
```

</details>

#### _compare_entries sorts by name descending

- _compare_entries sorts by name descending


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_compare_entries sorts by name descending")
val a = FileEntry(name: "alpha", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "beta", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Name, SortDirection.Descending)
expect(result).to_be_greater_than(0)
```

</details>

#### _compare_entries sorts by size

- _compare_entries sorts by size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_compare_entries sorts by size")
val a = FileEntry(name: "small", kind: FsNodeKind.File, size: 100, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "big", kind: FsNodeKind.File, size: 9999, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Size, SortDirection.Ascending)
expect(result).to_be_less_than(0)
```

</details>

#### _compare_entries sorts by date

- _compare_entries sorts by date


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_compare_entries sorts by date")
val a = FileEntry(name: "old", kind: FsNodeKind.File, size: 0, modified_ns: 100, permissions: 0)
val b = FileEntry(name: "new", kind: FsNodeKind.File, size: 0, modified_ns: 9999, permissions: 0)
val result = _compare_entries(a, b, SortField.Date, SortDirection.Ascending)
expect(result).to_be_less_than(0)
```

</details>

#### _sort_file_entries sorts list by name

- _sort_file_entries sorts list by name
   - Expected: sorted[0].name equals `a.txt`
   - Expected: sorted[1].name equals `b.txt`
   - Expected: sorted[2].name equals `c.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_sort_file_entries sorts list by name")
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

- _compare_entries returns 0 for equal names
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_compare_entries returns 0 for equal names")
val a = FileEntry(name: "same", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val b = FileEntry(name: "same", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
val result = _compare_entries(a, b, SortField.Name, SortDirection.Ascending)
expect(result).to_equal(0)
```

</details>

### FileManager navigation

#### navigate_to changes current_path

- navigate_to changes current_path
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigate_to changes current_path")
var fm = FileManager.new("/")
fm.navigate_to("/home")
expect(fm.current_path).to_equal("/home")
```

</details>

#### navigate_to resets selected_index

- navigate_to resets selected_index
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigate_to resets selected_index")
var fm = FileManager.new("/")
fm.selected_index = 5
fm.navigate_to("/home")
expect(fm.selected_index).to_equal(0)
```

</details>

#### navigate_up goes to parent directory

- navigate_up goes to parent directory
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigate_up goes to parent directory")
var fm = FileManager.new("/home/user")
fm.navigate_up()
expect(fm.current_path).to_equal("/home")
```

</details>

#### navigate_up from root stays at root

- navigate_up from root stays at root
   - Expected: fm.current_path equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigate_up from root stays at root")
var fm = FileManager.new("/")
fm.navigate_up()
expect(fm.current_path).to_equal("/")
```

</details>

#### open_selected resolves parent entries in-place

- open_selected resolves parent entries in-place
   - Expected: fm.current_path equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open_selected resolves parent entries in-place")
var fm = FileManager.new("/home/user")
fm.entries = [
    FileEntry(name: "..", kind: FsNodeKind.File, size: 0, modified_ns: 0, permissions: 0)
]
fm.open_selected()
expect(fm.current_path).to_equal("/home")
```

</details>

#### open_selected navigates when stat resolves a non-directory entry to a directory

- open_selected navigates when stat resolves a non-directory entry to a directory
   - Expected: mounted.is_ok() is true
   - Expected: fm.current_path equals `/home/docs`
   - Expected: fs.last_stat_path equals `/home/docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open_selected navigates when stat resolves a non-directory entry to a directory")
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

- select_next increments selected_index
   - Expected: fm.selected_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select_next increments selected_index")
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

- select_next does not exceed entries length
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select_next does not exceed entries length")
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

- select_prev decrements selected_index
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select_prev decrements selected_index")
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

- select_prev does not go below 0
   - Expected: fm.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select_prev does not go below 0")
var fm = FileManager.new("/")
fm.selected_index = 0
fm.select_prev()
expect(fm.selected_index).to_equal(0)
```

</details>

### FileManager show_hidden toggle

#### toggle_hidden flips from false to true

- toggle_hidden flips from false to true
   - Expected: fm.show_hidden is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle_hidden flips from false to true")
var fm = FileManager.new("/")
fm.toggle_hidden()
expect(fm.show_hidden).to_equal(true)
```

</details>

#### toggle_hidden flips from true to false

- toggle_hidden flips from true to false
   - Expected: fm.show_hidden is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggle_hidden flips from true to false")
var fm = FileManager.new("/")
fm.show_hidden = true
fm.toggle_hidden()
expect(fm.show_hidden).to_equal(false)
```

</details>

### FileManager set_sort

#### changes sort field to Size

- changes sort field to Size
   - Expected: fm.sort_by equals `SortField.Size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes sort field to Size")
var fm = FileManager.new("/")
fm.set_sort(SortField.Size)
expect(fm.sort_by).to_equal(SortField.Size)
```

</details>

#### changes sort field to Date

- changes sort field to Date
   - Expected: fm.sort_by equals `SortField.Date`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes sort field to Date")
var fm = FileManager.new("/")
fm.set_sort(SortField.Date)
expect(fm.sort_by).to_equal(SortField.Date)
```

</details>

### FileManager format helpers

#### format_size returns bytes for small sizes

- format_size returns bytes for small sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_size returns bytes for small sizes")
val result = format_size(512)
expect(result).to_contain("B")
```

</details>

#### format_size returns KB for kilobyte sizes

- format_size returns KB for kilobyte sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_size returns KB for kilobyte sizes")
val result = format_size(2048)
expect(result).to_contain("KB")
```

</details>

#### format_size returns MB for megabyte sizes

- format_size returns MB for megabyte sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_size returns MB for megabyte sizes")
val result = format_size(2097152)
expect(result).to_contain("MB")
```

</details>

#### format_kind returns File for file

- format_kind returns File for file
   - Expected: result equals `File`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_kind returns File for file")
val result = format_kind(FsNodeKind.File)
expect(result).to_equal("File")
```

</details>

#### format_kind returns Dir for directory

- format_kind returns Dir for directory
   - Expected: result equals `Dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("format_kind returns Dir for directory")
val result = format_kind(FsNodeKind.Directory)
expect(result).to_equal("Dir")
```

</details>

#### kind_icon returns folder for directory

- kind_icon returns folder for directory
   - Expected: result equals `folder`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kind_icon returns folder for directory")
val result = kind_icon(FsNodeKind.Directory)
expect(result).to_equal("folder")
```

</details>

### FileManager open path helpers

#### _resolve_open_path keeps current directory for dot entries

- _resolve_open_path keeps current directory for dot entries
   - Expected: _resolve_open_path("/home/user", ".") equals `/home/user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_resolve_open_path keeps current directory for dot entries")
expect(_resolve_open_path("/home/user", ".")).to_equal("/home/user")
```

</details>

#### _resolve_open_path resolves parent for dot-dot entries

- _resolve_open_path resolves parent for dot-dot entries
   - Expected: _resolve_open_path("/home/user", "..") equals `/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_resolve_open_path resolves parent for dot-dot entries")
expect(_resolve_open_path("/home/user", "..")).to_equal("/home")
```

</details>

#### _should_navigate_in_place prefers stat-resolved directories

- _should_navigate_in_place prefers stat-resolved directories
   - Expected: mounted.is_ok() is true
   - Expected: _should_navigate_in_place("docs", FsNodeKind.Symlink, "/home/docs", vfs) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_should_navigate_in_place prefers stat-resolved directories")
var vfs = VfsManager.new()
val fs = FileManagerOpenStatFs.new(FsNodeKind.Directory)
val mounted = vfs.mount(path: "/", fs_type: "mock", device: "", read_only: false, fs: fs)
expect(mounted.is_ok()).to_equal(true)
expect(_should_navigate_in_place("docs", FsNodeKind.Symlink, "/home/docs", vfs)).to_equal(true)
```

</details>

#### _should_navigate_in_place leaves regular files to the launcher

- _should_navigate_in_place leaves regular files to the launcher
   - Expected: _should_navigate_in_place("notes.txt", FsNodeKind.File, "/home/notes.txt", nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_should_navigate_in_place leaves regular files to the launcher")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe951705b0b1dd9331a1b9f74489be017151c4d73cf36f623401a5279fef74c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe951705b0b1dd9331a1b9f74489be017151c4d73cf36f623401a5279fef74c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe951705b0b1dd9331a1b9f74489be017151c4d73cf36f623401a5279fef74c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/file_manager/file_manager_spec.spl
mirror: doc/06_spec/unit/os/apps/file_manager/file_manager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/file_manager/file_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/file_manager/file_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/file_manager/file_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/file_manager/file_manager_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Name variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/file_manager/file_manager_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Size variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/file_manager/file_manager_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Date variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
