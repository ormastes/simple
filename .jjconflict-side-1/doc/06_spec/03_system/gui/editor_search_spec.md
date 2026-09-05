# Editor Search Specification

> <details>

<!-- sdn-diagram:id=editor_search_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_search_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_search_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_search_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Search Specification

## Scenarios

### editor search — structs

#### defines SearchMatch with line, col, length, context

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("struct SearchMatch:")).to_equal(true)
expect(src.contains("line: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
expect(src.contains("length: i64")).to_equal(true)
expect(src.contains("context: text")).to_equal(true)
```

</details>

#### defines SearchState with query, matches, current_match, active, wrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("struct SearchState:")).to_equal(true)
expect(src.contains("query: text")).to_equal(true)
expect(src.contains("matches: [SearchMatch]")).to_equal(true)
expect(src.contains("current_match: i64")).to_equal(true)
expect(src.contains("active: bool")).to_equal(true)
expect(src.contains("wrap: bool")).to_equal(true)
```

</details>

#### defines GrepResult with path, line, content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("struct GrepResult:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("content: text")).to_equal(true)
```

</details>

### editor search — state management

#### has search_new returning empty state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_new() -> SearchState:")).to_equal(true)
expect(src.contains("active: false")).to_equal(true)
expect(src.contains("wrap: true")).to_equal(true)
```

</details>

#### has search_activate setting query and finding matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_activate(state: SearchState, query: text, content: text) -> SearchState:")).to_equal(true)
expect(src.contains("active: true")).to_equal(true)
```

</details>

#### has search_next advancing current_match with wrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_next(state: SearchState) -> SearchState:")).to_equal(true)
expect(src.contains("var next_idx = state.current_match + 1")).to_equal(true)
```

</details>

#### has search_prev going to previous match with wrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_prev(state: SearchState) -> SearchState:")).to_equal(true)
expect(src.contains("var prev_idx = state.current_match - 1")).to_equal(true)
```

</details>

#### has search_clear resetting state to inactive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_clear(state: SearchState) -> SearchState:")).to_equal(true)
expect(src.contains("active: false")).to_equal(true)
```

</details>

#### has search_current returning current match nil-safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_current(state: SearchState) -> SearchMatch:")).to_equal(true)
expect(src.contains("line: -1, col: -1, length: 0")).to_equal(true)
```

</details>

### editor search — text search

#### has search_in_text finding all matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_in_text(content: text, query: text) -> [SearchMatch]:")).to_equal(true)
```

</details>

#### splits content by newlines for line tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("val lines = content.split")).to_equal(true)
```

</details>

#### uses internal _search_index_of for position finding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn _search_index_of(haystack: text, needle: text, start: i64) -> i64:")).to_equal(true)
expect(src.contains("haystack.slice(pos, pos + n_len)")).to_equal(true)
```

</details>

### editor search — grep

#### has grep_in_file searching a single file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn grep_in_file(path: text, query: text) -> [GrepResult]:")).to_equal(true)
expect(src.contains("rt_file_read_text(path)")).to_equal(true)
```

</details>

#### has grep_files for recursive cross-file search

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn grep_files(root: text, query: text, extensions: [text]) -> [GrepResult]:")).to_equal(true)
expect(src.contains("rt_dir_list(root)")).to_equal(true)
```

</details>

#### recurses into subdirectories using rt_dir_exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("rt_dir_exists(full_path)")).to_equal(true)
expect(src.contains("grep_files(full_path, query, extensions)")).to_equal(true)
```

</details>

#### filters files by extension with _search_ext_match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn _search_ext_match(filename: text, extensions: [text]) -> bool:")).to_equal(true)
expect(src.contains("filename.ends_with(ext)")).to_equal(true)
```

</details>

#### matches all files when extensions list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("if extensions.len() == 0:")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_search_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor search — structs
- editor search — state management
- editor search — text search
- editor search — grep

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
