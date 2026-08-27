# Editor Search Specification

> Tests covering editor search — structs, editor search — state management, editor search — text search, editor search — grep.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Search Specification

## Scenarios

### editor search — structs

#### defines SearchMatch with line, col, length, context

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines SearchMatch with line, col, length, context
   - Expected: src contains `struct SearchMatch:`
   - Expected: src contains `line: i64`
   - Expected: src contains `col: i64`
   - Expected: src contains `length: i64`
   - Expected: src contains `context: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SearchMatch with line, col, length, context")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("struct SearchMatch:")).to_equal(true)
expect(src.contains("line: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
expect(src.contains("length: i64")).to_equal(true)
expect(src.contains("context: text")).to_equal(true)
```

</details>

#### defines SearchState with query, matches, current_match, active, wrap

- defines SearchState with query, matches, current_match, active, wrap
   - Expected: src contains `struct SearchState:`
   - Expected: src contains `query: text`
   - Expected: src contains `matches: [SearchMatch]`
   - Expected: src contains `current_match: i64`
   - Expected: src contains `active: bool`
   - Expected: src contains `wrap: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SearchState with query, matches, current_match, active, wrap")
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

- defines GrepResult with path, line, content
   - Expected: src contains `struct GrepResult:`
   - Expected: src contains `path: text`
   - Expected: src contains `content: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines GrepResult with path, line, content")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("struct GrepResult:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("content: text")).to_equal(true)
```

</details>

### editor search — state management

#### has search_new returning empty state

- has search_new returning empty state
   - Expected: src contains `fn search_new() -> SearchState:`
   - Expected: src contains `active: false`
   - Expected: src contains `wrap: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_new returning empty state")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_new() -> SearchState:")).to_equal(true)
expect(src.contains("active: false")).to_equal(true)
expect(src.contains("wrap: true")).to_equal(true)
```

</details>

#### has search_activate setting query and finding matches

- has search_activate setting query and finding matches
   - Expected: src contains `fn search_activate(state: SearchState, query: text, content: text) -> SearchS... (full value in folded executable source)`
   - Expected: src contains `active: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_activate setting query and finding matches")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_activate(state: SearchState, query: text, content: text) -> SearchState:")).to_equal(true)
expect(src.contains("active: true")).to_equal(true)
```

</details>

#### has search_next advancing current_match with wrap

- has search_next advancing current_match with wrap
   - Expected: src contains `fn search_next(state: SearchState) -> SearchState:`
   - Expected: src contains `var next_idx = state.current_match + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_next advancing current_match with wrap")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_next(state: SearchState) -> SearchState:")).to_equal(true)
expect(src.contains("var next_idx = state.current_match + 1")).to_equal(true)
```

</details>

#### has search_prev going to previous match with wrap

- has search_prev going to previous match with wrap
   - Expected: src contains `fn search_prev(state: SearchState) -> SearchState:`
   - Expected: src contains `var prev_idx = state.current_match - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_prev going to previous match with wrap")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_prev(state: SearchState) -> SearchState:")).to_equal(true)
expect(src.contains("var prev_idx = state.current_match - 1")).to_equal(true)
```

</details>

#### has search_clear resetting state to inactive

- has search_clear resetting state to inactive
   - Expected: src contains `fn search_clear(state: SearchState) -> SearchState:`
   - Expected: src contains `active: false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_clear resetting state to inactive")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_clear(state: SearchState) -> SearchState:")).to_equal(true)
expect(src.contains("active: false")).to_equal(true)
```

</details>

#### has search_current returning current match nil-safe

- has search_current returning current match nil-safe
   - Expected: src contains `fn search_current(state: SearchState) -> SearchMatch:`
   - Expected: src contains `line: -1, col: -1, length: 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_current returning current match nil-safe")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_current(state: SearchState) -> SearchMatch:")).to_equal(true)
expect(src.contains("line: -1, col: -1, length: 0")).to_equal(true)
```

</details>

### editor search — text search

#### has search_in_text finding all matches

- has search_in_text finding all matches
   - Expected: src contains `fn search_in_text(content: text, query: text) -> [SearchMatch]:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has search_in_text finding all matches")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn search_in_text(content: text, query: text) -> [SearchMatch]:")).to_equal(true)
```

</details>

#### splits content by newlines for line tracking

- splits content by newlines for line tracking
   - Expected: src contains `val lines = content.split`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("splits content by newlines for line tracking")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("val lines = content.split")).to_equal(true)
```

</details>

#### uses internal _search_index_of for position finding

- uses internal _search_index_of for position finding
   - Expected: src contains `fn _search_index_of(haystack: text, needle: text, start: i64) -> i64:`
   - Expected: src contains `haystack.slice(pos, pos + n_len)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses internal _search_index_of for position finding")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn _search_index_of(haystack: text, needle: text, start: i64) -> i64:")).to_equal(true)
expect(src.contains("haystack.slice(pos, pos + n_len)")).to_equal(true)
```

</details>

### editor search — grep

#### has grep_in_file searching a single file

- has grep_in_file searching a single file
   - Expected: src contains `fn grep_in_file(path: text, query: text) -> [GrepResult]:`
   - Expected: src contains `rt_file_read_text(path)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has grep_in_file searching a single file")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn grep_in_file(path: text, query: text) -> [GrepResult]:")).to_equal(true)
expect(src.contains("rt_file_read_text(path)")).to_equal(true)
```

</details>

#### has grep_files for recursive cross-file search

- has grep_files for recursive cross-file search
   - Expected: src contains `fn grep_files(root: text, query: text, extensions: [text]) -> [GrepResult]:`
   - Expected: src contains `rt_dir_list(root)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has grep_files for recursive cross-file search")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn grep_files(root: text, query: text, extensions: [text]) -> [GrepResult]:")).to_equal(true)
expect(src.contains("rt_dir_list(root)")).to_equal(true)
```

</details>

#### recurses into subdirectories using rt_dir_exists

- recurses into subdirectories using rt_dir_exists
   - Expected: src contains `rt_dir_exists(full_path)`
   - Expected: src contains `grep_files(full_path, query, extensions)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recurses into subdirectories using rt_dir_exists")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("rt_dir_exists(full_path)")).to_equal(true)
expect(src.contains("grep_files(full_path, query, extensions)")).to_equal(true)
```

</details>

#### filters files by extension with _search_ext_match

- filters files by extension with _search_ext_match
   - Expected: src contains `fn _search_ext_match(filename: text, extensions: [text]) -> bool:`
   - Expected: src contains `filename.ends_with(ext)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters files by extension with _search_ext_match")
val src = read_text("src/lib/editor/services/search.spl")
expect(src.contains("fn _search_ext_match(filename: text, extensions: [text]) -> bool:")).to_equal(true)
expect(src.contains("filename.ends_with(ext)")).to_equal(true)
```

</details>

#### matches all files when extensions list is empty

- matches all files when extensions list is empty
   - Expected: src contains `if extensions.len() == 0:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches all files when extensions list is empty")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor search — structs, editor search — state management, editor search — text search, editor search — grep.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4da46617c98403af61ccb9bc8b24a52628b1181183123aca6dbb8f8411e23a58`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4da46617c98403af61ccb9bc8b24a52628b1181183123aca6dbb8f8411e23a58`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4da46617c98403af61ccb9bc8b24a52628b1181183123aca6dbb8f8411e23a58`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_search_spec.spl
mirror: doc/06_spec/03_system/gui/editor_search_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_search_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_search_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_search_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SearchMatch with line, col, length, context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_search_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SearchState with query, matches, current_match, active, wrap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_search_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines GrepResult with path, line, content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
