# Jsonl Watcher Specification

> <details>

<!-- sdn-diagram:id=jsonl_watcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jsonl_watcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jsonl_watcher_spec -> app
jsonl_watcher_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jsonl_watcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jsonl Watcher Specification

## Scenarios

### JsonlWatcher

#### tails newly discovered transcripts from EOF instead of replaying backlog

-  prepare tree
- file write
- var watcher = JsonlWatcher with dir
   - Expected: initial.len() equals `0`
   - Expected: watcher.watched_count() equals `1`
- file append text
   - Expected: appended.len() equals `1`
- dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _tmp_root("tail")
val project = "proj_a"
val transcript = "{root}/{project}/session.jsonl"
_prepare_tree(root, project)

val existing = _tool_use_line("src/old_1.spl", 1) + "\n" + _tool_use_line("src/old_2.spl", 2) + "\n"
file_write(transcript, existing)

var watcher = JsonlWatcher.with_dir(root)
val initial = watcher.poll()
expect(initial.len()).to_equal(0)
expect(watcher.watched_count()).to_equal(1)

file_append_text(transcript, _tool_use_line("src/new_append.spl", 3) + "\n")
val appended = watcher.poll()
expect(appended.len()).to_equal(1)

dir_remove(root, true)
```

</details>

#### resets offset after transcript truncation so replacement content is read

-  prepare tree
- file write
- var watcher = JsonlWatcher with dir
   - Expected: watcher.poll().len() equals `0`
- file append text
   - Expected: watcher.poll().len() equals `1`
- file write
   - Expected: rotated.len() equals `1`
- dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _tmp_root("truncate")
val project = "proj_b"
val transcript = "{root}/{project}/session.jsonl"
_prepare_tree(root, project)

file_write(transcript, _tool_use_line("src/original.spl", 1) + "\n")
var watcher = JsonlWatcher.with_dir(root)
expect(watcher.poll().len()).to_equal(0)

file_append_text(transcript, _tool_use_line("src/appended.spl", 2) + "\n")
expect(watcher.poll().len()).to_equal(1)

file_write(transcript, _tool_use_line("x.spl", 3) + "\n")
val rotated = watcher.poll()
expect(rotated.len()).to_equal(1)

dir_remove(root, true)
```

</details>

#### ignores stray files in the watch root while scanning project directories

- dir remove
- dir create
- file write
- var watcher = JsonlWatcher with dir
   - Expected: events.len() equals `0`
   - Expected: watcher.watched_count() equals `0`
- dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _tmp_root("root_file")
dir_remove(root, true)
dir_create(root, true)
file_write("{root}/README.txt", "not a transcript root\n")

var watcher = JsonlWatcher.with_dir(root)
val events = watcher.poll()
expect(events.len()).to_equal(0)
expect(watcher.watched_count()).to_equal(0)

dir_remove(root, true)
```

</details>

#### holds partial lines until the JSONL record is newline terminated

-  prepare tree
- file write
- var watcher = JsonlWatcher with dir
   - Expected: watcher.poll().len() equals `0`
- file append text
   - Expected: watcher.poll().len() equals `0`
- file append text
   - Expected: completed.len() equals `1`
- dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _tmp_root("partial")
val project = "proj_c"
val transcript = "{root}/{project}/session.jsonl"
_prepare_tree(root, project)

file_write(transcript, "")
var watcher = JsonlWatcher.with_dir(root)
expect(watcher.poll().len()).to_equal(0)

file_append_text(transcript, "{\"type\":\"tool_use\"")
expect(watcher.poll().len()).to_equal(0)

file_append_text(transcript, ",\"name\":\"Read\"}\n")
val completed = watcher.poll()
expect(completed.len()).to_equal(1)
expect(completed[0]).to_contain("\"tool_use\"")
expect(completed[0]).to_contain("\"Read\"")

dir_remove(root, true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/jsonl_watcher_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JsonlWatcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
