# File Watcher Specification

> 1. On start: perform initial build

<!-- sdn-diagram:id=file_watcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_watcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_watcher_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_watcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Watcher Specification

1. On start: perform initial build

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCHER-001 |
| Category | Tools \| Development |
| Status | Implemented |
| Source | `test/03_system/feature/usage/file_watcher_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Watcher Behavior

1. On start: perform initial build
2. Watch source file for changes
3. On change: rebuild module
4. Output SMF to .simple/build/ directory

## Syntax

```bash
simple watch src/main.spl
```

## Scenarios

### File Watcher

#### performs initial build on start

1. fn test initial build
2. expect test initial build


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_initial_build() -> bool:
    # Watcher should build on startup
    # SMF file should be created
    true

expect test_initial_build()
```

</details>

#### rebuilds on file change

1. fn test rebuild on change
2. expect test rebuild on change


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_rebuild_on_change() -> bool:
    # Touching the source file should trigger rebuild
    # New SMF should be generated
    true

expect test_rebuild_on_change()
```

</details>

#### outputs SMF to build directory

1. fn test smf output location
2. expect test smf output location


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_smf_output_location() -> bool:
    # SMF files should be in .simple/build/
    true

expect test_smf_output_location()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
