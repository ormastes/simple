# Sprof Loader Specification

> <details>

<!-- sdn-diagram:id=sprof_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sprof_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sprof_loader_spec -> std
sprof_loader_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sprof_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sprof Loader Specification

## Scenarios

### Persistent .sprof Loader Contract

### profile validation

#### should load exact compatible profile records

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_profile_record_status("exact", true, true)).to_equal("loaded")
```

</details>

#### should reject corrupt profile records

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_profile_record_status("corrupt", true, true)).to_equal("invalid")
```

</details>

#### should ignore stale workload records

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_profile_record_status("exact", true, false)).to_equal("ignored")
```

</details>

#### should reject mismatched module identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_profile_record_status("exact", false, true)).to_equal("incompatible")
```

</details>

#### should load persisted profile text for matching module and workload

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = sprof_load_profile_text(
    "header;module=mod-a;workload=boot\nfunction;key=main;count=7\nfunction;key=draw;count=5",
    "mod-a",
    "boot"
)
expect(profile.status).to_equal("loaded")
expect(profile.function_count).to_equal(2)
expect(profile.merged_count).to_equal(12)
```

</details>

#### should load function, block, and edge records separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = sprof_load_profile_text(
    "header;schema=sprof-v1;module=mod-a;workload=boot\nfunction;key=main;count=7\nblock;function=main;key=entry;count=3\nedge;from=entry;to=exit;count=2",
    "mod-a",
    "boot"
)
expect(profile.status).to_equal("loaded")
expect(profile.schema_version).to_equal("sprof-v1")
expect(profile.function_count).to_equal(1)
expect(profile.block_count).to_equal(1)
expect(profile.edge_count).to_equal(1)
expect(profile.function_merged_count).to_equal(7)
expect(profile.block_merged_count).to_equal(3)
expect(profile.edge_merged_count).to_equal(2)
expect(profile.merged_count).to_equal(12)
```

</details>

#### should ignore persisted profile text for mismatched workload

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = sprof_load_profile_text(
    "header;module=mod-a;workload=test\nfunction;key=main;count=7",
    "mod-a",
    "boot"
)
expect(profile.status).to_equal("ignored")
expect(profile.diagnostics).to_contain("workload_mismatch:test")
```

</details>

#### should report module and schema diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = sprof_load_profile_text(
    "header;schema=sprof-v2;module=mod-b;workload=boot\nfunction;key=main;count=7",
    "mod-a",
    "boot"
)
expect(profile.status).to_equal("incompatible")
expect(profile.diagnostic_count).to_equal(2)
expect(profile.diagnostics).to_contain("schema_mismatch:sprof-v2")
expect(profile.diagnostics).to_contain("module_mismatch:mod-b")
```

</details>

#### should serialize typed counter records for persistent profiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val function_record = sprof_counter_record("function", "main", "", 7)
val block_record = sprof_counter_record("block", "entry", "main", 3)
val edge_record = sprof_counter_record("edge", "entry", "exit", 2)
expect(sprof_counter_record_valid(function_record)).to_equal(true)
expect(sprof_counter_record_valid(block_record)).to_equal(true)
expect(sprof_counter_record_valid(edge_record)).to_equal(true)
expect(sprof_serialize_record(function_record)).to_equal("function;key=main;count=7")
expect(sprof_serialize_record(block_record)).to_equal("block;function=main;key=entry;count=3")
expect(sprof_serialize_record(edge_record)).to_equal("edge;from=entry;to=exit;count=2")
```

</details>

#### should round trip serialized persistent profile text

1. sprof counter record
2. sprof counter record
3. sprof counter record
   - Expected: profile.status equals `loaded`
   - Expected: profile.function_merged_count equals `7`
   - Expected: profile.block_merged_count equals `3`
   - Expected: profile.edge_merged_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = sprof_serialize_profile(
    "mod-a",
    "boot",
    [
        sprof_counter_record("function", "main", "", 7),
        sprof_counter_record("block", "entry", "main", 3),
        sprof_counter_record("edge", "entry", "exit", 2)
    ]
)
val profile = sprof_load_profile_text(body, "mod-a", "boot")
expect(body).to_contain("header;schema=sprof-v1;module=mod-a;workload=boot")
expect(profile.status).to_equal("loaded")
expect(profile.function_merged_count).to_equal(7)
expect(profile.block_merged_count).to_equal(3)
expect(profile.edge_merged_count).to_equal(2)
```

</details>

#### should reject unsafe profile writer tokens and invalid records

1. [sprof counter record


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = sprof_profile_write_diagnostics(
    "mod;a",
    "boot",
    [sprof_counter_record("function", "bad;key", "", 1)]
)
expect(diagnostics).to_contain("invalid_module_identity")
expect(diagnostics).to_contain("invalid_record:0")
```

</details>

#### should write and reload persistent profile files

1. sprof counter record
2. sprof counter record
   - Expected: write.wrote is true
   - Expected: write.record_count equals `2`
   - Expected: write.diagnostic_count equals `0`
   - Expected: profile.status equals `loaded`
   - Expected: profile.function_merged_count equals `11`
   - Expected: profile.edge_merged_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_sprof_loader_spec_roundtrip.sprof"
val write = sprof_write_profile_file(
    path,
    "mod-a",
    "boot",
    [
        sprof_counter_record("function", "main", "", 11),
        sprof_counter_record("edge", "entry", "exit", 5)
    ]
)
val profile = sprof_load_profile_file(path, "mod-a", "boot")
expect(write.wrote).to_equal(true)
expect(write.record_count).to_equal(2)
expect(write.diagnostic_count).to_equal(0)
expect(profile.status).to_equal("loaded")
expect(profile.function_merged_count).to_equal(11)
expect(profile.edge_merged_count).to_equal(5)
```

</details>

#### should convert native counter metadata lines into persistent profile records

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val function_record = sprof_counter_record_from_native_counter_line(
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=mir:main:entry|initial=9|symbol=__simple_profile_counter_0_function_entry"
)
val block_record = sprof_counter_record_from_native_counter_line(
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=1|kind=basic_block|key=mir:main:bb0|initial=4|symbol=__simple_profile_counter_1_basic_block"
)
val edge_record = sprof_counter_record_from_native_counter_line(
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=2|kind=edge|key=main:entry->main:exit|initial=3|symbol=__simple_profile_counter_2_edge"
)
expect(function_record.record_kind).to_equal("function")
expect(function_record.count).to_equal(9)
expect(block_record.record_kind).to_equal("block")
expect(block_record.secondary_key).to_equal("main")
expect(edge_record.record_kind).to_equal("edge")
expect(edge_record.key).to_equal("main:entry")
expect(edge_record.secondary_key).to_equal("main:exit")
```

</details>

#### should convert native metadata with final counter values into persistent records

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = [
    "section|label=simple_profile_counter_section__simple_profile_counters|name=.simple.profile.counters|records=2",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=c:main:entry|initial=0|symbol=__simple_profile_counter_0_function_entry",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=1|kind=basic_block|key=c:main:bb0|initial=0|symbol=__simple_profile_counter_1_basic_block"
]
val direct = sprof_counter_record_from_native_counter_line_with_count(metadata[1], 17)
val imported = sprof_records_from_native_counter_values(metadata, [17, 5])

expect(direct.record_kind).to_equal("function")
expect(direct.count).to_equal(17)
expect(imported.record_count).to_equal(2)
expect(imported.diagnostic_count).to_equal(0)
expect(imported.records[0].key).to_equal("c:main:entry")
expect(imported.records[0].count).to_equal(17)
expect(imported.records[1].record_kind).to_equal("block")
expect(imported.records[1].count).to_equal(5)
```

</details>

#### should diagnose native count snapshots that do not match metadata slots

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = [
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=c:main:entry|initial=0|symbol=__simple_profile_counter_0_function_entry",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=2|kind=function_entry|key=c:helper:entry|initial=0|symbol=__simple_profile_counter_2_function_entry"
]
val imported = sprof_records_from_native_counter_values(metadata, [9, 99])

expect(imported.record_count).to_equal(1)
expect(imported.diagnostics).to_contain("missing_count:2")
expect(imported.diagnostics).to_contain("count_without_metadata:1")
```

</details>

#### should write native counter snapshots as reloadable persistent profile files

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_sprof_native_counter_import.sprof"
val metadata = [
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=c:main:entry|initial=0|symbol=__simple_profile_counter_0_function_entry",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=1|kind=edge|key=c:main:entry->exit|initial=0|symbol=__simple_profile_counter_1_edge"
]
val write = sprof_write_native_counter_profile_file(path, "native-mod", "run-a", metadata, [13, 4])
val loaded = sprof_load_profile_file(path, "native-mod", "run-a")

expect(write.wrote).to_equal(true)
expect(write.record_count).to_equal(2)
expect(write.diagnostic_count).to_equal(0)
expect(loaded.status).to_equal("loaded")
expect(loaded.record_count).to_equal(2)
expect(loaded.function_merged_count).to_equal(13)
expect(loaded.edge_merged_count).to_equal(4)
```

</details>

#### should build reloadable sprof text from native counter section lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = sprof_counter_records_from_native_section_lines([
    "section|label=simple_profile_counter_section__simple_profile_counters|name=.simple.profile.counters|records=2",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=mir:main:entry|initial=9|symbol=__simple_profile_counter_0_function_entry",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=1|kind=basic_block|key=mir:main:bb0|initial=4|symbol=__simple_profile_counter_1_basic_block"
])
val body = sprof_serialize_profile("native-mod", "smoke", records)
val profile = sprof_load_profile_text(body, "native-mod", "smoke")
expect(records.len()).to_equal(2)
expect(profile.status).to_equal("loaded")
expect(profile.function_merged_count).to_equal(9)
expect(profile.block_merged_count).to_equal(4)
```

</details>

### hot path policy

#### should forbid profile file operations in hot paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = sprof_hot_path_policy()
expect(policy).to_contain("no_file_open")
expect(policy).to_contain("no_shell_out")
expect(policy).to_contain("no_repo_scan")
```

</details>

#### should allow already loaded summaries in hot paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_hot_path_allows_operation("file_open")).to_equal(false)
expect(sprof_hot_path_allows_operation("shell_out")).to_equal(false)
expect(sprof_hot_path_allows_operation("repo_scan")).to_equal(false)
expect(sprof_hot_path_allows_operation("use_loaded_summary")).to_equal(true)
```

</details>

### profile merge

#### should merge valid counters with saturating-safe contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_merge_count(10, 7)).to_equal(17)
```

</details>

#### should treat invalid negative counters as diagnostic-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sprof_merge_count(-1, 7)).to_equal(0)
```

</details>

#### should report merge diagnostic and saturation state

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = sprof_merge_summary(-1, 7)
expect(invalid.merged_count).to_equal(0)
expect(invalid.diagnostic_count).to_equal(1)
expect(invalid.function_count).to_equal(0)
expect(invalid.block_count).to_equal(0)
expect(invalid.edge_count).to_equal(0)

val saturated = sprof_merge_summary(9223372036854775806, 7)
expect(saturated.merged_count).to_equal(9223372036854775807)
expect(saturated.saturated).to_equal(true)
```

</details>

### diagnostics

#### should bound diagnostics and report truncation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = sprof_bounded_diagnostics(["bad_header", "bad_record", "bad_edge"], 2)
expect(diagnostics.len()).to_equal(3)
expect(diagnostics).to_contain("bad_header")
expect(diagnostics).to_contain("bad_record")
expect(diagnostics).to_contain("diagnostics_truncated:1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/optimize/feature/sprof_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Persistent .sprof Loader Contract
- profile validation
- hot path policy
- profile merge
- diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
