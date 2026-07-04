# Profile Layout Cli Specification

> 1. ] join

<!-- sdn-diagram:id=profile_layout_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=profile_layout_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

profile_layout_cli_spec -> std
profile_layout_cli_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=profile_layout_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Profile Layout Cli Specification

## Scenarios

### Profile Layout CLI Bridge

#### should parse semicolon executable metadata into layout entries

1. ] join
   - Expected: entries.len() equals `2`
   - Expected: entries[0].symbol_name equals `dispatch`
   - Expected: entries[0].section_name equals `.text`
   - Expected: entries[0].original_offset equals `64`
   - Expected: entries[0].size_bytes equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    "symbol=dispatch;section=.text;offset=64;size=80",
    "symbol=unused;section=.text;offset=200;size=40"
].join("\n")
val entries = profile_layout_parse_manifest_text(manifest)

expect(entries.len()).to_equal(2)
expect(entries[0].symbol_name).to_equal("dispatch")
expect(entries[0].section_name).to_equal(".text")
expect(entries[0].original_offset).to_equal(64)
expect(entries[0].size_bytes).to_equal(80)
```

</details>

#### should parse tab executable metadata into layout entries

1. ] join
   - Expected: entries.len() equals `2`
   - Expected: entries[0].symbol_name equals `parse`
   - Expected: entries[1].symbol_name equals `helper`
   - Expected: entries[1].original_offset equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    "entry\t.text\tparse\t160\t96",
    "helper\t.text\t256\t32"
].join("\n")
val entries = profile_layout_parse_manifest_text(manifest)

expect(entries.len()).to_equal(2)
expect(entries[0].symbol_name).to_equal("parse")
expect(entries[1].symbol_name).to_equal("helper")
expect(entries[1].original_offset).to_equal(256)
```

</details>

#### should derive function profiles from native stable sprof keys

1. ] join
   - Expected: profiles.len() equals `2`
   - Expected: profiles[0].symbol_name equals `dispatch`
   - Expected: profiles[0].sample_count equals `8`
   - Expected: profiles[0].size_bytes equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = "symbol=dispatch;section=.text;offset=64;size=80\nsymbol=rare;section=.text;offset=200;size=40"
val entries = profile_layout_parse_manifest_text(manifest)
val profile = [
    "header;schema=sprof-v1;module=demo;workload=smoke",
    "function;key=c:dispatch:entry;count=8",
    "function;key=c:rare:entry;count=1"
].join("\n")
val profiles = profile_layout_parse_sprof_functions(profile, entries)

expect(profiles.len()).to_equal(2)
expect(profiles[0].symbol_name).to_equal("dispatch")
expect(profiles[0].sample_count).to_equal(8)
expect(profiles[0].size_bytes).to_equal(80)
```

</details>

#### should consume reusable records from the persistent sprof loader

1. ] join
   - Expected: loaded.status equals `loaded`
   - Expected: loaded.record_count equals `3`
   - Expected: profiles.len() equals `2`
   - Expected: profiles[0].symbol_name equals `dispatch`
   - Expected: profiles[1].symbol_name equals `rare`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = "symbol=dispatch;section=.text;offset=64;size=80\nsymbol=rare;section=.text;offset=200;size=40"
val entries = profile_layout_parse_manifest_text(manifest)
val loaded = sprof_load_profile_text([
    "header;schema=sprof-v1;module=demo;workload=smoke",
    "function;key=c:dispatch:entry;count=8",
    "function;key=c:rare:entry;count=1",
    "block;function=dispatch;key=entry;count=3"
].join("\n"), "demo", "smoke")
val profiles = profile_layout_profiles_from_sprof_records(loaded.records, entries)

expect(loaded.status).to_equal("loaded")
expect(loaded.record_count).to_equal(3)
expect(profiles.len()).to_equal(2)
expect(profiles[0].symbol_name).to_equal("dispatch")
expect(profiles[1].symbol_name).to_equal("rare")
```

</details>

#### should accept already materialized loader records without profile text parsing

1. [sprof counter record
   - Expected: profiles.len() equals `1`
   - Expected: profiles[0].symbol_name equals `main`
   - Expected: profiles[0].sample_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = profile_layout_parse_manifest_text("symbol=main;section=.text;offset=0;size=32")
val profiles = profile_layout_profiles_from_sprof_records(
    [sprof_counter_record("function", "c:main:entry", "", 4)],
    entries
)

expect(profiles.len()).to_equal(1)
expect(profiles[0].symbol_name).to_equal("main")
expect(profiles[0].sample_count).to_equal(4)
```

</details>

#### should build a deterministic hot and cold layout manifest

1. ] join
2. ] join
   - Expected: result.status equals `ok`
   - Expected: result.diagnostic_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    "symbol=unused;section=.text;offset=500;size=40",
    "symbol=rare;section=.text;offset=300;size=64",
    "symbol=dispatch;section=.text;offset=64;size=80",
    "symbol=parse;section=.text;offset=160;size=96"
].join("\n")
val profile = [
    "header;schema=sprof-v1;module=demo;workload=smoke",
    "function;key=c:rare:entry;count=2",
    "function;key=c:dispatch:entry;count=8",
    "function;key=c:unused:entry;count=0",
    "function;key=c:parse:entry;count=6"
].join("\n")

val result = profile_layout_build_manifest(manifest, profile, 4096, 8192, 500, 2)

expect(result.status).to_equal("ok")
expect(result.diagnostic_count).to_equal(0)
expect(result.manifest_text).to_contain("simple-executable-layout-manifest-v1")
expect(result.manifest_text).to_contain("hot\t.text\tdispatch\t64\t4096\t80")
expect(result.manifest_text).to_contain("hot\t.text\tparse\t160\t4176\t96")
expect(result.manifest_text).to_contain("cold\t.text\trare\t300\t8192\t64")
expect(result.manifest_text).to_contain("cold\t.text\tunused\t500\t8256\t40")
```

</details>

#### should build native symbol order and C section map artifacts

1. ] join
2. ] join
   - Expected: order.status equals `ok`
   - Expected: order.manifest_text equals `dispatch\nparse\nrare\n`
   - Expected: c_map.status equals `ok`
   - Expected: unsupported.status equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    "symbol=rare;section=.text;offset=300;size=64",
    "symbol=dispatch;section=.text;offset=64;size=80",
    "symbol=parse;section=.text;offset=160;size=96"
].join("\n")
val profile = [
    "header;schema=sprof-v1;module=demo;workload=smoke",
    "function;key=c:rare:entry;count=0",
    "function;key=c:dispatch:entry;count=8",
    "function;key=c:parse:entry;count=6"
].join("\n")

val order = profile_layout_build_artifact(manifest, profile, "native-symbol-order", 4096, 8192, 500, 2)
expect(order.status).to_equal("ok")
expect(order.manifest_text).to_equal("dispatch\nparse\nrare\n")

val c_map = profile_layout_build_artifact(manifest, profile, "simple-c-section-map", 4096, 8192, 500, 2)
expect(c_map.status).to_equal("ok")
expect(c_map.manifest_text).to_contain("simple-c-layout-section-map-v1")
expect(c_map.manifest_text).to_contain("SIMPLE_LAYOUT_SECTION_dispatch")
expect(c_map.manifest_text).to_contain(".text.simple.hot.0.dispatch")

val unsupported = profile_layout_build_artifact(manifest, profile, "elf", 4096, 8192, 500, 2)
expect(unsupported.status).to_equal("invalid")
expect(unsupported.diagnostics).to_contain("unsupported_artifact_format:elf")
```

</details>

#### should produce checked native layout evidence from sprof through mapped C and measured runtime

1. ] join
2. ] join
3. "static int dispatch
4. "int parse
5. "  return dispatch
6. "int rare
7. ] join
   - Expected: evidence.status equals `ok`
   - Expected: evidence.diagnostic_count equals `0`
   - Expected: evidence.applied_count equals `3`
   - Expected: evidence.speedup_pct equals `20`
   - Expected: evidence.size_delta_bytes equals `-96`
   - Expected: evidence.regression is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    "symbol=rare;section=.text;offset=300;size=64",
    "symbol=dispatch;section=.text;offset=64;size=80",
    "symbol=parse;section=.text;offset=160;size=96"
].join("\n")
val profile = [
    "header;schema=sprof-v1;module=demo;workload=smoke",
    "function;key=c:rare:entry;count=0",
    "function;key=c:dispatch:entry;count=8",
    "function;key=c:parse:entry;count=6"
].join("\n")
val generated_c = [
    "static int dispatch(void) {",
    "  return 7;",
    "}",
    "int parse(void) {",
    "  return dispatch();",
    "}",
    "int rare(void) {",
    "  return 0;",
    "}"
].join("\n")

val evidence = profile_layout_native_evidence_report(
    manifest,
    profile,
    generated_c,
    "0000000000001640 t _ZL8dispatchv\n0000000000001650 t _ZL5parsev\n0000000000001660 t _ZL4rarev\n",
    0,
    100,
    80,
    4096,
    4000,
    4096,
    8192,
    500,
    2
)

expect(evidence.status).to_equal("ok")
expect(evidence.diagnostic_count).to_equal(0)
expect(evidence.applied_count).to_equal(3)
expect(evidence.speedup_pct).to_equal(20)
expect(evidence.size_delta_bytes).to_equal(-96)
expect(evidence.regression).to_equal(false)
expect(evidence.manifest_text).to_contain("hot\t.text\tdispatch")
expect(evidence.section_map_text).to_contain("SIMPLE_LAYOUT_SECTION_dispatch")
expect(evidence.mapped_c_source).to_contain("SIMPLE_LAYOUT_SECTION_dispatch static int dispatch(void) {")
```

</details>

#### should reject native layout evidence without measured runtime or mapped symbols

1. "int other
   - Expected: evidence.status equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = profile_layout_native_evidence_report(
    "symbol=dispatch;section=.text;offset=64;size=80",
    "function;key=c:dispatch:entry;count=8",
    "int other(void) {\n  return 1;\n}",
    "",
    0,
    0,
    70,
    4096,
    4000,
    4096,
    8192,
    500,
    2
)

expect(evidence.status).to_equal("invalid")
expect(evidence.diagnostics).to_contain("missing_baseline_runtime")
expect(evidence.diagnostics).to_contain("native_symbol_order_not_applied")
expect(evidence.diagnostics).to_contain("unused_section_map_entry:dispatch")
expect(evidence.diagnostics).to_contain("layout_section_map_not_applied")
```

</details>

#### should reject empty executable metadata and missing profile functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_manifest = profile_layout_build_manifest("", "function;key=c:main:entry;count=1", 4096, 8192, 500, 2)
expect(empty_manifest.status).to_equal("invalid")
expect(empty_manifest.diagnostics[0]).to_equal("empty_executable_manifest")

val missing_profile = profile_layout_build_manifest("symbol=main;section=.text;offset=0;size=32", "", 4096, 8192, 500, 2)
expect(missing_profile.status).to_equal("invalid")
expect(missing_profile.diagnostics[0]).to_equal("empty_function_profile")
```

</details>

#### should write an end-to-end layout manifest from a reloadable sprof profile

1. ] join
2. ] join
   - Expected: result.status equals `ok`
   - Expected: rt_file_exists(out_path) is true
   - Expected: order_result.status equals `ok`
   - Expected: rt_file_read_text(order_path) equals `parse\ndispatch\nrare\n`
   - Expected: c_map_result.status equals `ok`
3. rt file delete
4. rt file delete
5. rt file delete
6. rt file delete
7. rt file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/tmp/simple_profile_layout_e2e_{rt_getpid()}"
val profile_path = base + ".sprof"
val manifest_path = base + ".layout"
val out_path = base + ".optimized-layout"
val order_path = base + ".order"
val c_map_path = base + ".layout.h"
rt_file_write_text(profile_path, [
    "header;schema=sprof-v1;module=native-demo;workload=smoke",
    "function;key=c:dispatch:entry;count=1",
    "function;key=c:parse:entry;count=9",
    "function;key=c:rare:entry;count=0"
].join("\n"))
rt_file_write_text(manifest_path, [
    "symbol=rare;section=.text;offset=300;size=64",
    "symbol=dispatch;section=.text;offset=64;size=80",
    "symbol=parse;section=.text;offset=160;size=96"
].join("\n"))

val result = profile_layout_write_manifest_file(manifest_path, profile_path, out_path, 4096, 8192, 500, 2)
val output = rt_file_read_text(out_path)

expect(result.status).to_equal("ok")
expect(rt_file_exists(out_path)).to_equal(true)
expect(output).to_contain("simple-executable-layout-manifest-v1")
expect(output).to_contain("hot\t.text\tparse\t160\t4096\t96")
expect(output).to_contain("cold\t.text\tdispatch\t64\t8192\t80")
expect(output).to_contain("cold\t.text\trare\t300\t8272\t64")

val order_result = profile_layout_write_artifact_file(manifest_path, profile_path, order_path, "native-symbol-order", 4096, 8192, 500, 2)
val c_map_result = profile_layout_write_artifact_file(manifest_path, profile_path, c_map_path, "simple-c-section-map", 4096, 8192, 500, 2)

expect(order_result.status).to_equal("ok")
expect(rt_file_read_text(order_path)).to_equal("parse\ndispatch\nrare\n")
expect(c_map_result.status).to_equal("ok")
expect(rt_file_read_text(c_map_path)).to_contain("SIMPLE_LAYOUT_SECTION_parse")

rt_file_delete(profile_path)
rt_file_delete(manifest_path)
rt_file_delete(out_path)
rt_file_delete(order_path)
rt_file_delete(c_map_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/optimize/feature/profile_layout_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Profile Layout CLI Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
