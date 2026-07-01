# native_profile_counter_spec

> System coverage for native profile counter planning, instrumentation, and extraction.

<!-- sdn-diagram:id=native_profile_counter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_profile_counter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_profile_counter_spec -> std
native_profile_counter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_profile_counter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_profile_counter_spec

System coverage for native profile counter planning, instrumentation, and extraction.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compile/feature/native_profile_counter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System coverage for native profile counter planning, instrumentation, and extraction.

## Scenarios

### Native Profile Counter Contract

### counter ABI

#### should expose function block edge and call path counter kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = native_profile_counter_kinds()
expect(kinds).to_contain("function_entry")
expect(kinds).to_contain("basic_block")
expect(kinds).to_contain("edge")
expect(kinds).to_contain("call_path")
```

</details>

#### should enable counters only for profile builds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_profile_counters_enabled(true)).to_equal(true)
expect(native_profile_counters_enabled(false)).to_equal(false)
expect(native_profile_counter_enabled(true, "function_entry")).to_equal(true)
expect(native_profile_counter_enabled(false, "function_entry")).to_equal(false)
```

</details>

#### should reject unknown counter kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_profile_counter_enabled(true, "debug_printf")).to_equal(false)
```

</details>

### slot records

#### should create stable counter slot records

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = native_profile_counter_slot(3, "basic_block", "mir:main:bb3", 0)
expect(slot.slot_index).to_equal(3)
expect(slot.counter_kind).to_equal("basic_block")
expect(slot.stable_key).to_equal("mir:main:bb3")
expect(slot.initial_value).to_equal(0)
```

</details>

#### should validate counter slot records

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = native_profile_counter_slot(0, "edge", "mir:main:edge0", 7)
val bad_index = native_profile_counter_slot(-1, "edge", "mir:main:edge0", 0)
val bad_kind = native_profile_counter_slot(1, "debug_printf", "mir:main:edge0", 0)
val bad_key = native_profile_counter_slot(1, "edge", "", 0)
val bad_initial = native_profile_counter_slot(1, "edge", "mir:main:edge0", -1)
expect(native_profile_counter_slot_valid(valid)).to_equal(true)
expect(native_profile_counter_slot_valid(bad_index)).to_equal(false)
expect(native_profile_counter_slot_valid(bad_kind)).to_equal(false)
expect(native_profile_counter_slot_valid(bad_key)).to_equal(false)
expect(native_profile_counter_slot_valid(bad_initial)).to_equal(false)
```

</details>

#### should validate complete slot tables

1. native profile counter slot
2. native profile counter slot
3. native profile counter slot
4. native profile counter slot
   - Expected: native_profile_counter_slots_valid(valid_slots) is true
   - Expected: native_profile_counter_slots_valid(invalid_slots) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
    native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 0)
]
val invalid_slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
    native_profile_counter_slot(1, "trace", "mir:main:trace", 0)
]
expect(native_profile_counter_slots_valid(valid_slots)).to_equal(true)
expect(native_profile_counter_slots_valid(invalid_slots)).to_equal(false)
```

</details>

### emission planning

#### should compute stable section labels and counter symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = native_profile_counter_slot(4, "call_path", "mir:main:callee|leaf", 3)
expect(native_profile_counter_default_section_name()).to_equal(".simple.profile.counters")
expect(native_profile_counter_section_label(".simple.profile.counters")).to_equal("simple_profile_counter_section__simple_profile_counters")
expect(native_profile_counter_section_label("")).to_equal("simple_profile_counter_section__simple_profile_counters")
expect(native_profile_counter_symbol(slot)).to_equal("__simple_profile_counter_4_call_path")
```

</details>

#### should serialize counter records with escaped stable keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = native_profile_counter_slot(4, "call_path", "mir:main:callee|leaf", 3)
val line = native_profile_counter_serialization_line(".simple.profile.counters", slot)
expect(line).to_equal("counter|section=simple_profile_counter_section__simple_profile_counters|slot=4|kind=call_path|key=mir:main:callee\\pleaf|initial=3|symbol=__simple_profile_counter_4_call_path")

val record = native_profile_counter_emission_record(".simple.profile.counters", slot)
expect(record.slot_index).to_equal(4)
expect(record.counter_kind).to_equal("call_path")
expect(record.section_label).to_equal("simple_profile_counter_section__simple_profile_counters")
expect(record.counter_symbol).to_equal("__simple_profile_counter_4_call_path")
expect(record.serialization_line).to_equal(line)
```

</details>

#### should build deterministic valid emission records

1. native profile counter slot
2. native profile counter slot
3. native profile counter slot
4. native profile counter slot
   - Expected: sorted.len() equals `3`
   - Expected: sorted[0].stable_key equals `mir:main:entry`
   - Expected: sorted[1].stable_key equals `mir:main:bb0`
   - Expected: sorted[2].stable_key equals `mir:main:edge1`
   - Expected: records.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(2, "edge", "mir:main:edge1", 0),
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
    native_profile_counter_slot(1, "trace", "mir:main:trace", 0),
    native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 7)
]
val sorted = native_profile_counter_sorted_valid_slots(slots)
expect(sorted.len()).to_equal(3)
expect(sorted[0].stable_key).to_equal("mir:main:entry")
expect(sorted[1].stable_key).to_equal("mir:main:bb0")
expect(sorted[2].stable_key).to_equal("mir:main:edge1")

val records = native_profile_counter_emission_records(".simple.profile.counters", slots)
expect(records.len()).to_equal(3)
expect(records[0].serialization_line).to_contain("slot=0|kind=function_entry")
expect(records[1].serialization_line).to_contain("slot=1|kind=basic_block")
expect(records[2].serialization_line).to_contain("slot=2|kind=edge")
```

</details>

#### should produce stable profile section serialization lines

1. native profile counter slot
2. native profile counter slot
   - Expected: lines.len() equals `3`
   - Expected: lines[0] equals `section|label=simple_profile_counter_section__simple_profile_counters|name=.s... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 0),
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0)
]
val lines = native_profile_counter_section_serialization_lines(".simple.profile.counters", slots)
expect(lines.len()).to_equal(3)
expect(lines[0]).to_equal("section|label=simple_profile_counter_section__simple_profile_counters|name=.simple.profile.counters|records=2")
expect(lines[1]).to_contain("slot=0|kind=function_entry")
expect(lines[2]).to_contain("slot=1|kind=basic_block")
```

</details>

#### should emit concrete C counter declarations and increment statements

1. [valid, native profile counter slot
   - Expected: declarations.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = native_profile_counter_slot(2, "edge", "mir:main:edge1", 7)
val invalid = native_profile_counter_slot(3, "trace", "mir:main:trace", 0)
expect(native_profile_counter_c_declaration(".simple.profile.counters", valid)).to_equal("static unsigned long long __simple_profile_counter_2_edge __attribute__((section(\".simple.profile.counters\"), used)) = 7;")
expect(native_profile_counter_c_declaration(".simple.profile.counters", invalid)).to_equal("")
expect(native_profile_counter_increment_statement(true, valid)).to_equal("__simple_profile_counter_2_edge += 1;")
expect(native_profile_counter_increment_statement(false, valid)).to_equal("")

val declarations = native_profile_counter_c_declarations(
    ".simple.profile.counters",
    [valid, native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0)]
)
expect(declarations.len()).to_equal(2)
expect(declarations[0]).to_contain("__simple_profile_counter_0_function_entry")
expect(declarations[1]).to_contain("__simple_profile_counter_2_edge")
```

</details>

### profile section summary

#### should summarize profile sections with slot validity counts

1. native profile counter slot
2. native profile counter slot
3. native profile counter slot
   - Expected: summary.section_name equals `.simple.profile.counters`
   - Expected: summary.enabled is true
   - Expected: summary.slot_count equals `3`
   - Expected: summary.valid_slot_count equals `2`
   - Expected: summary.invalid_slot_count equals `1`
   - Expected: summary.cold_path_policy equals `emit_counter_increment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
    native_profile_counter_slot(1, "basic_block", "", 0),
    native_profile_counter_slot(2, "edge", "mir:main:edge", 2)
]
val summary = native_profile_section_summary(".simple.profile.counters", true, slots)
expect(summary.section_name).to_equal(".simple.profile.counters")
expect(summary.enabled).to_equal(true)
expect(summary.slot_count).to_equal(3)
expect(summary.valid_slot_count).to_equal(2)
expect(summary.invalid_slot_count).to_equal(1)
expect(summary.cold_path_policy).to_equal("emit_counter_increment")
```

</details>

#### should summarize disabled profile sections with cold path policy

1. native profile counter slot
   - Expected: summary.enabled is false
   - Expected: summary.cold_path_policy equals `native_profile_disabled_counter_cold_path_policy()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0)
]
val summary = native_profile_section_summary(".simple.profile.counters", false, slots)
expect(summary.enabled).to_equal(false)
expect(summary.cold_path_policy).to_equal(native_profile_disabled_counter_cold_path_policy())
```

</details>

### stable identity

#### should require native and interpreter counters to share stable keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_profile_counter_identity_matches("mir:main:abc", "mir:main:abc")).to_equal(true)
expect(native_profile_counter_identity_matches("mir:main:abc", "native:main:abc")).to_equal(false)
expect(native_profile_counter_identity_matches("", "")).to_equal(false)
```

</details>

### disabled-counter cold path policy

#### should compile out disabled counter increments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_profile_disabled_counter_cold_path_policy()).to_equal("compile_out_counter_increment")
expect(native_profile_counter_cold_path_policy(false, "function_entry")).to_equal("compile_out_counter_increment")
expect(native_profile_counter_cold_path_policy(true, "unknown")).to_equal("compile_out_counter_increment")
expect(native_profile_counter_cold_path_policy(true, "function_entry")).to_equal("emit_counter_increment")
```

</details>

#### should select emitted and compiled-out increment operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0)
val invalid = native_profile_counter_slot(1, "unknown", "mir:main:unknown", 0)
val emitted = native_profile_counter_increment_operation(true, valid)
val disabled = native_profile_counter_increment_operation(false, valid)
val compiled_out_invalid = native_profile_counter_increment_operation(true, invalid)

expect(emitted.emitted).to_equal(true)
expect(emitted.operation).to_equal("emit_counter_increment")
expect(emitted.reason).to_equal("profile_build_enabled")
expect(disabled.emitted).to_equal(false)
expect(disabled.operation).to_equal("compile_out_counter_increment")
expect(disabled.reason).to_equal("profile_build_disabled")
expect(compiled_out_invalid.emitted).to_equal(false)
expect(compiled_out_invalid.reason).to_equal("invalid_counter_slot")

val operations = native_profile_counter_increment_operations(true, [valid, invalid])
expect(operations.len()).to_equal(2)
expect(operations[0].emitted).to_equal(true)
expect(operations[1].emitted).to_equal(false)
```

</details>

### call path policy

#### should bound call path counters for profile builds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_depth = native_profile_call_path_counter_max_depth()
expect(max_depth).to_be_greater_than(0)
expect(native_profile_call_path_counter_allowed(true, 0)).to_equal(true)
expect(native_profile_call_path_counter_allowed(true, max_depth)).to_equal(true)
expect(native_profile_call_path_counter_allowed(true, max_depth + 1)).to_equal(false)
```

</details>

#### should reject call path counters outside profile builds and negative depths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_profile_call_path_counter_allowed(false, 1)).to_equal(false)
expect(native_profile_call_path_counter_allowed(true, -1)).to_equal(false)
```

</details>

### native C counter artifact

#### should generate deterministic prelude declarations and metadata comments from slots

1. native profile counter slot
2. native profile counter slot
3. native profile counter slot
   - Expected: prelude.counter_symbol equals `native_profile_counter_array_symbol()`
   - Expected: prelude.metadata_symbol equals `native_profile_counter_metadata_symbol()`
   - Expected: prelude.slot_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
    native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 7),
    native_profile_counter_slot(2, "edge", "mir:main:bb0->bb1", 2)
]
val prelude = native_profile_counter_c_prelude(slots)
expect(prelude.counter_symbol).to_equal(native_profile_counter_array_symbol())
expect(prelude.metadata_symbol).to_equal(native_profile_counter_metadata_symbol())
expect(prelude.slot_count).to_equal(3)
expect(prelude.c_source).to_contain("/* simple-profile-counter-prelude-v1 */")
expect(prelude.c_source).to_contain("#include <stdint.h>")
expect(prelude.c_source).to_contain("#include <stdio.h>")
expect(prelude.c_source).to_contain("#include <stdlib.h>")
expect(prelude.c_source).to_contain("static uint64_t __simple_profile_counters[3] = {0, 7, 2};")
expect(prelude.c_source).to_contain("static const size_t __simple_profile_counters_count = 3u;")
expect(prelude.c_source).to_contain("static const char * const __simple_profile_counter_metadata[3] = {0};")
expect(prelude.c_source).to_contain("SIMPLE_PROFILE_COUNTER_SNAPSHOT")
expect(prelude.c_source).to_contain("simple-profile-counter-snapshot-v1\\n")
expect(prelude.c_source).to_contain("count|slot=%zu|value=%llu\\n")
expect(prelude.c_source).to_contain("atexit(__simple_profile_write_counter_snapshot);")
expect(prelude.c_source).to_contain("/* simple-profile-counter slot=0 kind=function_entry key=mir:main:entry initial=0 */")
expect(prelude.c_source).to_contain("/* simple-profile-counter slot=1 kind=basic_block key=mir:main:bb0 initial=7 */")
expect(prelude.c_source).to_contain("/* simple-profile-counter slot=2 kind=edge key=mir:main:bb0->bb1 initial=2 */")
```

</details>

#### should sanitize metadata comment values without changing stable slot order

1. native profile counter slot
2. native profile counter slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:*/entry", 0),
    native_profile_counter_slot(1, "call_path", "mir:main\ncallee", 0)
]
val prelude = native_profile_counter_c_prelude(slots)
expect(prelude.c_source).to_contain("key=mir:main:* /entry")
expect(prelude.c_source).to_contain("key=mir:main callee")
```

</details>

### increment insertion records

#### should generate per-slot increment records with placement labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = native_profile_counter_slot(4, "call_path", "mir:main:call:callee", 0)
val record = native_profile_counter_increment_record(slot, "main", "bb2", "bb2->bb3", "main/callee")
expect(record.slot_index).to_equal(4)
expect(record.counter_kind).to_equal("call_path")
expect(record.stable_key).to_equal("mir:main:call:callee")
expect(record.function_label).to_equal("main")
expect(record.block_label).to_equal("bb2")
expect(record.edge_label).to_equal("bb2->bb3")
expect(record.call_path_label).to_equal("main/callee")
expect(record.placement_label).to_equal("function=main|block=bb2|edge=bb2->bb3|call_path=main/callee")
expect(record.c_statement).to_equal("__simple_profile_counters[4] += 1u;")
```

</details>

#### should generate one deterministic increment record per slot

1. native profile counter slot
2. native profile counter slot
   - Expected: records.len() equals `2`
   - Expected: records[0].slot_index equals `0`
   - Expected: records[0].c_statement equals `__simple_profile_counters[0] += 1u;`
   - Expected: records[1].slot_index equals `1`
   - Expected: records[1].placement_label equals `function=main|block=bb0|edge=|call_path=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
    native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 0)
]
val records = native_profile_counter_increment_records(slots, "main", "bb0", "", "")
expect(records.len()).to_equal(2)
expect(records[0].slot_index).to_equal(0)
expect(records[0].c_statement).to_equal("__simple_profile_counters[0] += 1u;")
expect(records[1].slot_index).to_equal(1)
expect(records[1].placement_label).to_equal("function=main|block=bb0|edge=|call_path=")
```

</details>

### native C source instrumentation

#### should derive function entry slots from generated C source

1. "int main
   - Expected: slots.len() equals `2`
   - Expected: slots[0].stable_key equals `c:main:entry`
   - Expected: slots[1].stable_key equals `c:helper:entry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = native_profile_counter_function_entry_slots_from_c_source(
    "int main(void) {\n  return 0;\n}\nstatic RtVal helper(void) {\n  return rt_nil();\n}\nif (ready) {\n}\n"
)
expect(slots.len()).to_equal(2)
expect(slots[0].stable_key).to_equal("c:main:entry")
expect(slots[1].stable_key).to_equal("c:helper:entry")
```

</details>

#### should derive function block edge and call path slots from generated C source

1. "int main
2. "  helper
3. "void helper
4. ] join
5. native profile counter all c instrumentation kinds
   - Expected: slots.len() equals `7`
   - Expected: slots[0].counter_kind equals `function_entry`
   - Expected: slots[0].stable_key equals `c:main:entry`
   - Expected: slots[1].counter_kind equals `basic_block`
   - Expected: slots[1].stable_key equals `c:main:bb0`
   - Expected: slots[2].counter_kind equals `call_path`
   - Expected: slots[2].stable_key equals `c:main:call:helper:0`
   - Expected: slots[3].counter_kind equals `edge`
   - Expected: slots[3].stable_key equals `c:main:return->main:exit0`
   - Expected: slots[4].stable_key equals `c:helper:entry`
   - Expected: slots[5].stable_key equals `c:helper:bb0`
   - Expected: slots[6].stable_key equals `c:helper:return->helper:exit0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = native_profile_counter_c_slots_from_source(
    [
        "int main(void) {",
        "  helper();",
        "  return 0;",
        "}",
        "void helper(void) {",
        "  return;",
        "}"
    ].join("\n"),
    native_profile_counter_all_c_instrumentation_kinds()
)
expect(slots.len()).to_equal(7)
expect(slots[0].counter_kind).to_equal("function_entry")
expect(slots[0].stable_key).to_equal("c:main:entry")
expect(slots[1].counter_kind).to_equal("basic_block")
expect(slots[1].stable_key).to_equal("c:main:bb0")
expect(slots[2].counter_kind).to_equal("call_path")
expect(slots[2].stable_key).to_equal("c:main:call:helper:0")
expect(slots[3].counter_kind).to_equal("edge")
expect(slots[3].stable_key).to_equal("c:main:return->main:exit0")
expect(slots[4].stable_key).to_equal("c:helper:entry")
expect(slots[5].stable_key).to_equal("c:helper:bb0")
expect(slots[6].stable_key).to_equal("c:helper:return->helper:exit0")
```

</details>

#### should inject counter prelude and function entry increments into C source

1. "int main
   - Expected: instrumented.enabled is true
   - Expected: instrumented.slot_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instrumented = native_profile_counter_instrument_c_source(
    "int main(void) {\n  helper();\n  return 0;\n}\nvoid helper(void) {\n}\n",
    true
)
expect(instrumented.enabled).to_equal(true)
expect(instrumented.slot_count).to_equal(6)
expect(instrumented.c_source).to_contain("/* simple-profile-counter-prelude-v1 */")
expect(instrumented.c_source).to_contain("static uint64_t __simple_profile_counters[6] = {0, 0, 0, 0, 0, 0};")
expect(instrumented.c_source).to_contain("__simple_profile_write_counter_snapshot")
expect(instrumented.c_source).to_contain("__simple_profile_counters[0] += 1u;")
expect(instrumented.c_source).to_contain("__simple_profile_counters[1] += 1u;")
expect(instrumented.c_source).to_contain("__simple_profile_counters[2] += 1u;")
expect(instrumented.c_source).to_contain("  helper();")
expect(instrumented.c_source).to_contain("__simple_profile_counters[3] += 1u;")
expect(instrumented.c_source).to_contain("  return 0;")
expect(instrumented.metadata_lines).to_contain("counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=c:main:entry|initial=0|symbol=__simple_profile_counter_0_function_entry")
expect(instrumented.metadata_lines).to_contain("counter|section=simple_profile_counter_section__simple_profile_counters|slot=1|kind=basic_block|key=c:main:bb0|initial=0|symbol=__simple_profile_counter_1_basic_block")
expect(instrumented.metadata_lines).to_contain("counter|section=simple_profile_counter_section__simple_profile_counters|slot=2|kind=call_path|key=c:main:call:helper:0|initial=0|symbol=__simple_profile_counter_2_call_path")
expect(instrumented.metadata_lines).to_contain("counter|section=simple_profile_counter_section__simple_profile_counters|slot=3|kind=edge|key=c:main:return->main:exit0|initial=0|symbol=__simple_profile_counter_3_edge")
```

</details>

#### should leave C source unchanged when profile counters are disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "int main(void) {\n  return 0;\n}\n"
val instrumented = native_profile_counter_instrument_c_source(source, false)
expect(instrumented.enabled).to_equal(false)
expect(instrumented.slot_count).to_equal(0)
expect(instrumented.c_source).to_equal(source)
expect(instrumented.c_source.contains("SIMPLE_PROFILE_COUNTER_SNAPSHOT")).to_equal(false)
```

</details>

#### should fail the build audit if counters leak into non-profile builds

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "int main(void) {\n  return 0;\n}\n"
val clean = native_profile_counter_build_audit(source, false)
expect(clean.allowed).to_equal(true)
expect(clean.reason).to_equal("non_profile_build_clean")

val instrumented = native_profile_counter_instrument_c_source(source, true)
val profile_audit = native_profile_counter_build_audit(instrumented.c_source, true)
expect(profile_audit.allowed).to_equal(true)
expect(profile_audit.counter_symbols_found).to_equal(true)
expect(profile_audit.counter_increments_found).to_equal(true)
expect(profile_audit.metadata_found).to_equal(true)

val leaked = native_profile_counter_build_audit(instrumented.c_source, false)
expect(leaked.allowed).to_equal(false)
expect(leaked.reason).to_equal("counter_artifacts_in_non_profile_build")
```

</details>

#### should wire the native compile path audit so normal builds cannot contain counters

1. var profile opts = default compile opts
   - Expected: profile_allowed.allowed is true
   - Expected: profile_allowed.reason equals `profile_build_may_contain_counters`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "int main(void) {\n  return 0;\n}\n"
val clean_opts = default_compile_opts()
val clean = llvm_direct_native_counter_artifact_audit(source, clean_opts)
expect(clean.allowed).to_equal(true)
expect(clean.reason).to_equal("non_profile_build_clean")

val profile_source = native_profile_counter_instrument_c_source(source, true).c_source
val leaked = llvm_direct_native_counter_artifact_audit(profile_source, clean_opts)
expect(leaked.allowed).to_equal(false)
expect(leaked.reason).to_equal("counter_artifacts_in_non_profile_build")

var profile_opts = default_compile_opts()
profile_opts.simple_profile_counters = true
val profile_allowed = llvm_direct_native_counter_artifact_audit(profile_source, profile_opts)
expect(profile_allowed.allowed).to_equal(true)
expect(profile_allowed.reason).to_equal("profile_build_may_contain_counters")
```

</details>

### runtime sprof extraction

#### should map metadata and final counter values to sprof-compatible records

1. native profile counter slot
2. native profile counter slot
3. native profile counter slot
4. native profile counter slot
   - Expected: extraction.record_count equals `4`
   - Expected: extraction.line_count equals `4`
   - Expected: extraction.diagnostic_count equals `0`
   - Expected: extraction.lines[0] equals `function;key=mir:main:entry;count=11`
   - Expected: extraction.lines[1] equals `block;function=main;key=mir:main:bb0;count=7`
   - Expected: extraction.lines[2] equals `edge;from=mir:main:bb0;to=bb1;count=5`
   - Expected: extraction.lines[3] equals `edge;from=mir:main:call:helper;to=call_path;count=3`
   - Expected: extraction.records[0].record_kind equals `function`
   - Expected: extraction.records[1].record_kind equals `block`
   - Expected: extraction.records[2].record_kind equals `edge`
   - Expected: extraction.records[3].counter_kind equals `call_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata_lines = native_profile_counter_section_serialization_lines(
    ".simple.profile.counters",
    [
        native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
        native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 0),
        native_profile_counter_slot(2, "edge", "mir:main:bb0->bb1", 0),
        native_profile_counter_slot(3, "call_path", "mir:main:call:helper", 0)
    ]
)
val extraction = native_profile_counter_extract_sprof_records(metadata_lines, [11, 7, 5, 3])
expect(extraction.record_count).to_equal(4)
expect(extraction.line_count).to_equal(4)
expect(extraction.diagnostic_count).to_equal(0)
expect(extraction.lines[0]).to_equal("function;key=mir:main:entry;count=11")
expect(extraction.lines[1]).to_equal("block;function=main;key=mir:main:bb0;count=7")
expect(extraction.lines[2]).to_equal("edge;from=mir:main:bb0;to=bb1;count=5")
expect(extraction.lines[3]).to_equal("edge;from=mir:main:call:helper;to=call_path;count=3")
expect(extraction.records[0].record_kind).to_equal("function")
expect(extraction.records[1].record_kind).to_equal("block")
expect(extraction.records[2].record_kind).to_equal("edge")
expect(extraction.records[3].counter_kind).to_equal("call_path")
```

</details>

#### should expose direct sprof line extraction for profile writers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata_lines = [
    "section|label=simple_profile_counter_section__simple_profile_counters|name=.simple.profile.counters|records=1",
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=0|kind=function_entry|key=c:main:entry|initial=0|symbol=__simple_profile_counter_0_function_entry"
]
val lines = native_profile_counter_extract_sprof_lines(metadata_lines, [9])
expect(lines.len()).to_equal(1)
expect(lines[0]).to_equal("function;key=c:main:entry;count=9")
```

</details>

#### should expose durable sidecar metadata path for native compile outputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_profile_counter_metadata_path("/tmp/demo")).to_equal("/tmp/demo.simple-profile-counters")
expect(native_profile_counter_metadata_path("build/app.bin")).to_equal("build/app.bin.simple-profile-counters")
```

</details>

#### should unescape native metadata keys while preserving sprof token safety

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = native_profile_counter_sprof_record_from_metadata_line(
    "counter|section=simple_profile_counter_section__simple_profile_counters|slot=4|kind=call_path|key=mir:main:callee\\pleaf|initial=0|symbol=__simple_profile_counter_4_call_path",
    6
)
expect(record.slot_index).to_equal(4)
expect(record.stable_key).to_equal("mir:main:callee|leaf")
expect(record.line).to_equal("edge;from=mir:main:callee|leaf;to=call_path;count=6")
```

</details>

#### should diagnose missing and mismatched runtime counter values

1. native profile counter slot
2. native profile counter slot
   - Expected: extraction.record_count equals `1`
   - Expected: extraction.lines[0] equals `function;key=mir:main:entry;count=8`
   - Expected: missing.record_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata_lines = native_profile_counter_section_serialization_lines(
    ".simple.profile.counters",
    [
        native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
        native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 4)
    ]
)
val extraction = native_profile_counter_extract_sprof_records(metadata_lines, [8, 2, 99])
expect(extraction.record_count).to_equal(1)
expect(extraction.lines[0]).to_equal("function;key=mir:main:entry;count=8")
expect(extraction.diagnostics).to_contain("counter_below_initial:1")
expect(extraction.diagnostics).to_contain("count_without_metadata:2")

val missing = native_profile_counter_extract_sprof_records(metadata_lines, [8])
expect(missing.record_count).to_equal(1)
expect(missing.diagnostics).to_contain("missing_count:1")
```

</details>

#### should parse runtime counter snapshots into ordered final counts

1. native profile counter snapshot header
2. native profile counter snapshot line
3. native profile counter snapshot line
   - Expected: snapshot.status equals `valid`
   - Expected: snapshot.counter_count equals `2`
   - Expected: snapshot.counters[0] equals `11`
   - Expected: snapshot.counters[1] equals `7`
   - Expected: snapshot.diagnostic_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = native_profile_counter_runtime_snapshot_from_text(
    native_profile_counter_snapshot_header() + "\n" +
    native_profile_counter_snapshot_line(0, 11) + "\n" +
    native_profile_counter_snapshot_line(1, 7) + "\n"
)
expect(snapshot.status).to_equal("valid")
expect(snapshot.counter_count).to_equal(2)
expect(snapshot.counters[0]).to_equal(11)
expect(snapshot.counters[1]).to_equal(7)
expect(snapshot.diagnostic_count).to_equal(0)
```

</details>

#### should reject incomplete or malformed runtime counter snapshots

1. native profile counter snapshot header
2. native profile counter snapshot line
   - Expected: snapshot.status equals `invalid`
3. native profile counter snapshot line


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = native_profile_counter_runtime_snapshot_from_text(
    native_profile_counter_snapshot_header() + "\n" +
    native_profile_counter_snapshot_line(1, 7) + "\n" +
    "count|slot=1|value=8\n" +
    "noise\n"
)
expect(snapshot.status).to_equal("invalid")
expect(snapshot.diagnostics).to_contain("missing_snapshot_slot:0")
expect(snapshot.diagnostics).to_contain("duplicate_snapshot_slot:1")
expect(snapshot.diagnostics).to_contain("invalid_snapshot_line:3")

val missing_header = native_profile_counter_runtime_snapshot_from_text(
    native_profile_counter_snapshot_line(0, 1)
)
expect(missing_header.diagnostics).to_contain("missing_snapshot_header")
```

</details>

#### should create a write-gated sprof import plan from runtime snapshots

1. native profile counter slot
2. native profile counter slot
3. native profile counter snapshot line
4. native profile counter snapshot line
   - Expected: plan.status equals `ready`
   - Expected: plan.write_allowed is true
   - Expected: plan.record_count equals `2`
   - Expected: plan.lines[0] equals `function;key=mir:main:entry;count=11`
   - Expected: plan.lines[1] equals `block;function=main;key=mir:main:bb0;count=7`
   - Expected: no_output.status equals `missing_output_path`
   - Expected: no_output.write_allowed is false
   - Expected: bad_snapshot.status equals `invalid_snapshot`
   - Expected: bad_snapshot.write_allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata_lines = native_profile_counter_section_serialization_lines(
    ".simple.profile.counters",
    [
        native_profile_counter_slot(0, "function_entry", "mir:main:entry", 0),
        native_profile_counter_slot(1, "basic_block", "mir:main:bb0", 0)
    ]
)
val snapshot_text = native_profile_counter_snapshot_header() + "\n" +
    native_profile_counter_snapshot_line(0, 11) + "\n" +
    native_profile_counter_snapshot_line(1, 7) + "\n"
val plan = native_profile_counter_sprof_import_plan("build/app.sprof", metadata_lines, snapshot_text)
expect(plan.status).to_equal("ready")
expect(plan.write_allowed).to_equal(true)
expect(plan.record_count).to_equal(2)
expect(plan.lines[0]).to_equal("function;key=mir:main:entry;count=11")
expect(plan.lines[1]).to_equal("block;function=main;key=mir:main:bb0;count=7")

val no_output = native_profile_counter_sprof_import_plan("", metadata_lines, snapshot_text)
expect(no_output.status).to_equal("missing_output_path")
expect(no_output.write_allowed).to_equal(false)
expect(no_output.diagnostics).to_contain("missing_output_path")

val bad_snapshot = native_profile_counter_sprof_import_plan("build/app.sprof", metadata_lines, "count|slot=0|value=1")
expect(bad_snapshot.status).to_equal("invalid_snapshot")
expect(bad_snapshot.write_allowed).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
