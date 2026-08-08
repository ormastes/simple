# Mcp T32 Impl Fixes Specification

> 1. var store = fs new

<!-- sdn-diagram:id=mcp_t32_impl_fixes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_impl_fixes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_impl_fixes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_impl_fixes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Impl Fixes Specification

## Scenarios

### T32 MCP Implementation Fixes (F5)

#### dict-based field state (REQ-F5-001)

#### set field stores value

1. var store = fs new
2. store = fs set
   - Expected: fs_count(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
expect(fs_count(store)).to_equal(1)
```

</details>

#### get field retrieves stored value

1. var store = fs new
2. store = fs set
   - Expected: result equals `0x08001234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
val result = fs_get(store, "s1", "register.pc")
expect(result).to_equal("0x08001234")
```

</details>

#### get unknown field returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fs_new()
val result = fs_get(store, "s1", "nonexistent")
expect(result).to_equal("")
```

</details>

#### update existing field changes value

1. var store = fs new
2. store = fs set
3. store = fs set
   - Expected: result equals `0x08001238`
   - Expected: fs_count(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
store = fs_set(store, "s1", "register.pc", "0x08001238")
val result = fs_get(store, "s1", "register.pc")
expect(result).to_equal("0x08001238")
expect(fs_count(store)).to_equal(1)
```

</details>

#### multiple fields stored independently

1. var store = fs new
2. store = fs set
3. store = fs set
4. store = fs set
   - Expected: fs_get(store, "s1", "register.pc") equals `0x08001234`
   - Expected: fs_get(store, "s1", "register.sp") equals `0x20001000`
   - Expected: fs_get(store, "s1", "register.lr") equals `0x08000100`
   - Expected: fs_count(store) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
store = fs_set(store, "s1", "register.sp", "0x20001000")
store = fs_set(store, "s1", "register.lr", "0x08000100")
expect(fs_get(store, "s1", "register.pc")).to_equal("0x08001234")
expect(fs_get(store, "s1", "register.sp")).to_equal("0x20001000")
expect(fs_get(store, "s1", "register.lr")).to_equal("0x08000100")
expect(fs_count(store)).to_equal(3)
```

</details>

#### field key format uses session_id:field_key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compound = fs_compound_key("sess_42", "register.pc")
expect(compound).to_equal("sess_42:register.pc")
```

</details>

#### get is O(1)-class with 100+ entries

1. var store = fs new
2. store = fs set
   - Expected: fs_get(store, "s1", "field_0") equals `val_0`
   - Expected: fs_get(store, "s1", "field_75") equals `val_75`
   - Expected: fs_get(store, "s1", "field_149") equals `val_149`
   - Expected: fs_count(store) equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
var i = 0
while i < 150:
    store = fs_set(store, "s1", "field_" + str(i), "val_" + str(i))
    i = i + 1
# Verify first, middle, last entries are accessible
expect(fs_get(store, "s1", "field_0")).to_equal("val_0")
expect(fs_get(store, "s1", "field_75")).to_equal("val_75")
expect(fs_get(store, "s1", "field_149")).to_equal("val_149")
expect(fs_count(store)).to_equal(150)
```

</details>

#### delete field removes it

1. var store = fs new
2. store = fs set
3. store = fs set
4. store = fs delete
   - Expected: fs_get(store, "s1", "register.pc") equals ``
   - Expected: fs_get(store, "s1", "register.sp") equals `0x20001000`
   - Expected: fs_count(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
store = fs_set(store, "s1", "register.sp", "0x20001000")
store = fs_delete(store, "s1", "register.pc")
expect(fs_get(store, "s1", "register.pc")).to_equal("")
expect(fs_get(store, "s1", "register.sp")).to_equal("0x20001000")
expect(fs_count(store)).to_equal(1)
```

</details>

#### session-scoped isolation

1. var store = fs new
2. store = fs set
3. store = fs set
   - Expected: fs_get(store, "session_A", "register.pc") equals `0xAAAAAAAA`
   - Expected: fs_get(store, "session_B", "register.pc") equals `0xBBBBBBBB`
   - Expected: fs_count(store) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "session_A", "register.pc", "0xAAAAAAAA")
store = fs_set(store, "session_B", "register.pc", "0xBBBBBBBB")
expect(fs_get(store, "session_A", "register.pc")).to_equal("0xAAAAAAAA")
expect(fs_get(store, "session_B", "register.pc")).to_equal("0xBBBBBBBB")
expect(fs_count(store)).to_equal(2)
```

</details>

#### common field aliases resolve correctly for pc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_field_alias("pc")).to_equal("register.pc")
```

</details>

#### common field aliases resolve correctly for sp

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_field_alias("sp")).to_equal("register.sp")
```

</details>

#### common field aliases resolve correctly for lr

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_field_alias("lr")).to_equal("register.lr")
```

</details>

#### unknown alias passes through unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_field_alias("custom_field")).to_equal("custom_field")
```

</details>

#### alias resolution is case-insensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_field_alias("PC")).to_equal("register.pc")
expect(resolve_field_alias("Sp")).to_equal("register.sp")
```

</details>

#### delete nonexistent field is no-op

1. var store = fs new
2. store = fs set
3. store = fs delete
   - Expected: fs_count(store) equals `1`
   - Expected: fs_get(store, "s1", "register.pc") equals `0x08001234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
store = fs_delete(store, "s1", "register.sp")
expect(fs_count(store)).to_equal(1)
expect(fs_get(store, "s1", "register.pc")).to_equal("0x08001234")
```

</details>

#### connection retry (REQ-F5-002)

#### first attempt succeeds - connected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("localhost", 20000, 0)
expect(result.connected).to_equal(true)
expect(result.total_attempts).to_equal(1)
expect(result.session_id).to_start_with("session_")
```

</details>

#### first fails second succeeds - connected after retry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("localhost", 20000, 1)
expect(result.connected).to_equal(true)
expect(result.total_attempts).to_equal(2)
```

</details>

#### all 3 attempts fail - error with attempt count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("localhost", 20000, 3)
expect(result.connected).to_equal(false)
expect(result.total_attempts).to_equal(3)
expect(result.error_msg).to_contain("3 attempts")
```

</details>

#### exponential backoff timing 1s 2s 4s

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = retry_backoff_ms(1)
val b2 = retry_backoff_ms(2)
val b3 = retry_backoff_ms(3)
expect(b1).to_equal(1000)
expect(b2).to_equal(2000)
expect(b3).to_equal(4000)
```

</details>

#### retry count in error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("10.0.0.1", 20000, 5)
expect(result.error_msg).to_contain("3 attempts")
expect(result.error_msg).to_start_with("T4200")
```

</details>

#### backend attempts field in result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("localhost", 20000, 2)
expect(result.connected).to_equal(true)
expect(result.total_attempts).to_equal(3)
```

</details>

#### connection error includes host:port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("192.168.1.100", 20001, 10)
expect(result.error_msg).to_contain("192.168.1.100:20001")
```

</details>

#### retry does not duplicate sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = retry_connect("localhost", 20000, 1)
expect(result.connected).to_equal(true)
# Only one session_id, no duplicates
expect(result.session_id).to_equal("session_2")
```

</details>

#### attempt log records all tries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attempts = retry_connect_with_log("localhost", 20000, 2)
expect(attempts.len()).to_equal(3)
expect(attempts[0].succeeded).to_equal(false)
expect(attempts[1].succeeded).to_equal(false)
expect(attempts[2].succeeded).to_equal(true)
```

</details>

#### attempt log error messages include host:port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attempts = retry_connect_with_log("myhost", 20005, 1)
expect(attempts[0].error_msg).to_contain("myhost:20005")
expect(attempts[0].succeeded).to_equal(false)
expect(attempts[1].succeeded).to_equal(true)
```

</details>

#### SDN catalog error handling (REQ-F5-003)

#### valid SDN parses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "flash_stm32: STM32 flash programming\nreset_target: Reset and halt target"
val result = sdn_parse_catalog(content, "catalog.sdn")
expect(result.has_error).to_equal(false)
expect(result.entries.len()).to_equal(2)
expect(result.entries[0].name).to_equal("flash_stm32")
expect(result.entries[0].description).to_equal("STM32 flash programming")
```

</details>

#### missing SDN file returns empty catalog with error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sdn_parse_missing_file("/etc/t32/catalog.sdn")
expect(result.entries.len()).to_equal(0)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("not found")
```

</details>

#### malformed SDN returns empty catalog with error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "this has no colon separator"
val result = sdn_parse_catalog(content, "bad.sdn")
expect(result.entries.len()).to_equal(0)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("Malformed")
```

</details>

#### error message includes file path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sdn_parse_missing_file("/opt/trace32/catalog.sdn")
expect(result.error_msg).to_contain("/opt/trace32/catalog.sdn")
```

</details>

#### no silent fallback to hardcoded entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Empty file must return empty entries, not hardcoded defaults
val result = sdn_parse_catalog("", "empty.sdn")
expect(result.entries.len()).to_equal(0)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("empty")
```

</details>

#### partial SDN parse returns valid entries plus error for invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "good_entry: This is valid\nbad line without separator\nanother_good: Also valid"
val result = sdn_parse_catalog(content, "mixed.sdn")
expect(result.entries.len()).to_equal(2)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("Malformed")
expect(result.entries[0].name).to_equal("good_entry")
expect(result.entries[1].name).to_equal("another_good")
```

</details>

#### comments are skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# This is a comment\nflash: Flash tool"
val result = sdn_parse_catalog(content, "commented.sdn")
expect(result.has_error).to_equal(false)
expect(result.entries.len()).to_equal(1)
expect(result.entries[0].name).to_equal("flash")
```

</details>

#### blank lines are skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "entry_a: First\n\n\nentry_b: Second"
val result = sdn_parse_catalog(content, "blanks.sdn")
expect(result.has_error).to_equal(false)
expect(result.entries.len()).to_equal(2)
```

</details>

#### timeout parameters (REQ-F5-004)

#### default connect_timeout_ms is 5000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_timeout_config()
expect(config.connect_timeout_ms).to_equal(5000)
```

</details>

#### default command_timeout_ms is 5000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_timeout_config()
expect(config.command_timeout_ms).to_equal(5000)
```

</details>

#### default practice_wait_timeout_ms is 30000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_timeout_config()
expect(config.practice_wait_timeout_ms).to_equal(30000)
```

</details>

#### custom timeout_ms overrides default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = resolve_timeout(8000, 5000)
expect(resolved).to_equal(8000)
```

</details>

#### zero timeout_ms means no timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = resolve_timeout(0, 5000)
expect(resolved).to_equal(0)
```

</details>

#### negative timeout_ms rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = validate_timeout_ms(-1)
expect(err).to_start_with("T4300")
expect(err).to_contain("-1")
```

</details>

#### effective timeout uses connect default for session_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ToolCallParams(tool_name: "t32_session_open", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(5000)
```

</details>

#### effective timeout uses practice default for cmm_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ToolCallParams(tool_name: "t32_cmm_run", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(30000)
```

</details>

#### effective timeout uses command default for cmd_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ToolCallParams(tool_name: "t32_cmd_run", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(5000)
```

</details>

#### custom timeout overrides tool-specific default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ToolCallParams(tool_name: "t32_cmm_run", timeout_ms: 15000)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(15000)
```

</details>

#### zero timeout disables timeout for any tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ToolCallParams(tool_name: "t32_cmd_run", timeout_ms: 0)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(0)
```

</details>

#### positive timeout_ms validation passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = validate_timeout_ms(5000)
expect(err).to_equal("")
```

</details>

#### zero timeout_ms validation passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = validate_timeout_ms(0)
expect(err).to_equal("")
```

</details>

#### unknown tool falls back to command_timeout default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ToolCallParams(tool_name: "t32_some_new_tool", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(5000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP Implementation Fixes (F5)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
