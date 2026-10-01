# Mcp T32 Impl Fixes Specification

> Tests covering T32 MCP Implementation Fixes (F5).

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
#### get field retrieves stored value

- get field retrieves stored value
   - Expected: result equals `0x08001234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get field retrieves stored value")
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
val result = fs_get(store, "s1", "register.pc")
expect(result).to_equal("0x08001234")
```

</details>

#### get unknown field returns empty string

- get unknown field returns empty string
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get unknown field returns empty string")
val store = fs_new()
val result = fs_get(store, "s1", "nonexistent")
expect(result).to_equal("")
```

</details>

#### update existing field changes value

- update existing field changes value
   - Expected: result equals `0x08001238`
   - Expected: fs_count(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update existing field changes value")
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
store = fs_set(store, "s1", "register.pc", "0x08001238")
val result = fs_get(store, "s1", "register.pc")
expect(result).to_equal("0x08001238")
expect(fs_count(store)).to_equal(1)
```

</details>

#### multiple fields stored independently

- multiple fields stored independently
   - Expected: fs_get(store, "s1", "register.pc") equals `0x08001234`
   - Expected: fs_get(store, "s1", "register.sp") equals `0x20001000`
   - Expected: fs_get(store, "s1", "register.lr") equals `0x08000100`
   - Expected: fs_count(store) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple fields stored independently")
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

- field key format uses session_id:field_key
   - Expected: compound equals `sess_42:register.pc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("field key format uses session_id:field_key")
val compound = fs_compound_key("sess_42", "register.pc")
expect(compound).to_equal("sess_42:register.pc")
```

</details>

#### get is O(1)-class with 100+ entries

- get is O(1)-class with 100+ entries
   - Expected: fs_get(store, "s1", "field_0") equals `val_0`
   - Expected: fs_get(store, "s1", "field_75") equals `val_75`
   - Expected: fs_get(store, "s1", "field_149") equals `val_149`
   - Expected: fs_count(store) equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get is O(1)-class with 100+ entries")
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

- delete field removes it
   - Expected: fs_get(store, "s1", "register.pc") equals ``
   - Expected: fs_get(store, "s1", "register.sp") equals `0x20001000`
   - Expected: fs_count(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delete field removes it")
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

- session-scoped isolation
   - Expected: fs_get(store, "session_A", "register.pc") equals `0xAAAAAAAA`
   - Expected: fs_get(store, "session_B", "register.pc") equals `0xBBBBBBBB`
   - Expected: fs_count(store) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session-scoped isolation")
var store = fs_new()
store = fs_set(store, "session_A", "register.pc", "0xAAAAAAAA")
store = fs_set(store, "session_B", "register.pc", "0xBBBBBBBB")
expect(fs_get(store, "session_A", "register.pc")).to_equal("0xAAAAAAAA")
expect(fs_get(store, "session_B", "register.pc")).to_equal("0xBBBBBBBB")
expect(fs_count(store)).to_equal(2)
```

</details>

#### common field aliases resolve correctly for pc

- common field aliases resolve correctly for pc
   - Expected: resolve_field_alias("pc") equals `register.pc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common field aliases resolve correctly for pc")
expect(resolve_field_alias("pc")).to_equal("register.pc")
```

</details>

#### common field aliases resolve correctly for sp

- common field aliases resolve correctly for sp
   - Expected: resolve_field_alias("sp") equals `register.sp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common field aliases resolve correctly for sp")
expect(resolve_field_alias("sp")).to_equal("register.sp")
```

</details>

#### common field aliases resolve correctly for lr

- common field aliases resolve correctly for lr
   - Expected: resolve_field_alias("lr") equals `register.lr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common field aliases resolve correctly for lr")
expect(resolve_field_alias("lr")).to_equal("register.lr")
```

</details>

#### unknown alias passes through unchanged

- unknown alias passes through unchanged
   - Expected: resolve_field_alias("custom_field") equals `custom_field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown alias passes through unchanged")
expect(resolve_field_alias("custom_field")).to_equal("custom_field")
```

</details>

#### alias resolution is case-insensitive

- alias resolution is case-insensitive
   - Expected: resolve_field_alias("PC") equals `register.pc`
   - Expected: resolve_field_alias("Sp") equals `register.sp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alias resolution is case-insensitive")
expect(resolve_field_alias("PC")).to_equal("register.pc")
expect(resolve_field_alias("Sp")).to_equal("register.sp")
```

</details>

#### delete nonexistent field is no-op

- delete nonexistent field is no-op
   - Expected: fs_count(store) equals `1`
   - Expected: fs_get(store, "s1", "register.pc") equals `0x08001234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delete nonexistent field is no-op")
var store = fs_new()
store = fs_set(store, "s1", "register.pc", "0x08001234")
store = fs_delete(store, "s1", "register.sp")
expect(fs_count(store)).to_equal(1)
expect(fs_get(store, "s1", "register.pc")).to_equal("0x08001234")
```

</details>

#### connection retry (REQ-F5-002)

#### first attempt succeeds - connected

- first attempt succeeds - connected
   - Expected: result.connected is true
   - Expected: result.total_attempts equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first attempt succeeds - connected")
val result = retry_connect("localhost", 20000, 0)
expect(result.connected).to_equal(true)
expect(result.total_attempts).to_equal(1)
expect(result.session_id).to_start_with("session_")
```

</details>

#### first fails second succeeds - connected after retry

- first fails second succeeds - connected after retry
   - Expected: result.connected is true
   - Expected: result.total_attempts equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first fails second succeeds - connected after retry")
val result = retry_connect("localhost", 20000, 1)
expect(result.connected).to_equal(true)
expect(result.total_attempts).to_equal(2)
```

</details>

#### all 3 attempts fail - error with attempt count

- all 3 attempts fail - error with attempt count
   - Expected: result.connected is false
   - Expected: result.total_attempts equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 3 attempts fail - error with attempt count")
val result = retry_connect("localhost", 20000, 3)
expect(result.connected).to_equal(false)
expect(result.total_attempts).to_equal(3)
expect(result.error_msg).to_contain("3 attempts")
```

</details>

#### exponential backoff timing 1s 2s 4s

- exponential backoff timing 1s 2s 4s
   - Expected: b1 equals `1000`
   - Expected: b2 equals `2000`
   - Expected: b3 equals `4000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exponential backoff timing 1s 2s 4s")
val b1 = retry_backoff_ms(1)
val b2 = retry_backoff_ms(2)
val b3 = retry_backoff_ms(3)
expect(b1).to_equal(1000)
expect(b2).to_equal(2000)
expect(b3).to_equal(4000)
```

</details>

#### retry count in error message

- retry count in error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retry count in error message")
val result = retry_connect("10.0.0.1", 20000, 5)
expect(result.error_msg).to_contain("3 attempts")
expect(result.error_msg).to_start_with("T4200")
```

</details>

#### backend attempts field in result

- backend attempts field in result
   - Expected: result.connected is true
   - Expected: result.total_attempts equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("backend attempts field in result")
val result = retry_connect("localhost", 20000, 2)
expect(result.connected).to_equal(true)
expect(result.total_attempts).to_equal(3)
```

</details>

#### connection error includes host:port

- connection error includes host:port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("connection error includes host:port")
val result = retry_connect("192.168.1.100", 20001, 10)
expect(result.error_msg).to_contain("192.168.1.100:20001")
```

</details>

#### retry does not duplicate sessions

- retry does not duplicate sessions
   - Expected: result.connected is true
   - Expected: result.session_id equals `session_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retry does not duplicate sessions")
val result = retry_connect("localhost", 20000, 1)
expect(result.connected).to_equal(true)
# Only one session_id, no duplicates
expect(result.session_id).to_equal("session_2")
```

</details>

#### attempt log records all tries

- attempt log records all tries
   - Expected: attempts.len() equals `3`
   - Expected: attempts[0].succeeded is false
   - Expected: attempts[1].succeeded is false
   - Expected: attempts[2].succeeded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attempt log records all tries")
val attempts = retry_connect_with_log("localhost", 20000, 2)
expect(attempts.len()).to_equal(3)
expect(attempts[0].succeeded).to_equal(false)
expect(attempts[1].succeeded).to_equal(false)
expect(attempts[2].succeeded).to_equal(true)
```

</details>

#### attempt log error messages include host:port

- attempt log error messages include host:port
   - Expected: attempts[0].succeeded is false
   - Expected: attempts[1].succeeded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attempt log error messages include host:port")
val attempts = retry_connect_with_log("myhost", 20005, 1)
expect(attempts[0].error_msg).to_contain("myhost:20005")
expect(attempts[0].succeeded).to_equal(false)
expect(attempts[1].succeeded).to_equal(true)
```

</details>

#### SDN catalog error handling (REQ-F5-003)

#### valid SDN parses correctly

- valid SDN parses correctly
   - Expected: result.has_error is false
   - Expected: result.entries.len() equals `2`
   - Expected: result.entries[0].name equals `flash_stm32`
   - Expected: result.entries[0].description equals `STM32 flash programming`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("valid SDN parses correctly")
val content = "flash_stm32: STM32 flash programming\nreset_target: Reset and halt target"
val result = sdn_parse_catalog(content, "catalog.sdn")
expect(result.has_error).to_equal(false)
expect(result.entries.len()).to_equal(2)
expect(result.entries[0].name).to_equal("flash_stm32")
expect(result.entries[0].description).to_equal("STM32 flash programming")
```

</details>

#### missing SDN file returns empty catalog with error

- missing SDN file returns empty catalog with error
   - Expected: result.entries.len() equals `0`
   - Expected: result.has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing SDN file returns empty catalog with error")
val result = sdn_parse_missing_file("/etc/t32/catalog.sdn")
expect(result.entries.len()).to_equal(0)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("not found")
```

</details>

#### malformed SDN returns empty catalog with error

- malformed SDN returns empty catalog with error
   - Expected: result.entries.len() equals `0`
   - Expected: result.has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("malformed SDN returns empty catalog with error")
val content = "this has no colon separator"
val result = sdn_parse_catalog(content, "bad.sdn")
expect(result.entries.len()).to_equal(0)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("Malformed")
```

</details>

#### error message includes file path

- error message includes file path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error message includes file path")
val result = sdn_parse_missing_file("/opt/trace32/catalog.sdn")
expect(result.error_msg).to_contain("/opt/trace32/catalog.sdn")
```

</details>

#### no silent fallback to hardcoded entries

- no silent fallback to hardcoded entries
   - Expected: result.entries.len() equals `0`
   - Expected: result.has_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no silent fallback to hardcoded entries")
# Empty file must return empty entries, not hardcoded defaults
val result = sdn_parse_catalog("", "empty.sdn")
expect(result.entries.len()).to_equal(0)
expect(result.has_error).to_equal(true)
expect(result.error_msg).to_contain("empty")
```

</details>

#### partial SDN parse returns valid entries plus error for invalid

- partial SDN parse returns valid entries plus error for invalid
   - Expected: result.entries.len() equals `2`
   - Expected: result.has_error is true
   - Expected: result.entries[0].name equals `good_entry`
   - Expected: result.entries[1].name equals `another_good`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("partial SDN parse returns valid entries plus error for invalid")
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

- comments are skipped
   - Expected: result.has_error is false
   - Expected: result.entries.len() equals `1`
   - Expected: result.entries[0].name equals `flash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comments are skipped")
val content = "# This is a comment\nflash: Flash tool"
val result = sdn_parse_catalog(content, "commented.sdn")
expect(result.has_error).to_equal(false)
expect(result.entries.len()).to_equal(1)
expect(result.entries[0].name).to_equal("flash")
```

</details>

#### blank lines are skipped

- blank lines are skipped
   - Expected: result.has_error is false
   - Expected: result.entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blank lines are skipped")
val content = "entry_a: First\n\n\nentry_b: Second"
val result = sdn_parse_catalog(content, "blanks.sdn")
expect(result.has_error).to_equal(false)
expect(result.entries.len()).to_equal(2)
```

</details>

#### timeout parameters (REQ-F5-004)

#### default connect_timeout_ms is 5000

- default connect_timeout_ms is 5000
   - Expected: config.connect_timeout_ms equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default connect_timeout_ms is 5000")
val config = default_timeout_config()
expect(config.connect_timeout_ms).to_equal(5000)
```

</details>

#### default command_timeout_ms is 5000

- default command_timeout_ms is 5000
   - Expected: config.command_timeout_ms equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default command_timeout_ms is 5000")
val config = default_timeout_config()
expect(config.command_timeout_ms).to_equal(5000)
```

</details>

#### default practice_wait_timeout_ms is 30000

- default practice_wait_timeout_ms is 30000
   - Expected: config.practice_wait_timeout_ms equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default practice_wait_timeout_ms is 30000")
val config = default_timeout_config()
expect(config.practice_wait_timeout_ms).to_equal(30000)
```

</details>

#### custom timeout_ms overrides default

- custom timeout_ms overrides default
   - Expected: resolved equals `8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom timeout_ms overrides default")
val resolved = resolve_timeout(8000, 5000)
expect(resolved).to_equal(8000)
```

</details>

#### zero timeout_ms means no timeout

- zero timeout_ms means no timeout
   - Expected: resolved equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero timeout_ms means no timeout")
val resolved = resolve_timeout(0, 5000)
expect(resolved).to_equal(0)
```

</details>

#### negative timeout_ms rejected

- negative timeout_ms rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative timeout_ms rejected")
val err = validate_timeout_ms(-1)
expect(err).to_start_with("T4300")
expect(err).to_contain("-1")
```

</details>

#### effective timeout uses connect default for session_open

- effective timeout uses connect default for session_open
   - Expected: timeout equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("effective timeout uses connect default for session_open")
val params = ToolCallParams(tool_name: "t32_session_open", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(5000)
```

</details>

#### effective timeout uses practice default for cmm_run

- effective timeout uses practice default for cmm_run
   - Expected: timeout equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("effective timeout uses practice default for cmm_run")
val params = ToolCallParams(tool_name: "t32_cmm_run", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(30000)
```

</details>

#### effective timeout uses command default for cmd_run

- effective timeout uses command default for cmd_run
   - Expected: timeout equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("effective timeout uses command default for cmd_run")
val params = ToolCallParams(tool_name: "t32_cmd_run", timeout_ms: -1)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(5000)
```

</details>

#### custom timeout overrides tool-specific default

- custom timeout overrides tool-specific default
   - Expected: timeout equals `15000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom timeout overrides tool-specific default")
val params = ToolCallParams(tool_name: "t32_cmm_run", timeout_ms: 15000)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(15000)
```

</details>

#### zero timeout disables timeout for any tool

- zero timeout disables timeout for any tool
   - Expected: timeout equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero timeout disables timeout for any tool")
val params = ToolCallParams(tool_name: "t32_cmd_run", timeout_ms: 0)
val defaults = default_timeout_config()
val timeout = effective_timeout(params, defaults)
expect(timeout).to_equal(0)
```

</details>

#### positive timeout_ms validation passes

- positive timeout_ms validation passes
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive timeout_ms validation passes")
val err = validate_timeout_ms(5000)
expect(err).to_equal("")
```

</details>

#### zero timeout_ms validation passes

- zero timeout_ms validation passes
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero timeout_ms validation passes")
val err = validate_timeout_ms(0)
expect(err).to_equal("")
```

</details>

#### unknown tool falls back to command_timeout default

- unknown tool falls back to command_timeout default
   - Expected: timeout equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown tool falls back to command_timeout default")
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
| Source | `test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 MCP Implementation Fixes (F5).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-F5-001`
- `REQ-F5-002`
- `REQ-F5-003`
- `REQ-F5-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62edafd11b1ba17d69b647dce4d59ea72c0472332b043a56b64fbd022a3dc013`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62edafd11b1ba17d69b647dce4d59ea72c0472332b043a56b64fbd022a3dc013`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62edafd11b1ba17d69b647dce4d59ea72c0472332b043a56b64fbd022a3dc013`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=90 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 32 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl:289:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'set field stores value' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl:301:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get field retrieves stored value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl:309:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get unknown field returns empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_impl_fixes_spec.spl:316:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'update existing field changes value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
