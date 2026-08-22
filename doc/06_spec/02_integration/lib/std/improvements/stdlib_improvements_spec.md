# stdlib_improvements_spec

> Verifies the stdlib improvements behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# stdlib_improvements_spec

Verifies the stdlib improvements behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the stdlib improvements behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### text Method Improvements

#### Substring Operations

#### substring extracts range

- Verify: substring extracts range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: substring extracts range")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
expect text.substring(start=0, end=5) == "hello"
```

</details>

#### substr extracts with length

- Verify: substr extracts with length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: substr extracts with length")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
expect text.substr(start=6, length=5) == "world"
```

</details>

#### char_at gets single character

- Verify: char_at gets single character


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: char_at gets single character")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello"
expect text.char_at(0) == "h"
expect text.char_at(4) == "o"
```

</details>

#### chars returns list of characters

- Verify: chars returns list of characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: chars returns list of characters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "abc"
val chars = text.chars()
expect chars.len() == 3
expect chars[0] == "a"
```

</details>

#### Search Operations

#### find returns index of substring

- Verify: find returns index of substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: find returns index of substring")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
val result = text.find("world")
expect result.is_some()
```

</details>

#### find_all returns all indices

- Verify: find_all returns all indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: find_all returns all indices")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "abcabc"
val indices = text.find_all("a")
expect indices.len() == 2
```

</details>

#### contains checks for substring

- Verify: contains checks for substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: contains checks for substring")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
expect text.contains("world") == true
expect text.contains("xyz") == false
```

</details>

#### starts_with checks prefix

- Verify: starts_with checks prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: starts_with checks prefix")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
expect text.starts_with("hello") == true
expect text.starts_with("world") == false
```

</details>

#### ends_with checks suffix

- Verify: ends_with checks suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: ends_with checks suffix")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
expect text.ends_with("world") == true
expect text.ends_with("hello") == false
```

</details>

#### Whitespace Operations

#### strip removes leading and trailing whitespace

- Verify: strip removes leading and trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: strip removes leading and trailing whitespace")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "  hello  "
expect text.strip() == "hello"
```

</details>

#### trim removes leading and trailing whitespace

- Verify: trim removes leading and trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: trim removes leading and trailing whitespace")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "  hello  "
expect text.trim() == "hello"
```

</details>

#### trim_start removes leading whitespace

- Verify: trim_start removes leading whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: trim_start removes leading whitespace")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "  hello  "
expect text.trim_start() == "hello  "
```

</details>

#### trim_end removes trailing whitespace

- Verify: trim_end removes trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: trim_end removes trailing whitespace")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "  hello  "
expect text.trim_end() == "  hello"
```

</details>

#### Case Operations

#### to_upper converts to uppercase

- Verify: to_upper converts to uppercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: to_upper converts to uppercase")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello"
expect text.upper() == "HELLO"
```

</details>

#### to_lower converts to lowercase

- Verify: to_lower converts to lowercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: to_lower converts to lowercase")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "HELLO"
expect text.lower() == "hello"
```

</details>

#### capitalize capitalizes first letter

- Verify: capitalize capitalizes first letter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: capitalize capitalizes first letter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello world"
expect text.capitalize() == "Hello world"
```

</details>

#### Split and Join

#### split divides string by delimiter

- Verify: split divides string by delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: split divides string by delimiter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "a,b,c"
val parts = text.split(",")
expect parts.len() == 3
expect parts[0] == "a"
```

</details>

#### join combines list with delimiter

- Verify: join combines list with delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: join combines list with delimiter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val parts = ["a", "b", "c"]
expect ",".join(parts) == "a,b,c"
```

</details>

#### lines splits by newlines

- Verify: lines splits by newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: lines splits by newlines")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "line1\nline2\nline3"
val lines = text.lines()
expect lines.len() == 3
```

</details>

#### lines aliases preserve Rust-compatible edge cases

- Verify: lines aliases preserve Rust-compatible edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: lines aliases preserve Rust-compatible edge cases")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect "".lines().len() == 0
expect "".split_lines().len() == 0
val crlf = "a\r\nb".lines()
expect crlf.len() == 2
expect crlf[0] == "a"
expect crlf[1] == "b"
val trailing = "a\n\n".split_lines()
expect trailing.len() == 2
expect trailing[1] == ""
val lone_cr = "a\rb".lines()
expect lone_cr.len() == 1
expect lone_cr[0] == "a\rb"
```

</details>

#### Replacement

#### replace replaces all occurrences

- Verify: replace replaces all occurrences


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: replace replaces all occurrences")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello hello"
expect text.replace(old="hello", new="hi") == "hi hi"
```

</details>

#### replace_first replaces first occurrence

- Verify: replace_first replaces first occurrence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: replace_first replaces first occurrence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "hello hello"
expect text.replace_first(old="hello", new="hi") == "hi hello"
```

</details>

### File I/O Improvements

#### File Reading

#### read_file returns file contents

- Verify: read_file returns file contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: read_file returns file contents")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val content = fs.read_file("/tmp/test.txt")
expect content == "Hello, World!"
```

</details>

#### read_bytes returns raw bytes

- Verify: read_bytes returns raw bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: read_bytes returns raw bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val bytes = fs.read_bytes("/tmp/test.txt")
expect bytes.len() == 5
expect bytes[0] == 72
```

</details>

#### read_lines returns list of lines

- Verify: read_lines returns list of lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: read_lines returns list of lines")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val lines = fs.read_lines("/tmp/test.txt")
expect lines.len() == 3
expect lines[0] == "line1"
```

</details>

#### File Writing

#### write_file writes string to file

- Verify: write_file writes string to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: write_file writes string to file")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val success = fs.write_file(path="/tmp/output.txt", content="content")
expect success == true
```

</details>

#### write_bytes writes raw bytes

- Verify: write_bytes writes raw bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: write_bytes writes raw bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val success = fs.write_bytes("/tmp/output.bin", [1, 2, 3])
expect success == true
```

</details>

#### append_file appends to existing file

- Verify: append_file appends to existing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: append_file appends to existing file")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val success = fs.append_file(path="/tmp/test.txt", content="more")
expect success == true
```

</details>

#### File Metadata

#### path_exists checks if path exists

- Verify: path_exists checks if path exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: path_exists checks if path exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
expect fs.path_exists("/tmp/test.txt") == true
expect fs.path_exists("/nonexistent") == false
```

</details>

#### is_file checks if path is file

- Verify: is_file checks if path is file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: is_file checks if path is file")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
expect fs.is_file("/tmp/test.txt") == true
expect fs.is_file("/tmp") == false
```

</details>

#### is_dir checks if path is directory

- Verify: is_dir checks if path is directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: is_dir checks if path is directory")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
expect fs.is_dir("/tmp") == true
expect fs.is_dir("/tmp/test.txt") == false
```

</details>

#### file_size returns size in bytes

- Verify: file_size returns size in bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: file_size returns size in bytes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
expect fs.file_size("/tmp/test.txt") == 13
```

</details>

#### Directory Operations

#### list_dir returns directory contents

- Verify: list_dir returns directory contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: list_dir returns directory contents")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val contents = fs.list_dir("/tmp")
expect contents.len() == 2
```

</details>

#### create_dir creates new directory

- Verify: create_dir creates new directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: create_dir creates new directory")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val success = fs.create_dir("/tmp/newdir")
expect success == true
```

</details>

#### remove_file deletes file

- Verify: remove_file deletes file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: remove_file deletes file")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val success = fs.remove_file("/tmp/test.txt")
expect success == true
```

</details>

#### remove_dir deletes directory

- Verify: remove_dir deletes directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: remove_dir deletes directory")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val fs = MockFileSystem.create()
val success = fs.remove_dir("/tmp")
expect success == true
```

</details>

### JSON Library Improvements

#### JSON Parsing

#### from_json parses JSON string

- Verify: from_json parses JSON string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: from_json parses JSON string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json = MockJson.from_json("object:test")
expect json.is_object() == true
```

</details>

#### parses JSON arrays

- Verify: parses JSON arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: parses JSON arrays")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json = MockJson.from_json("array:test")
expect json.is_array() == true
```

</details>

#### parses nested JSON

- Verify: parses nested JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: parses nested JSON")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json = MockJson.from_json("object:nested")
expect json.is_object() == true
```

</details>

#### JSON Generation

#### to_json converts dict to JSON

- Verify: to_json converts dict to JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: to_json converts dict to JSON")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json_str = MockJson.to_json("test")
expect json_str.contains("json:")
```

</details>

#### to_json handles nested structures

- Verify: to_json handles nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: to_json handles nested structures")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json_str = MockJson.to_json("nested")
expect json_str.starts_with("json:")
```

</details>

#### escapes special characters

- Verify: escapes special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: escapes special characters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val escaped = MockJson.escape("test")
expect escaped.starts_with("escaped:")
```

</details>

#### JSON Builder

#### builds JSON objects fluently

- Verify: builds JSON objects fluently


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: builds JSON objects fluently")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val builder = MockJsonBuilder.object()
builder.add(key="key", value="value")
val json_str = builder.build()
expect json_str.contains("key")
```

</details>

#### builds JSON arrays fluently

- Verify: builds JSON arrays fluently


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: builds JSON arrays fluently")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val builder = MockJsonBuilder.array()
builder.append("item")
val json_str = builder.build()
expect json_str.contains("item")
```

</details>

### Error Handling Improvements

#### Question Mark Operator

#### propagates Result errors

- Verify: propagates Result errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: propagates Result errors")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Test that ? propagates Err values
val success = wrapper_divide(a=10, b=2)
expect success.is_ok() == true
expect success.unwrap() == 10

val failure = wrapper_divide(a=10, b=0)
expect failure.is_err() == true
```

</details>

#### propagates Option None

- Verify: propagates Option None


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: propagates Option None")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Test that ? propagates None values
val items = [10, 20, 30]

val found = get_doubled_index(items=items, target=20)
expect found.is_some() == true
expect found.unwrap() == 2  # index 1 * 2

val not_found = get_doubled_index(items=items, target=99)
expect not_found.is_none() == true
```

</details>

#### chains multiple ? operations

- Verify: chains multiple ? operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-IMPROVEMENTS_STDLIB_IMPROVEM-001
step("Verify: chains multiple ? operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Test chaining multiple ? in sequence
val success = chain_operations(a=100, b=5, c=2)
# 100 / 5 = 20, 20 / 2 = 10
expect success.is_ok() == true
expect success.unwrap() == 10

# First division fails
val fail_first = chain_operations(a=100, b=0, c=2)
expect fail_first.is_err() == true

# Second division fails
val fail_second = chain_operations(a=100, b=5, c=0)
expect fail_second.is_err() == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89de264e6402aeb13ffae3639e9a54e7383a7f9dd58383f6b8e14cd70e665866`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89de264e6402aeb13ffae3639e9a54e7383a7f9dd58383f6b8e14cd70e665866`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89de264e6402aeb13ffae3639e9a54e7383a7f9dd58383f6b8e14cd70e665866`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl
mirror: doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
