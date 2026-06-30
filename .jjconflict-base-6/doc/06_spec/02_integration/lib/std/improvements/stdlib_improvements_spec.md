# Stdlib Improvements Specification

> 1. expect text substring

<!-- sdn-diagram:id=stdlib_improvements_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stdlib_improvements_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stdlib_improvements_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stdlib_improvements_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stdlib Improvements Specification

## Scenarios

### text Method Improvements

#### Substring Operations

#### substring extracts range

1. expect text substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.substring(start=0, end=5) == "hello"
```

</details>

#### substr extracts with length

1. expect text substr


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.substr(start=6, length=5) == "world"
```

</details>

#### char_at gets single character

1. expect text char at
2. expect text char at


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
expect text.char_at(0) == "h"
expect text.char_at(4) == "o"
```

</details>

#### chars returns list of characters

1. expect chars len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "abc"
val chars = text.chars()
expect chars.len() == 3
expect chars[0] == "a"
```

</details>

#### Search Operations

#### find returns index of substring

1. expect result is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
val result = text.find("world")
expect result.is_some()
```

</details>

#### find_all returns all indices

1. expect indices len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "abcabc"
val indices = text.find_all("a")
expect indices.len() == 2
```

</details>

#### contains checks for substring

1. expect text contains
2. expect text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.contains("world") == true
expect text.contains("xyz") == false
```

</details>

#### starts_with checks prefix

1. expect text starts with
2. expect text starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.starts_with("hello") == true
expect text.starts_with("world") == false
```

</details>

#### ends_with checks suffix

1. expect text ends with
2. expect text ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.ends_with("world") == true
expect text.ends_with("hello") == false
```

</details>

#### Whitespace Operations

#### strip removes leading and trailing whitespace

1. expect text strip


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "  hello  "
expect text.strip() == "hello"
```

</details>

#### trim removes leading and trailing whitespace

1. expect text trim


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "  hello  "
expect text.trim() == "hello"
```

</details>

#### trim_start removes leading whitespace

1. expect text trim start


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "  hello  "
expect text.trim_start() == "hello  "
```

</details>

#### trim_end removes trailing whitespace

1. expect text trim end


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "  hello  "
expect text.trim_end() == "  hello"
```

</details>

#### Case Operations

#### to_upper converts to uppercase

1. expect text upper


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
expect text.upper() == "HELLO"
```

</details>

#### to_lower converts to lowercase

1. expect text lower


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "HELLO"
expect text.lower() == "hello"
```

</details>

#### capitalize capitalizes first letter

1. expect text capitalize


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.capitalize() == "Hello world"
```

</details>

#### Split and Join

#### split divides string by delimiter

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "a,b,c"
val parts = text.split(",")
expect parts.len() == 3
expect parts[0] == "a"
```

</details>

#### join combines list with delimiter

1. expect "," join


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = ["a", "b", "c"]
expect ",".join(parts) == "a,b,c"
```

</details>

#### lines splits by newlines

1. expect lines len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "line1\nline2\nline3"
val lines = text.lines()
expect lines.len() == 3
```

</details>

#### Replacement

#### replace replaces all occurrences

1. expect text replace


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello hello"
expect text.replace(old="hello", new="hi") == "hi hi"
```

</details>

#### replace_first replaces first occurrence

1. expect text replace first


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello hello"
expect text.replace_first(old="hello", new="hi") == "hi hello"
```

</details>

### File I/O Improvements

#### File Reading

#### read_file returns file contents

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val content = fs.read_file("/tmp/test.txt")
expect content == "Hello, World!"
```

</details>

#### read_bytes returns raw bytes

1. expect bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val bytes = fs.read_bytes("/tmp/test.txt")
expect bytes.len() == 5
expect bytes[0] == 72
```

</details>

#### read_lines returns list of lines

1. expect lines len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val lines = fs.read_lines("/tmp/test.txt")
expect lines.len() == 3
expect lines[0] == "line1"
```

</details>

#### File Writing

#### write_file writes string to file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val success = fs.write_file(path="/tmp/output.txt", content="content")
expect success == true
```

</details>

#### write_bytes writes raw bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val success = fs.write_bytes("/tmp/output.bin", [1, 2, 3])
expect success == true
```

</details>

#### append_file appends to existing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val success = fs.append_file(path="/tmp/test.txt", content="more")
expect success == true
```

</details>

#### File Metadata

#### path_exists checks if path exists

1. expect fs path exists
2. expect fs path exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
expect fs.path_exists("/tmp/test.txt") == true
expect fs.path_exists("/nonexistent") == false
```

</details>

#### is_file checks if path is file

1. expect fs is file
2. expect fs is file


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
expect fs.is_file("/tmp/test.txt") == true
expect fs.is_file("/tmp") == false
```

</details>

#### is_dir checks if path is directory

1. expect fs is dir
2. expect fs is dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
expect fs.is_dir("/tmp") == true
expect fs.is_dir("/tmp/test.txt") == false
```

</details>

#### file_size returns size in bytes

1. expect fs file size


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
expect fs.file_size("/tmp/test.txt") == 13
```

</details>

#### Directory Operations

#### list_dir returns directory contents

1. expect contents len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val contents = fs.list_dir("/tmp")
expect contents.len() == 2
```

</details>

#### create_dir creates new directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val success = fs.create_dir("/tmp/newdir")
expect success == true
```

</details>

#### remove_file deletes file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val success = fs.remove_file("/tmp/test.txt")
expect success == true
```

</details>

#### remove_dir deletes directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.create()
val success = fs.remove_dir("/tmp")
expect success == true
```

</details>

### JSON Library Improvements

#### JSON Parsing

#### from_json parses JSON string

1. expect json is object


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = MockJson.from_json("object:test")
expect json.is_object() == true
```

</details>

#### parses JSON arrays

1. expect json is array


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = MockJson.from_json("array:test")
expect json.is_array() == true
```

</details>

#### parses nested JSON

1. expect json is object


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = MockJson.from_json("object:nested")
expect json.is_object() == true
```

</details>

#### JSON Generation

#### to_json converts dict to JSON

1. expect json str contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json_str = MockJson.to_json("test")
expect json_str.contains("json:")
```

</details>

#### to_json handles nested structures

1. expect json str starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json_str = MockJson.to_json("nested")
expect json_str.starts_with("json:")
```

</details>

#### escapes special characters

1. expect escaped starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = MockJson.escape("test")
expect escaped.starts_with("escaped:")
```

</details>

#### JSON Builder

#### builds JSON objects fluently

1. builder add
2. expect json str contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = MockJsonBuilder.object()
builder.add(key="key", value="value")
val json_str = builder.build()
expect json_str.contains("key")
```

</details>

#### builds JSON arrays fluently

1. builder append
2. expect json str contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = MockJsonBuilder.array()
builder.append("item")
val json_str = builder.build()
expect json_str.contains("item")
```

</details>

### Error Handling Improvements

#### Question Mark Operator

#### propagates Result errors

1. expect success is ok
2. expect success unwrap
3. expect failure is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that ? propagates Err values
val success = wrapper_divide(a=10, b=2)
expect success.is_ok() == true
expect success.unwrap() == 10

val failure = wrapper_divide(a=10, b=0)
expect failure.is_err() == true
```

</details>

#### propagates Option None

1. expect found is some
2. expect found unwrap
3. expect not found is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect success is ok
2. expect success unwrap
3. expect fail first is err
4. expect fail second is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- text Method Improvements
- File I/O Improvements
- JSON Library Improvements
- Error Handling Improvements

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
