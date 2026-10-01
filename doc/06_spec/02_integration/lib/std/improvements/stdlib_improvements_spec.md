# Stdlib Improvements Specification

> Tests covering text Method Improvements, File I/O Improvements, JSON Library Improvements, Error Handling Improvements.

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

- substring extracts range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("substring extracts range")
val text = "hello world"
expect text.substring(start=0, end=5) == "hello"
```

</details>

#### substr extracts with length

- substr extracts with length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.substr(start=6, length=5) == "world"
```

</details>

#### char_at gets single character

- char_at gets single character


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("char_at gets single character")
val text = "hello"
expect text.char_at(0) == "h"
expect text.char_at(4) == "o"
```

</details>

#### chars returns list of characters

- chars returns list of characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("chars returns list of characters")
val text = "abc"
val chars = text.chars()
expect chars.len() == 3
expect chars[0] == "a"
```

</details>

#### Search Operations

#### find returns index of substring

- find returns index of substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("find returns index of substring")
val text = "hello world"
val result = text.find("world")
expect result.is_some()
```

</details>

#### find_all returns all indices

- find_all returns all indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("find_all returns all indices")
val text = "abcabc"
val indices = text.find_all("a")
expect indices.len() == 2
```

</details>

#### contains checks for substring

- contains checks for substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("contains checks for substring")
val text = "hello world"
expect text.contains("world") == true
expect text.contains("xyz") == false
```

</details>

#### starts_with checks prefix

- starts_with checks prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("starts_with checks prefix")
val text = "hello world"
expect text.starts_with("hello") == true
expect text.starts_with("world") == false
```

</details>

#### ends_with checks suffix

- ends_with checks suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ends_with checks suffix")
val text = "hello world"
expect text.ends_with("world") == true
expect text.ends_with("hello") == false
```

</details>

#### Whitespace Operations

#### strip removes leading and trailing whitespace

- strip removes leading and trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strip removes leading and trailing whitespace")
val text = "  hello  "
expect text.strip() == "hello"
```

</details>

#### trim removes leading and trailing whitespace

- trim removes leading and trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("trim removes leading and trailing whitespace")
val text = "  hello  "
expect text.trim() == "hello"
```

</details>

#### trim_start removes leading whitespace

- trim_start removes leading whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("trim_start removes leading whitespace")
val text = "  hello  "
expect text.trim_start() == "hello  "
```

</details>

#### trim_end removes trailing whitespace

- trim_end removes trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("trim_end removes trailing whitespace")
val text = "  hello  "
expect text.trim_end() == "  hello"
```

</details>

#### Case Operations

#### to_upper converts to uppercase

- to_upper converts to uppercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("to_upper converts to uppercase")
val text = "hello"
expect text.upper() == "HELLO"
```

</details>

#### to_lower converts to lowercase

- to_lower converts to lowercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("to_lower converts to lowercase")
val text = "HELLO"
expect text.lower() == "hello"
```

</details>

#### capitalize capitalizes first letter

- capitalize capitalizes first letter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("capitalize capitalizes first letter")
val text = "hello world"
expect text.capitalize() == "Hello world"
```

</details>

#### Split and Join

#### split divides string by delimiter

- split divides string by delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("split divides string by delimiter")
val text = "a,b,c"
val parts = text.split(",")
expect parts.len() == 3
expect parts[0] == "a"
```

</details>

#### join combines list with delimiter

- join combines list with delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = ["a", "b", "c"]
expect ",".join(parts) == "a,b,c"
```

</details>

#### lines splits by newlines

- lines splits by newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lines splits by newlines")
val text = "line1\nline2\nline3"
val lines = text.lines()
expect lines.len() == 3
```

</details>

#### lines aliases preserve Rust-compatible edge cases

- lines aliases preserve Rust-compatible edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lines aliases preserve Rust-compatible edge cases")
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

- replace replaces all occurrences


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replace replaces all occurrences")
val text = "hello hello"
expect text.replace(old="hello", new="hi") == "hi hi"
```

</details>

#### replace_first replaces first occurrence

- replace_first replaces first occurrence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replace_first replaces first occurrence")
val text = "hello hello"
expect text.replace_first(old="hello", new="hi") == "hi hello"
```

</details>

### File I/O Improvements

#### File Reading

#### read_file returns file contents

- read_file returns file contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_file returns file contents")
val fs = MockFileSystem.create()
val content = fs.read_file("/tmp/test.txt")
expect content == "Hello, World!"
```

</details>

#### read_bytes returns raw bytes

- read_bytes returns raw bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_bytes returns raw bytes")
val fs = MockFileSystem.create()
val bytes = fs.read_bytes("/tmp/test.txt")
expect bytes.len() == 5
expect bytes[0] == 72
```

</details>

#### read_lines returns list of lines

- read_lines returns list of lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_lines returns list of lines")
val fs = MockFileSystem.create()
val lines = fs.read_lines("/tmp/test.txt")
expect lines.len() == 3
expect lines[0] == "line1"
```

</details>

#### File Writing

#### write_file writes string to file

- write_file writes string to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write_file writes string to file")
val fs = MockFileSystem.create()
val success = fs.write_file(path="/tmp/output.txt", content="content")
expect success == true
```

</details>

#### write_bytes writes raw bytes

- write_bytes writes raw bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write_bytes writes raw bytes")
val fs = MockFileSystem.create()
val success = fs.write_bytes("/tmp/output.bin", [1, 2, 3])
expect success == true
```

</details>

#### append_file appends to existing file

- append_file appends to existing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("append_file appends to existing file")
val fs = MockFileSystem.create()
val success = fs.append_file(path="/tmp/test.txt", content="more")
expect success == true
```

</details>

#### File Metadata

#### path_exists checks if path exists

- path_exists checks if path exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("path_exists checks if path exists")
val fs = MockFileSystem.create()
expect fs.path_exists("/tmp/test.txt") == true
expect fs.path_exists("/nonexistent") == false
```

</details>

#### is_file checks if path is file

- is_file checks if path is file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is_file checks if path is file")
val fs = MockFileSystem.create()
expect fs.is_file("/tmp/test.txt") == true
expect fs.is_file("/tmp") == false
```

</details>

#### is_dir checks if path is directory

- is_dir checks if path is directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is_dir checks if path is directory")
val fs = MockFileSystem.create()
expect fs.is_dir("/tmp") == true
expect fs.is_dir("/tmp/test.txt") == false
```

</details>

#### file_size returns size in bytes

- file_size returns size in bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("file_size returns size in bytes")
val fs = MockFileSystem.create()
expect fs.file_size("/tmp/test.txt") == 13
```

</details>

#### Directory Operations

#### list_dir returns directory contents

- list_dir returns directory contents


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("list_dir returns directory contents")
val fs = MockFileSystem.create()
val contents = fs.list_dir("/tmp")
expect contents.len() == 2
```

</details>

#### create_dir creates new directory

- create_dir creates new directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("create_dir creates new directory")
val fs = MockFileSystem.create()
val success = fs.create_dir("/tmp/newdir")
expect success == true
```

</details>

#### remove_file deletes file

- remove_file deletes file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("remove_file deletes file")
val fs = MockFileSystem.create()
val success = fs.remove_file("/tmp/test.txt")
expect success == true
```

</details>

#### remove_dir deletes directory

- remove_dir deletes directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("remove_dir deletes directory")
val fs = MockFileSystem.create()
val success = fs.remove_dir("/tmp")
expect success == true
```

</details>

### JSON Library Improvements

#### JSON Parsing

#### from_json parses JSON string

- from_json parses JSON string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("from_json parses JSON string")
val json = MockJson.from_json("object:test")
expect json.is_object() == true
```

</details>

#### parses JSON arrays

- parses JSON arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses JSON arrays")
val json = MockJson.from_json("array:test")
expect json.is_array() == true
```

</details>

#### parses nested JSON

- parses nested JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses nested JSON")
val json = MockJson.from_json("object:nested")
expect json.is_object() == true
```

</details>

#### JSON Generation

#### to_json converts dict to JSON

- to_json converts dict to JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("to_json converts dict to JSON")
val json_str = MockJson.to_json("test")
expect json_str.contains("json:")
```

</details>

#### to_json handles nested structures

- to_json handles nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("to_json handles nested structures")
val json_str = MockJson.to_json("nested")
expect json_str.starts_with("json:")
```

</details>

#### escapes special characters

- escapes special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("escapes special characters")
val escaped = MockJson.escape("test")
expect escaped.starts_with("escaped:")
```

</details>

#### JSON Builder

#### builds JSON objects fluently

- builds JSON objects fluently


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds JSON objects fluently")
val builder = MockJsonBuilder.object()
builder.add(key="key", value="value")
val json_str = builder.build()
expect json_str.contains("key")
```

</details>

#### builds JSON arrays fluently

- builds JSON arrays fluently


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds JSON arrays fluently")
val builder = MockJsonBuilder.array()
builder.append("item")
val json_str = builder.build()
expect json_str.contains("item")
```

</details>

### Error Handling Improvements

#### Question Mark Operator

#### propagates Result errors

- propagates Result errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("propagates Result errors")
# Test that ? propagates Err values
val success = wrapper_divide(a=10, b=2)
expect success.is_ok() == true
expect success.unwrap() == 10

val failure = wrapper_divide(a=10, b=0)
expect failure.is_err() == true
```

</details>

#### propagates Option None

- propagates Option None


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("propagates Option None")
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

- chains multiple ? operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("chains multiple ? operations")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text Method Improvements, File I/O Improvements, JSON Library Improvements, Error Handling Improvements.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `955f09df53d524dde2770a6801162b5329014023af7a23a356aeb907552ec7b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `955f09df53d524dde2770a6801162b5329014023af7a23a356aeb907552ec7b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `955f09df53d524dde2770a6801162b5329014023af7a23a356aeb907552ec7b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl
mirror: doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/improvements/stdlib_improvements_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'substring extracts range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'substr extracts with length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'char_at gets single character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
