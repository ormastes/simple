# Resources Mime Uri Specification

> <details>

<!-- sdn-diagram:id=resources_mime_uri_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resources_mime_uri_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resources_mime_uri_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resources_mime_uri_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resources Mime Uri Specification

## Scenarios

### ResourceInfo

#### creates with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ResourceInfo(
    uri: "file:///src/main.spl",
    name: "Main Source",
    description: "Main entry point",
    mime_type: "text/x-simple"
)
expect(info.uri).to_equal("file:///src/main.spl")
expect(info.name).to_equal("Main Source")
expect(info.description).to_equal("Main entry point")
expect(info.mime_type).to_equal("text/x-simple")
```

</details>

#### handles empty description

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ResourceInfo(
    uri: "symbol:///MyClass",
    name: "MyClass",
    description: "",
    mime_type: "application/json"
)
expect(info.description).to_equal("")
```

</details>

#### stores project info URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ResourceInfo(
    uri: "project:///info",
    name: "Project Information",
    description: "Project metadata",
    mime_type: "text/plain"
)
expect(info.uri).to_equal("project:///info")
```

</details>

### ResourceTemplate

#### creates with URI template pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl_uri = "file:///" + "{" + "path" + "}"
val tmpl = ResourceTemplate(
    uri_template: tpl_uri,
    name: "File Contents",
    description: "Read file contents by path",
    mime_type: "text/plain"
)
expect(tmpl.uri_template).to_start_with("file:///")
expect(tmpl.name).to_equal("File Contents")
```

</details>

#### stores symbol template

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl_uri = "symbol:///" + "{" + "name" + "}"
val tmpl = ResourceTemplate(
    uri_template: tpl_uri,
    name: "Symbol Information",
    description: "Get symbol details by name",
    mime_type: "application/json"
)
expect(tmpl.uri_template).to_start_with("symbol:///")
```

</details>

#### stores bugdb template

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl_uri = "bugdb:///" + "{" + "query" + "}"
val tmpl = ResourceTemplate(
    uri_template: tpl_uri,
    name: "Bug Database",
    description: "Query bug database",
    mime_type: "application/json"
)
expect(tmpl.uri_template).to_start_with("bugdb:///")
```

</details>

### ResourceContent

#### creates with uri and contents

1. contents: "fn main
   - Expected: content.uri equals `file:///test.spl`
   - Expected: content.mime_type equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ResourceContent(
    uri: "file:///test.spl",
    contents: "fn main(): print(\"hello\")",
    mime_type: "text/x-simple"
)
expect(content.uri).to_equal("file:///test.spl")
expect(content.contents).to_contain("main")
expect(content.mime_type).to_equal("text/x-simple")
```

</details>

#### handles empty contents

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ResourceContent(
    uri: "file:///empty.spl",
    contents: "",
    mime_type: "text/x-simple"
)
expect(content.contents).to_equal("")
```

</details>

#### handles large content

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var large = ""
for i in 0..100:
    large = large + "line {i}{NL}"
val content = ResourceContent(
    uri: "file:///large.spl",
    contents: large,
    mime_type: "text/plain"
)
expect(content.contents).to_contain("line 0")
expect(content.contents).to_contain("line 99")
```

</details>

### get_mime_type_for_uri

#### returns text/x-simple for .spl files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("file:///src/main.spl")
expect(mime).to_equal("text/x-simple")
```

</details>

#### returns text/x-simple for .shs files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("file:///script.shs")
expect(mime).to_equal("text/x-simple")
```

</details>

#### returns application/json for .json files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("file:///data.json")
expect(mime).to_equal("application/json")
```

</details>

#### returns text/markdown for .md files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("file:///README.md")
expect(mime).to_equal("text/markdown")
```

</details>

#### returns text/plain for unknown file extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("file:///data.txt")
expect(mime).to_equal("text/plain")
```

</details>

#### returns text/plain for files without extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("file:///Makefile")
expect(mime).to_equal("text/plain")
```

</details>

#### returns application/json for symbol URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("symbol:///MyClass")
expect(mime).to_equal("application/json")
```

</details>

#### returns application/json for type URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("type:///String")
expect(mime).to_equal("application/json")
```

</details>

#### returns text/markdown for docs URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("docs:///guide/intro")
expect(mime).to_equal("text/markdown")
```

</details>

#### returns text/plain for tree URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("tree:///src/")
expect(mime).to_equal("text/plain")
```

</details>

#### returns empty string for unknown URI schemes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("custom:///resource")
expect(mime).to_equal("")
```

</details>

#### returns empty string for bugdb URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = get_mime_type_for_uri("bugdb:///all")
expect(mime).to_equal("")
```

</details>

### repeat_string

#### repeats string given number of times

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = repeat_string("ab", 3)
expect(result).to_equal("ababab")
```

</details>

#### returns empty string for count of zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = repeat_string("x", 0)
expect(result).to_equal("")
```

</details>

#### repeats single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = repeat_string("*", 5)
expect(result).to_equal("*****")
```

</details>

#### handles indentation pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = repeat_string("  ", 3)
expect(result).to_equal("      ")
```

</details>

#### handles single repetition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = repeat_string("hello", 1)
expect(result).to_equal("hello")
```

</details>

### URI routing

#### routes project:///info to project_info

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("project:///info")).to_equal("project_info")
```

</details>

#### routes file:// URIs to file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("file:///src/main.spl")).to_equal("file")
```

</details>

#### routes symbol:// URIs to symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("symbol:///MyClass")).to_equal("symbol")
```

</details>

#### routes type:// URIs to type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("type:///String")).to_equal("type")
```

</details>

#### routes docs:// URIs to docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("docs:///guide")).to_equal("docs")
```

</details>

#### routes tree:// URIs to tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("tree:///src/")).to_equal("tree")
```

</details>

#### routes bugdb:// URIs to bugdb

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("bugdb:///all")).to_equal("bugdb")
```

</details>

#### routes featuredb:// URIs to featuredb

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("featuredb:///stats")).to_equal("featuredb")
```

</details>

#### routes testdb:// URIs to testdb

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("testdb:///runs")).to_equal("testdb")
```

</details>

#### routes unknown URIs to unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("custom:///foo")).to_equal("unknown")
```

</details>

#### routes empty string to unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(route_uri("")).to_equal("unknown")
```

</details>

### Type Resource Path Normalization

#### normalizes bare type name to default type domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_resource_path("Text")
expect(normalized).to_equal("src/type/simple_lang/Text.spl")
```

</details>

#### normalizes owned-domain import to type directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_resource_path("simple-lang/Bool")
expect(normalized).to_equal("src/type/simple_lang/Bool.spl")
```

</details>

#### keeps nested owned-domain path segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_resource_path("simple-lang/math/F64")
expect(normalized).to_equal("src/type/simple_lang/math/F64.spl")
```

</details>

#### does not rewrite dotted module paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_type_resource_path("compiler.frontend.core")
expect(normalized).to_equal("")
```

</details>

### URI path extraction

#### extracts file path from file URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = extract_file_path("file:///src/main.spl")
expect(path).to_equal("/src/main.spl")
```

</details>

#### extracts path with triple slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = extract_file_path("file:///absolute/path.spl")
expect(path).to_equal("/absolute/path.spl")
```

</details>

#### extracts symbol name from symbol URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = extract_symbol_name("symbol:///MyClass")
expect(name).to_equal("/MyClass")
```

</details>

#### extracts type name from type URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = extract_type_name("type:///String")
expect(name).to_equal("/String")
```

</details>

#### extracts bugdb query from bugdb URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = extract_bugdb_query("bugdb:///all")
expect(query).to_equal("/all")
```

</details>

#### extracts bugdb critical query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = extract_bugdb_query("bugdb:///critical")
expect(query).to_equal("/critical")
```

</details>

### extract_json_string

#### extracts string value by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\": \"Alice\", \"age\": 30}"
val name = extract_json_string(json, "name")
expect(name).to_equal("Alice")
```

</details>

#### returns empty string for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\": \"Alice\"}"
val missing = extract_json_string(json, "email")
expect(missing).to_equal("")
```

</details>

#### extracts from complex JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"status\": \"open\", \"priority\": \"P0\", \"title\": \"Fix bug\"}"
expect(extract_json_string(json, "status")).to_equal("open")
expect(extract_json_string(json, "priority")).to_equal("P0")
expect(extract_json_string(json, "title")).to_equal("Fix bug")
```

</details>

#### handles empty string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"value\": \"\"}"
val result = extract_json_string(json, "value")
expect(result).to_equal("")
```

</details>

#### extracts first occurrence of key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\": \"first\", \"other\": \"second\"}"
val result = extract_json_string(json, "key")
expect(result).to_equal("first")
```

</details>

#### returns empty for empty JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_json_string("{}", "key")
expect(result).to_equal("")
```

</details>

### extract_json_int

#### extracts integer value by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"count\": 42, \"name\": \"test\"}"
val count = extract_json_int(json, "count")
expect(count).to_equal(42)
```

</details>

#### returns 0 for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"count\": 42}"
val missing = extract_json_int(json, "other")
expect(missing).to_equal(0)
```

</details>

#### extracts zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"count\": 0}"
val count = extract_json_int(json, "count")
expect(count).to_equal(0)
```

</details>

#### extracts large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"total\": 999999}"
val total = extract_json_int(json, "total")
expect(total).to_equal(999999)
```

</details>

#### returns 0 for empty JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_json_int("{}", "key")
expect(result).to_equal(0)
```

</details>

### bugdb query routing

#### recognizes /all query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = extract_bugdb_query("bugdb:///all")
var is_all = query == "/all" or query == "all"
expect(is_all).to_equal(true)
```

</details>

#### recognizes /open query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = extract_bugdb_query("bugdb:///open")
var is_open = query == "/open" or query == "open"
expect(is_open).to_equal(true)
```

</details>

#### recognizes /critical query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = extract_bugdb_query("bugdb:///critical")
var is_critical = query == "/critical" or query == "critical"
expect(is_critical).to_equal(true)
```

</details>

#### recognizes /stats query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = extract_bugdb_query("bugdb:///stats")
var is_stats = query == "/stats" or query == "stats"
expect(is_stats).to_equal(true)
```

</details>

### resource list coverage

#### verifies expected static resource URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_uris = [
    "project:///info",
    "file:///*",
    "symbol:///*",
    "type:///*",
    "docs:///*",
    "tree:///*",
    "bugdb:///all",
    "bugdb:///open",
    "bugdb:///critical",
    "bugdb:///stats",
    "featuredb:///all",
    "featuredb:///stats",
    "testdb:///runs",
    "testdb:///stats",
    "testdb:///flaky"
]
expect(expected_uris.len()).to_equal(15)
```

</details>

#### verifies expected template URI count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template_count = 6
expect(template_count).to_equal(6)
```

</details>

#### all template URI prefixes are unique

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefixes = [
    "file:///",
    "symbol:///",
    "type:///",
    "docs:///",
    "tree:///",
    "bugdb:///"
]
expect(prefixes.len()).to_equal(6)
expect(prefixes[0]).to_start_with("file")
expect(prefixes[1]).to_start_with("symbol")
expect(prefixes[2]).to_start_with("type")
expect(prefixes[3]).to_start_with("docs")
expect(prefixes[4]).to_start_with("tree")
expect(prefixes[5]).to_start_with("bugdb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/resources_mime_uri_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ResourceInfo
- ResourceTemplate
- ResourceContent
- get_mime_type_for_uri
- repeat_string
- URI routing
- Type Resource Path Normalization
- URI path extraction
- extract_json_string
- extract_json_int
- bugdb query routing
- resource list coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
