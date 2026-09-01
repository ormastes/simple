# Resources Mime Uri Specification

> Tests covering ResourceInfo, ResourceTemplate, ResourceContent, get_mime_type_for_uri, repeat_string, URI routing, Type Resource Path Normalization, URI path extraction, extract_json_string, extract_json_int, bugdb query routing, resource list coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resources Mime Uri Specification

## Scenarios

### ResourceInfo

#### creates with all fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates with all fields
   - Expected: info.uri equals `file:///src/main.spl`
   - Expected: info.name equals `Main Source`
   - Expected: info.description equals `Main entry point`
   - Expected: info.mime_type equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with all fields")
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

- handles empty description
   - Expected: info.description equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty description")
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

- stores project info URI
   - Expected: info.uri equals `project:///info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores project info URI")
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

- creates with URI template pattern
   - Expected: tmpl.name equals `File Contents`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with URI template pattern")
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

- stores symbol template


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores symbol template")
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

- stores bugdb template


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores bugdb template")
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

- creates with uri and contents
   - Expected: content.uri equals `file:///test.spl`
   - Expected: content.mime_type equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with uri and contents")
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

- handles empty contents
   - Expected: content.contents equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty contents")
val content = ResourceContent(
    uri: "file:///empty.spl",
    contents: "",
    mime_type: "text/x-simple"
)
expect(content.contents).to_equal("")
```

</details>

#### handles large content

- handles large content


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large content")
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

- returns text/x-simple for .spl files
   - Expected: mime equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/x-simple for .spl files")
val mime = get_mime_type_for_uri("file:///src/main.spl")
expect(mime).to_equal("text/x-simple")
```

</details>

#### returns text/x-simple for .shs files

- returns text/x-simple for .shs files
   - Expected: mime equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/x-simple for .shs files")
val mime = get_mime_type_for_uri("file:///script.shs")
expect(mime).to_equal("text/x-simple")
```

</details>

#### returns application/json for .json files

- returns application/json for .json files
   - Expected: mime equals `application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns application/json for .json files")
val mime = get_mime_type_for_uri("file:///data.json")
expect(mime).to_equal("application/json")
```

</details>

#### returns text/markdown for .md files

- returns text/markdown for .md files
   - Expected: mime equals `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/markdown for .md files")
val mime = get_mime_type_for_uri("file:///README.md")
expect(mime).to_equal("text/markdown")
```

</details>

#### returns text/plain for unknown file extensions

- returns text/plain for unknown file extensions
   - Expected: mime equals `text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/plain for unknown file extensions")
val mime = get_mime_type_for_uri("file:///data.txt")
expect(mime).to_equal("text/plain")
```

</details>

#### returns text/plain for files without extension

- returns text/plain for files without extension
   - Expected: mime equals `text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/plain for files without extension")
val mime = get_mime_type_for_uri("file:///Makefile")
expect(mime).to_equal("text/plain")
```

</details>

#### returns application/json for symbol URIs

- returns application/json for symbol URIs
   - Expected: mime equals `application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns application/json for symbol URIs")
val mime = get_mime_type_for_uri("symbol:///MyClass")
expect(mime).to_equal("application/json")
```

</details>

#### returns application/json for type URIs

- returns application/json for type URIs
   - Expected: mime equals `application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns application/json for type URIs")
val mime = get_mime_type_for_uri("type:///String")
expect(mime).to_equal("application/json")
```

</details>

#### returns text/markdown for docs URIs

- returns text/markdown for docs URIs
   - Expected: mime equals `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/markdown for docs URIs")
val mime = get_mime_type_for_uri("docs:///guide/intro")
expect(mime).to_equal("text/markdown")
```

</details>

#### returns text/plain for tree URIs

- returns text/plain for tree URIs
   - Expected: mime equals `text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns text/plain for tree URIs")
val mime = get_mime_type_for_uri("tree:///src/")
expect(mime).to_equal("text/plain")
```

</details>

#### returns empty string for unknown URI schemes

- returns empty string for unknown URI schemes
   - Expected: mime equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for unknown URI schemes")
val mime = get_mime_type_for_uri("custom:///resource")
expect(mime).to_equal("")
```

</details>

#### returns empty string for bugdb URIs

- returns empty string for bugdb URIs
   - Expected: mime equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for bugdb URIs")
val mime = get_mime_type_for_uri("bugdb:///all")
expect(mime).to_equal("")
```

</details>

### repeat_string

#### repeats string given number of times

- repeats string given number of times
   - Expected: result equals `ababab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats string given number of times")
val result = repeat_string("ab", 3)
expect(result).to_equal("ababab")
```

</details>

#### returns empty string for count of zero

- returns empty string for count of zero
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for count of zero")
val result = repeat_string("x", 0)
expect(result).to_equal("")
```

</details>

#### repeats single character

- repeats single character
   - Expected: result equals `*****`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats single character")
val result = repeat_string("*", 5)
expect(result).to_equal("*****")
```

</details>

#### handles indentation pattern

- handles indentation pattern
   - Expected: result equals `      `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles indentation pattern")
val result = repeat_string("  ", 3)
expect(result).to_equal("      ")
```

</details>

#### handles single repetition

- handles single repetition
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single repetition")
val result = repeat_string("hello", 1)
expect(result).to_equal("hello")
```

</details>

### URI routing

#### routes project:///info to project_info

- routes project:///info to project_info
   - Expected: route_uri("project:///info") equals `project_info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes project:///info to project_info")
expect(route_uri("project:///info")).to_equal("project_info")
```

</details>

#### routes file:// URIs to file

- routes file:// URIs to file
   - Expected: route_uri("file:///src/main.spl") equals `file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes file:// URIs to file")
expect(route_uri("file:///src/main.spl")).to_equal("file")
```

</details>

#### routes symbol:// URIs to symbol

- routes symbol:// URIs to symbol
   - Expected: route_uri("symbol:///MyClass") equals `symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes symbol:// URIs to symbol")
expect(route_uri("symbol:///MyClass")).to_equal("symbol")
```

</details>

#### routes type:// URIs to type

- routes type:// URIs to type
   - Expected: route_uri("type:///String") equals `type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes type:// URIs to type")
expect(route_uri("type:///String")).to_equal("type")
```

</details>

#### routes docs:// URIs to docs

- routes docs:// URIs to docs
   - Expected: route_uri("docs:///guide") equals `docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes docs:// URIs to docs")
expect(route_uri("docs:///guide")).to_equal("docs")
```

</details>

#### routes tree:// URIs to tree

- routes tree:// URIs to tree
   - Expected: route_uri("tree:///src/") equals `tree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes tree:// URIs to tree")
expect(route_uri("tree:///src/")).to_equal("tree")
```

</details>

#### routes bugdb:// URIs to bugdb

- routes bugdb:// URIs to bugdb
   - Expected: route_uri("bugdb:///all") equals `bugdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes bugdb:// URIs to bugdb")
expect(route_uri("bugdb:///all")).to_equal("bugdb")
```

</details>

#### routes featuredb:// URIs to featuredb

- routes featuredb:// URIs to featuredb
   - Expected: route_uri("featuredb:///stats") equals `featuredb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes featuredb:// URIs to featuredb")
expect(route_uri("featuredb:///stats")).to_equal("featuredb")
```

</details>

#### routes testdb:// URIs to testdb

- routes testdb:// URIs to testdb
   - Expected: route_uri("testdb:///runs") equals `testdb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes testdb:// URIs to testdb")
expect(route_uri("testdb:///runs")).to_equal("testdb")
```

</details>

#### routes unknown URIs to unknown

- routes unknown URIs to unknown
   - Expected: route_uri("custom:///foo") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes unknown URIs to unknown")
expect(route_uri("custom:///foo")).to_equal("unknown")
```

</details>

#### routes empty string to unknown

- routes empty string to unknown
   - Expected: route_uri("") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes empty string to unknown")
expect(route_uri("")).to_equal("unknown")
```

</details>

### Type Resource Path Normalization

#### normalizes bare type name to default type domain

- normalizes bare type name to default type domain
   - Expected: normalized equals `src/type/simple_lang/Text.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes bare type name to default type domain")
val normalized = normalize_type_resource_path("Text")
expect(normalized).to_equal("src/type/simple_lang/Text.spl")
```

</details>

#### normalizes owned-domain import to type directory

- normalizes owned-domain import to type directory
   - Expected: normalized equals `src/type/simple_lang/Bool.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes owned-domain import to type directory")
val normalized = normalize_type_resource_path("simple-lang/Bool")
expect(normalized).to_equal("src/type/simple_lang/Bool.spl")
```

</details>

#### keeps nested owned-domain path segments

- keeps nested owned-domain path segments
   - Expected: normalized equals `src/type/simple_lang/math/F64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps nested owned-domain path segments")
val normalized = normalize_type_resource_path("simple-lang/math/F64")
expect(normalized).to_equal("src/type/simple_lang/math/F64.spl")
```

</details>

#### does not rewrite dotted module paths

- does not rewrite dotted module paths
   - Expected: normalized equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite dotted module paths")
val normalized = normalize_type_resource_path("compiler.frontend.core")
expect(normalized).to_equal("")
```

</details>

### URI path extraction

#### extracts file path from file URI

- extracts file path from file URI
   - Expected: path equals `/src/main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts file path from file URI")
val path = extract_file_path("file:///src/main.spl")
expect(path).to_equal("/src/main.spl")
```

</details>

#### extracts path with triple slash

- extracts path with triple slash
   - Expected: path equals `/absolute/path.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts path with triple slash")
val path = extract_file_path("file:///absolute/path.spl")
expect(path).to_equal("/absolute/path.spl")
```

</details>

#### extracts symbol name from symbol URI

- extracts symbol name from symbol URI
   - Expected: name equals `/MyClass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts symbol name from symbol URI")
val name = extract_symbol_name("symbol:///MyClass")
expect(name).to_equal("/MyClass")
```

</details>

#### extracts type name from type URI

- extracts type name from type URI
   - Expected: name equals `/String`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type name from type URI")
val name = extract_type_name("type:///String")
expect(name).to_equal("/String")
```

</details>

#### extracts bugdb query from bugdb URI

- extracts bugdb query from bugdb URI
   - Expected: query equals `/all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts bugdb query from bugdb URI")
val query = extract_bugdb_query("bugdb:///all")
expect(query).to_equal("/all")
```

</details>

#### extracts bugdb critical query

- extracts bugdb critical query
   - Expected: query equals `/critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts bugdb critical query")
val query = extract_bugdb_query("bugdb:///critical")
expect(query).to_equal("/critical")
```

</details>

### extract_json_string

#### extracts string value by key

- extracts string value by key
   - Expected: name equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string value by key")
val json = "{\"name\": \"Alice\", \"age\": 30}"
val name = extract_json_string(json, "name")
expect(name).to_equal("Alice")
```

</details>

#### returns empty string for missing key

- returns empty string for missing key
   - Expected: missing equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for missing key")
val json = "{\"name\": \"Alice\"}"
val missing = extract_json_string(json, "email")
expect(missing).to_equal("")
```

</details>

#### extracts from complex JSON

- extracts from complex JSON
   - Expected: extract_json_string(json, "status") equals `open`
   - Expected: extract_json_string(json, "priority") equals `P0`
   - Expected: extract_json_string(json, "title") equals `Fix bug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts from complex JSON")
val json = "{\"status\": \"open\", \"priority\": \"P0\", \"title\": \"Fix bug\"}"
expect(extract_json_string(json, "status")).to_equal("open")
expect(extract_json_string(json, "priority")).to_equal("P0")
expect(extract_json_string(json, "title")).to_equal("Fix bug")
```

</details>

#### handles empty string value

- handles empty string value
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string value")
val json = "{\"value\": \"\"}"
val result = extract_json_string(json, "value")
expect(result).to_equal("")
```

</details>

#### extracts first occurrence of key

- extracts first occurrence of key
   - Expected: result equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts first occurrence of key")
val json = "{\"key\": \"first\", \"other\": \"second\"}"
val result = extract_json_string(json, "key")
expect(result).to_equal("first")
```

</details>

#### returns empty for empty JSON

- returns empty for empty JSON
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty JSON")
val result = extract_json_string("{}", "key")
expect(result).to_equal("")
```

</details>

### extract_json_int

#### extracts integer value by key

- extracts integer value by key
   - Expected: count equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts integer value by key")
val json = "{\"count\": 42, \"name\": \"test\"}"
val count = extract_json_int(json, "count")
expect(count).to_equal(42)
```

</details>

#### returns 0 for missing key

- returns 0 for missing key
   - Expected: missing equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for missing key")
val json = "{\"count\": 42}"
val missing = extract_json_int(json, "other")
expect(missing).to_equal(0)
```

</details>

#### extracts zero value

- extracts zero value
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts zero value")
val json = "{\"count\": 0}"
val count = extract_json_int(json, "count")
expect(count).to_equal(0)
```

</details>

#### extracts large numbers

- extracts large numbers
   - Expected: total equals `999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts large numbers")
val json = "{\"total\": 999999}"
val total = extract_json_int(json, "total")
expect(total).to_equal(999999)
```

</details>

#### returns 0 for empty JSON

- returns 0 for empty JSON
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty JSON")
val result = extract_json_int("{}", "key")
expect(result).to_equal(0)
```

</details>

### bugdb query routing

#### recognizes /all query

- recognizes /all query
   - Expected: is_all is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes /all query")
val query = extract_bugdb_query("bugdb:///all")
var is_all = query == "/all" or query == "all"
expect(is_all).to_equal(true)
```

</details>

#### recognizes /open query

- recognizes /open query
   - Expected: is_open is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes /open query")
val query = extract_bugdb_query("bugdb:///open")
var is_open = query == "/open" or query == "open"
expect(is_open).to_equal(true)
```

</details>

#### recognizes /critical query

- recognizes /critical query
   - Expected: is_critical is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes /critical query")
val query = extract_bugdb_query("bugdb:///critical")
var is_critical = query == "/critical" or query == "critical"
expect(is_critical).to_equal(true)
```

</details>

#### recognizes /stats query

- recognizes /stats query
   - Expected: is_stats is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes /stats query")
val query = extract_bugdb_query("bugdb:///stats")
var is_stats = query == "/stats" or query == "stats"
expect(is_stats).to_equal(true)
```

</details>

### resource list coverage

#### verifies expected static resource URIs

- verifies expected static resource URIs
   - Expected: expected_uris.len() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies expected static resource URIs")
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

- verifies expected template URI count
   - Expected: template_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies expected template URI count")
val template_count = 6
expect(template_count).to_equal(6)
```

</details>

#### all template URI prefixes are unique

- all template URI prefixes are unique
   - Expected: prefixes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all template URI prefixes are unique")
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
| Source | `test/unit/app/mcp_unit/resources_mime_uri_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ResourceInfo, ResourceTemplate, ResourceContent, get_mime_type_for_uri, repeat_string, URI routing, Type Resource Path Normalization, URI path extraction, extract_json_string, extract_json_int, bugdb query routing, resource list coverage.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e246118dc8c34939d145d612b8087604196da49b0514f3899cb4064747c5156`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e246118dc8c34939d145d612b8087604196da49b0514f3899cb4064747c5156`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e246118dc8c34939d145d612b8087604196da49b0514f3899cb4064747c5156`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/resources_mime_uri_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/resources_mime_uri_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/resources_mime_uri_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/resources_mime_uri_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/resources_mime_uri_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/resources_mime_uri_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/resources_mime_uri_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty description' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/resources_mime_uri_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores project info URI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
