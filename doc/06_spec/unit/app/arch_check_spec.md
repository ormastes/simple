# arch_check_spec

> Purpose: Prove that arch_check: _str_trim.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 74 | 74 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# arch_check_spec

Purpose: Prove that arch_check: _str_trim.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/arch_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that arch_check: _str_trim.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### arch_check: _str_trim

#### trims leading spaces

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trims leading spaces
- Verify: trims leading spaces
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims leading spaces")
step("Verify: trims leading spaces")
# @req: REQ-APP-ARCH-CHECK-STR-TRIM-001
val result = _str_trim("  hello")
expect(result).to_equal("hello")
```

</details>

#### trims trailing spaces

- trims trailing spaces
- Verify: trims trailing spaces
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims trailing spaces")
step("Verify: trims trailing spaces")
val result = _str_trim("hello  ")
expect(result).to_equal("hello")
```

</details>

#### trims both sides

- trims both sides
- Verify: trims both sides
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims both sides")
step("Verify: trims both sides")
val result = _str_trim("  hello world  ")
expect(result).to_equal("hello world")
```

</details>

#### returns unchanged string when no whitespace

- returns unchanged string when no whitespace
- Verify: returns unchanged string when no whitespace
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unchanged string when no whitespace")
step("Verify: returns unchanged string when no whitespace")
val result = _str_trim("hello")
expect(result).to_equal("hello")
```

</details>

#### returns empty string for all whitespace

- returns empty string for all whitespace
- Verify: returns empty string for all whitespace
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for all whitespace")
step("Verify: returns empty string for all whitespace")
val result = _str_trim("   ")
expect(result).to_equal("")
```

</details>

### arch_check: _parse_pattern_list

#### parses single pattern

- parses single pattern
- Verify: parses single pattern
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single pattern")
step("Verify: parses single pattern")
val result = _parse_pattern_list("allow = [\"core\"]")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("core")
```

</details>

#### parses multiple patterns

- parses multiple patterns
- Verify: parses multiple patterns
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `core`
   - Expected: result[1] equals `std`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple patterns")
step("Verify: parses multiple patterns")
val result = _parse_pattern_list("allow = [\"core\", \"std\"]")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("core")
expect(result[1]).to_equal("std")
```

</details>

#### parses glob patterns

- parses glob patterns
- Verify: parses glob patterns
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `compiler/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses glob patterns")
step("Verify: parses glob patterns")
val result = _parse_pattern_list("deny = [\"compiler/**\", \"app.io\"]")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("compiler/**")
```

</details>

#### returns empty for missing brackets

- returns empty for missing brackets
- Verify: returns empty for missing brackets
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing brackets")
step("Verify: returns empty for missing brackets")
val result = _parse_pattern_list("allow = core")
expect(result.len()).to_equal(0)
```

</details>

#### handles empty list

- handles empty list
- Verify: handles empty list
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty list")
step("Verify: handles empty list")
val result = _parse_pattern_list("deny = []")
expect(result.len()).to_equal(0)
```

</details>

### arch_check: _parse_string_value

#### parses double-quoted value

- parses double-quoted value
- Verify: parses double-quoted value
   - Expected: result equals `entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses double-quoted value")
step("Verify: parses double-quoted value")
val result = _parse_string_value("dimension = \"entity\"")
expect(result).to_equal("entity")
```

</details>

#### parses single-quoted value

- parses single-quoted value
- Verify: parses single-quoted value
   - Expected: result equals `transform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single-quoted value")
step("Verify: parses single-quoted value")
val result = _parse_string_value("dimension = 'transform'")
expect(result).to_equal("transform")
```

</details>

#### returns empty when no equals sign

- returns empty when no equals sign
- Verify: returns empty when no equals sign
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when no equals sign")
step("Verify: returns empty when no equals sign")
val result = _parse_string_value("no equals here")
expect(result).to_equal("")
```

</details>

#### trims whitespace around value

- trims whitespace around value
- Verify: trims whitespace around value
   - Expected: result equals `feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace around value")
step("Verify: trims whitespace around value")
val result = _parse_string_value("dimension =   \"feature\"  ")
expect(result).to_equal("feature")
```

</details>

### arch_check: _parse_arch_block

#### returns false when no arch block

- returns false when no arch block
- Verify: returns false when no arch block
   - Expected: result.0 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no arch block")
step("Verify: returns false when no arch block")
val content = "mod simple\nexport foo.*\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(false)
```

</details>

#### returns true when arch block exists

- returns true when arch block exists
- Verify: returns true when arch block exists
   - Expected: result.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when arch block exists")
step("Verify: returns true when arch block exists")
var content = "arch {\n"
content = content + "  dimension = \"entity\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
```

</details>

#### parses allow patterns from imports block

- parses allow patterns from imports block
- Verify: parses allow patterns from imports block
   - Expected: result.0 is true
   - Expected: allow_list.len() equals `2`
   - Expected: allow_list[0] equals `core/entity/**`
   - Expected: allow_list[1] equals `shared/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses allow patterns from imports block")
step("Verify: parses allow patterns from imports block")
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    allow = [\"core/entity/**\", \"shared/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
val allow_list = result.1
expect(allow_list.len()).to_equal(2)
expect(allow_list[0]).to_equal("core/entity/**")
expect(allow_list[1]).to_equal("shared/**")
```

</details>

#### parses deny patterns from imports block

- parses deny patterns from imports block
- Verify: parses deny patterns from imports block
   - Expected: result.0 is true
   - Expected: deny.len() equals `2`
   - Expected: deny[0] equals `compiler/**`
   - Expected: deny[1] equals `feature/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses deny patterns from imports block")
step("Verify: parses deny patterns from imports block")
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    deny = [\"compiler/**\", \"feature/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
val deny = result.2
expect(deny.len()).to_equal(2)
expect(deny[0]).to_equal("compiler/**")
expect(deny[1]).to_equal("feature/**")
```

</details>

#### parses both allow and deny

- parses both allow and deny
- Verify: parses both allow and deny
   - Expected: result.0 is true
   - Expected: result.1.len() equals `1`
   - Expected: result.2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses both allow and deny")
step("Verify: parses both allow and deny")
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    allow = [\"core/entity/**\"]\n"
content = content + "    deny = [\"compiler/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.1.len()).to_equal(1)
expect(result.2.len()).to_equal(1)
```

</details>

#### returns empty patterns when no imports block

- returns empty patterns when no imports block
- Verify: returns empty patterns when no imports block
   - Expected: result.0 is true
   - Expected: result.1.len() equals `0`
   - Expected: result.2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty patterns when no imports block")
step("Verify: returns empty patterns when no imports block")
var content = "arch {\n"
content = content + "  dimension = \"entity\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.1.len()).to_equal(0)
expect(result.2.len()).to_equal(0)
```

</details>

#### parses dimension from arch block

- parses dimension from arch block
- Verify: parses dimension from arch block
   - Expected: result.0 is true
   - Expected: result.3 equals `transform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses dimension from arch block")
step("Verify: parses dimension from arch block")
var content = "arch {\n"
content = content + "  dimension = \"transform\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.3).to_equal("transform")
```

</details>

#### parses transform allow_from

- parses transform allow_from
- Verify: parses transform allow_from
   - Expected: result.0 is true
   - Expected: tf.len() equals `1`
   - Expected: tf[0] equals `entity/Identity/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses transform allow_from")
step("Verify: parses transform allow_from")
var content = "arch {\n"
content = content + "  transform {\n"
content = content + "    allow_from = [\"entity/Identity/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
val tf = result.4
expect(tf.len()).to_equal(1)
expect(tf[0]).to_equal("entity/Identity/**")
```

</details>

#### parses dimension and transform allow_from together

- parses dimension and transform allow_from together
- Verify: parses dimension and transform allow_from together
   - Expected: result.0 is true
   - Expected: result.3 equals `transform`
   - Expected: tf.len() equals `2`
   - Expected: tf[0] equals `entity/Identity/**`
   - Expected: tf[1] equals `entity/Shared/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses dimension and transform allow_from together")
step("Verify: parses dimension and transform allow_from together")
var content = "arch {\n"
content = content + "  dimension = \"transform\"\n"
content = content + "  transform {\n"
content = content + "    allow_from = [\"entity/Identity/**\", \"entity/Shared/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.3).to_equal("transform")
val tf = result.4
expect(tf.len()).to_equal(2)
expect(tf[0]).to_equal("entity/Identity/**")
expect(tf[1]).to_equal("entity/Shared/**")
```

</details>

### arch_check: _module_path_from_init_file

#### extracts module path from absolute init file

- extracts module path from absolute init file
- Verify: extracts module path from absolute init file
   - Expected: result equals `src/compiler/10.frontend/core/entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts module path from absolute init file")
step("Verify: extracts module path from absolute init file")
val path = "/home/user/project/src/compiler/10.frontend/core/entity/__init__.spl"
val root = "/home/user/project"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src/compiler/10.frontend/core/entity")
```

</details>

#### handles top-level init file

- handles top-level init file
- Verify: handles top-level init file
   - Expected: result equals `src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles top-level init file")
step("Verify: handles top-level init file")
val path = "/project/src/__init__.spl"
val root = "/project"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src")
```

</details>

#### handles deeply nested path

- handles deeply nested path
- Verify: handles deeply nested path
   - Expected: result equals `src/compiler/10.frontend/feature/lexing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles deeply nested path")
step("Verify: handles deeply nested path")
val path = "/root/src/compiler/10.frontend/feature/lexing/__init__.spl"
val root = "/root"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src/compiler/10.frontend/feature/lexing")
```

</details>

### arch_check: _parse_imports_from_content

#### extracts simple use statements

- extracts simple use statements
- Verify: extracts simple use statements
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `app/io/mod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts simple use statements")
step("Verify: extracts simple use statements")
var content = "use app.io.mod (file_read)\n"
content = content + "fn main():\n"
content = content + "    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("app/io/mod")
```

</details>

#### extracts multiple use statements

- extracts multiple use statements
- Verify: extracts multiple use statements
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `app/io/mod`
   - Expected: result[1] equals `std/text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple use statements")
step("Verify: extracts multiple use statements")
var content = "use app.io.mod (file_read)\n"
content = content + "use std.text.\n\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("app/io/mod")
expect(result[1]).to_equal("std/text")
```

</details>

#### converts dots to slashes

- converts dots to slashes
- Verify: converts dots to slashes
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `compiler/core/ast`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts dots to slashes")
step("Verify: converts dots to slashes")
# Build content string without brace interpolation issues
val open_b = "{"
val close_b = "}"
val content = "use compiler.core.ast." + open_b + "CoreExpr" + close_b + "\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("compiler/core/ast")
```

</details>

#### ignores non-use lines

- ignores non-use lines
- Verify: ignores non-use lines
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores non-use lines")
step("Verify: ignores non-use lines")
var content = "# Comment\n"
content = content + "fn foo():\n"
content = content + "    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### handles use with wildcard

- handles use with wildcard
- Verify: handles use with wildcard
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `app/io`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles use with wildcard")
step("Verify: handles use with wildcard")
val content = "use app.io.*\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("app/io")
```

</details>

### arch_check: _match_pattern

#### matches exact paths

- matches exact paths
- Verify: matches exact paths
   - Expected: _match_pattern("core/ast", "core/ast") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exact paths")
step("Verify: matches exact paths")
expect(_match_pattern("core/ast", "core/ast")).to_equal(true)
```

</details>

#### does not match different paths

- does not match different paths
- Verify: does not match different paths
   - Expected: _match_pattern("core/ast", "std/text") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not match different paths")
step("Verify: does not match different paths")
expect(_match_pattern("core/ast", "std/text")).to_equal(false)
```

</details>

#### matches glob with /** for sub-paths

- matches glob with /** for sub-paths
- Verify: matches glob with /** for sub-paths
   - Expected: _match_pattern("compiler/feature/lexing", "compiler/**") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches glob with /** for sub-paths")
step("Verify: matches glob with /** for sub-paths")
expect(_match_pattern("compiler/feature/lexing", "compiler/**")).to_equal(true)
```

</details>

#### matches glob /** for direct child

- matches glob /** for direct child
- Verify: matches glob /** for direct child
   - Expected: _match_pattern("compiler/backend", "compiler/**") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches glob /** for direct child")
step("Verify: matches glob /** for direct child")
expect(_match_pattern("compiler/backend", "compiler/**")).to_equal(true)
```

</details>

#### does not match sibling with /**

- does not match sibling with /**
- Verify: does not match sibling with /**
   - Expected: _match_pattern("core/ast", "compiler/**") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not match sibling with /**")
step("Verify: does not match sibling with /**")
expect(_match_pattern("core/ast", "compiler/**")).to_equal(false)
```

</details>

#### matches prefix with / boundary

- matches prefix with / boundary
- Verify: matches prefix with / boundary
   - Expected: _match_pattern("compiler/backend/jit", "compiler/backend") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches prefix with / boundary")
step("Verify: matches prefix with / boundary")
expect(_match_pattern("compiler/backend/jit", "compiler/backend")).to_equal(true)
```

</details>

#### does not match partial prefix without boundary

- does not match partial prefix without boundary
- Verify: does not match partial prefix without boundary
   - Expected: _match_pattern("compiler_other/ast", "compiler") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not match partial prefix without boundary")
step("Verify: does not match partial prefix without boundary")
expect(_match_pattern("compiler_other/ast", "compiler")).to_equal(false)
```

</details>

#### matches exact with no subpath

- matches exact with no subpath
- Verify: matches exact with no subpath
   - Expected: _match_pattern("std", "std") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exact with no subpath")
step("Verify: matches exact with no subpath")
expect(_match_pattern("std", "std")).to_equal(true)
```

</details>

### arch_check: _is_import_allowed

#### allows import when no allow or deny rules

- allows import when no allow or deny rules
- Verify: allows import when no allow or deny rules
   - Expected: _is_import_allowed("app/io/mod", rule) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows import when no allow or deny rules")
step("Verify: allows import when no allow or deny rules")
val rule = ArchRule(
    init_file: "test/__init__.spl",
    module_path: "test",
    allow_patterns: [],
    deny_patterns: [],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("app/io/mod", rule)).to_equal(true)
```

</details>

#### denies import matching deny pattern

- denies import matching deny pattern
- Verify: denies import matching deny pattern
   - Expected: _is_import_allowed("compiler/backend", rule) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies import matching deny pattern")
step("Verify: denies import matching deny pattern")
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: ["compiler/**"],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("compiler/backend", rule)).to_equal(false)
```

</details>

#### allows import not matching deny pattern

- allows import not matching deny pattern
- Verify: allows import not matching deny pattern
   - Expected: _is_import_allowed("core/ast", rule) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows import not matching deny pattern")
step("Verify: allows import not matching deny pattern")
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: ["compiler/**"],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("core/ast", rule)).to_equal(true)
```

</details>

#### allows import matching allow pattern

- allows import matching allow pattern
- Verify: allows import matching allow pattern
   - Expected: _is_import_allowed("core/ast", rule) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows import matching allow pattern")
step("Verify: allows import matching allow pattern")
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**", "std/**"],
    deny_patterns: [],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("core/ast", rule)).to_equal(true)
```

</details>

#### denies import not matching allow pattern

- denies import not matching allow pattern
- Verify: denies import not matching allow pattern
   - Expected: _is_import_allowed("app/io", rule) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies import not matching allow pattern")
step("Verify: denies import not matching allow pattern")
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**", "std/**"],
    deny_patterns: [],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("app/io", rule)).to_equal(false)
```

</details>

#### deny takes precedence over allow

- deny takes precedence over allow
- Verify: deny takes precedence over allow
   - Expected: _is_import_allowed("core/compiler/backend", rule) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deny takes precedence over allow")
step("Verify: deny takes precedence over allow")
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: ["core/compiler/**"],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("core/compiler/backend", rule)).to_equal(false)
```

</details>

#### allows core/ast when core allowed and core/compiler denied

- allows core/ast when core allowed and core/compiler denied
- Verify: allows core/ast when core allowed and core/compiler denied
   - Expected: _is_import_allowed("core/ast", rule) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows core/ast when core allowed and core/compiler denied")
step("Verify: allows core/ast when core allowed and core/compiler denied")
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: ["core/compiler/**"],
    dimension: "",
    transform_allow_from: []
)
expect(_is_import_allowed("core/ast", rule)).to_equal(true)
```

</details>

### arch_check: _file_is_under_module

#### returns true for file under module path

- returns true for file under module path
- Verify: returns true for file under module path
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for file under module path")
step("Verify: returns true for file under module path")
val file = "/project/src/compiler/10.frontend/core/entity/ast.spl"
val result = _file_is_under_module(file, "src/compiler/10.frontend/core/entity", "/project")
expect(result).to_equal(true)
```

</details>

#### returns false for file not under module path

- returns false for file not under module path
- Verify: returns false for file not under module path
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for file not under module path")
step("Verify: returns false for file not under module path")
val file = "/project/src/compiler/70.backend/backend.spl"
val result = _file_is_under_module(file, "src/compiler/10.frontend/core/entity", "/project")
expect(result).to_equal(false)
```

</details>

#### returns true for empty module path (matches all)

- returns true for empty module path (matches all)
- Verify: returns true for empty module path (matches all)
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for empty module path (matches all)")
step("Verify: returns true for empty module path (matches all)")
val file = "/project/src/anything/file.spl"
val result = _file_is_under_module(file, "", "/project")
expect(result).to_equal(true)
```

</details>

### arch_check: _infer_dimension_from_file

#### infers feature from feature/ directory

- infers feature from feature/ directory
- Verify: infers feature from feature/ directory
   - Expected: result equals `feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers feature from feature/ directory")
step("Verify: infers feature from feature/ directory")
val result = _infer_dimension_from_file("/project/src/feature/Auth/Login.spl", "/project")
expect(result).to_equal("feature")
```

</details>

#### infers entity from entity/ directory

- infers entity from entity/ directory
- Verify: infers entity from entity/ directory
   - Expected: result equals `entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers entity from entity/ directory")
step("Verify: infers entity from entity/ directory")
val result = _infer_dimension_from_file("/project/src/entity/Identity/User.spl", "/project")
expect(result).to_equal("entity")
```

</details>

#### infers transform from transform/ directory

- infers transform from transform/ directory
- Verify: infers transform from transform/ directory
   - Expected: result equals `transform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers transform from transform/ directory")
step("Verify: infers transform from transform/ directory")
val result = _infer_dimension_from_file("/project/src/transform/Auth/LoginFlow.spl", "/project")
expect(result).to_equal("transform")
```

</details>

#### returns unknown for compiler/core/ directory

- returns unknown for compiler/core/ directory
- Verify: returns unknown for compiler/core/ directory
   - Expected: result equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for compiler/core/ directory")
step("Verify: returns unknown for compiler/core/ directory")
val result = _infer_dimension_from_file("/project/src/compiler/10.frontend/core/parser.spl", "/project")
expect(result).to_equal("unknown")
```

</details>

#### returns unknown for app/ directory

- returns unknown for app/ directory
- Verify: returns unknown for app/ directory
   - Expected: result equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for app/ directory")
step("Verify: returns unknown for app/ directory")
val result = _infer_dimension_from_file("/project/src/app/cli/main.spl", "/project")
expect(result).to_equal("unknown")
```

</details>

#### infers correct dimension for deeply nested path

- infers correct dimension for deeply nested path
- Verify: infers correct dimension for deeply nested path
   - Expected: result equals `entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers correct dimension for deeply nested path")
step("Verify: infers correct dimension for deeply nested path")
val result = _infer_dimension_from_file("/project/src/entity/User/Profile/Address.spl", "/project")
expect(result).to_equal("entity")
```

</details>

### arch_check: _infer_dimension_from_import

#### infers feature from feature/ prefix

- infers feature from feature/ prefix
- Verify: infers feature from feature/ prefix
   - Expected: _infer_dimension_from_import("feature/Auth/login") equals `feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers feature from feature/ prefix")
step("Verify: infers feature from feature/ prefix")
expect(_infer_dimension_from_import("feature/Auth/login")).to_equal("feature")
```

</details>

#### infers entity from entity/ prefix

- infers entity from entity/ prefix
- Verify: infers entity from entity/ prefix
   - Expected: _infer_dimension_from_import("entity/Identity/user") equals `entity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers entity from entity/ prefix")
step("Verify: infers entity from entity/ prefix")
expect(_infer_dimension_from_import("entity/Identity/user")).to_equal("entity")
```

</details>

#### infers transform from transform/ prefix

- infers transform from transform/ prefix
- Verify: infers transform from transform/ prefix
   - Expected: _infer_dimension_from_import("transform/Auth/flow") equals `transform`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers transform from transform/ prefix")
step("Verify: infers transform from transform/ prefix")
expect(_infer_dimension_from_import("transform/Auth/flow")).to_equal("transform")
```

</details>

#### returns unknown for std/ prefix

- returns unknown for std/ prefix
- Verify: returns unknown for std/ prefix
   - Expected: _infer_dimension_from_import("std/text") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for std/ prefix")
step("Verify: returns unknown for std/ prefix")
expect(_infer_dimension_from_import("std/text")).to_equal("unknown")
```

</details>

#### returns unknown for bare module name

- returns unknown for bare module name
- Verify: returns unknown for bare module name
   - Expected: _infer_dimension_from_import("core/ast") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for bare module name")
step("Verify: returns unknown for bare module name")
expect(_infer_dimension_from_import("core/ast")).to_equal("unknown")
```

</details>

### arch_check: _dim_allows_import

#### feature cannot import entity

- feature cannot import entity
- Verify: feature cannot import entity
   - Expected: _dim_allows_import("feature", "entity") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("feature cannot import entity")
step("Verify: feature cannot import entity")
expect(_dim_allows_import("feature", "entity")).to_equal(false)
```

</details>

#### feature can import transform

- feature can import transform
- Verify: feature can import transform
   - Expected: _dim_allows_import("feature", "transform") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("feature can import transform")
step("Verify: feature can import transform")
expect(_dim_allows_import("feature", "transform")).to_equal(true)
```

</details>

#### entity cannot import feature

- entity cannot import feature
- Verify: entity cannot import feature
   - Expected: _dim_allows_import("entity", "feature") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entity cannot import feature")
step("Verify: entity cannot import feature")
expect(_dim_allows_import("entity", "feature")).to_equal(false)
```

</details>

#### entity cannot import transform

- entity cannot import transform
- Verify: entity cannot import transform
   - Expected: _dim_allows_import("entity", "transform") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entity cannot import transform")
step("Verify: entity cannot import transform")
expect(_dim_allows_import("entity", "transform")).to_equal(false)
```

</details>

#### entity can import entity

- entity can import entity
- Verify: entity can import entity
   - Expected: _dim_allows_import("entity", "entity") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entity can import entity")
step("Verify: entity can import entity")
expect(_dim_allows_import("entity", "entity")).to_equal(true)
```

</details>

#### transform cannot import feature

- transform cannot import feature
- Verify: transform cannot import feature
   - Expected: _dim_allows_import("transform", "feature") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform cannot import feature")
step("Verify: transform cannot import feature")
expect(_dim_allows_import("transform", "feature")).to_equal(false)
```

</details>

#### transform can import entity

- transform can import entity
- Verify: transform can import entity
   - Expected: _dim_allows_import("transform", "entity") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform can import entity")
step("Verify: transform can import entity")
expect(_dim_allows_import("transform", "entity")).to_equal(true)
```

</details>

#### unknown dimension allows any import

- unknown dimension allows any import
- Verify: unknown dimension allows any import
   - Expected: _dim_allows_import("unknown", "entity") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown dimension allows any import")
step("Verify: unknown dimension allows any import")
expect(_dim_allows_import("unknown", "entity")).to_equal(true)
```

</details>

#### any import from unknown dimension is allowed

- any import from unknown dimension is allowed
- Verify: any import from unknown dimension is allowed
   - Expected: _dim_allows_import("feature", "unknown") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("any import from unknown dimension is allowed")
step("Verify: any import from unknown dimension is allowed")
expect(_dim_allows_import("feature", "unknown")).to_equal(true)
```

</details>

### arch_check: _arch_explicitly_allows

#### returns true when applicable rule allows the import

- returns true when applicable rule allows the import
- Verify: returns true when applicable rule allows the import
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when applicable rule allows the import")
step("Verify: returns true when applicable rule allows the import")
val rule = ArchRule(
    init_file: "/project/src/feature/Auth/__init__.spl",
    module_path: "src/feature/Auth",
    allow_patterns: ["entity/Identity/**"],
    deny_patterns: [],
    dimension: "feature",
    transform_allow_from: []
)
val rules: [ArchRule] = [rule]
val result = _arch_explicitly_allows(
    "entity/Identity/User",
    rules,
    "/project/src/feature/Auth/Login.spl",
    "/project"
)
expect(result).to_equal(true)
```

</details>

#### returns false when rule does not match the import

- returns false when rule does not match the import
- Verify: returns false when rule does not match the import
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when rule does not match the import")
step("Verify: returns false when rule does not match the import")
val rule = ArchRule(
    init_file: "/project/src/feature/Auth/__init__.spl",
    module_path: "src/feature/Auth",
    allow_patterns: ["entity/Identity/**"],
    deny_patterns: [],
    dimension: "feature",
    transform_allow_from: []
)
val rules: [ArchRule] = [rule]
val result = _arch_explicitly_allows(
    "entity/Other/Data",
    rules,
    "/project/src/feature/Auth/Login.spl",
    "/project"
)
expect(result).to_equal(false)
```

</details>

#### returns false when no rules exist

- returns false when no rules exist
- Verify: returns false when no rules exist
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no rules exist")
step("Verify: returns false when no rules exist")
val rules: [ArchRule] = []
val result = _arch_explicitly_allows(
    "entity/Identity/User",
    rules,
    "/project/src/feature/Auth/Login.spl",
    "/project"
)
expect(result).to_equal(false)
```

</details>

### arch_check: implementation file exists

#### arch_check.spl source file exists

- arch_check.spl source file exists
- Verify: arch_check.spl source file exists
   - Expected: result.stdout.trim() equals `yes`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arch_check.spl source file exists")
step("Verify: arch_check.spl source file exists")
val result = shell("test -f src/app/cli/arch_check.spl && echo yes")
expect(result.stdout.trim()).to_equal("yes")

val capture = UntypedCapture(label: "arch-check-file-exists-stdout", raw_value: result.stdout, source_kind: "stdout")
val evidence = untyped_capture_to_canonical(capture, "arch_check_spec/file-exists-stdout")
val comparison = compare_evidence(evidence, oracle_spec("arch_check_spec/file-exists-stdout", [
    check_exact("value", "yes\n")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

#### check-arch is wired in main.spl

- check-arch is wired in main.spl
- Verify: check-arch is wired in main.spl
   - Expected: count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check-arch is wired in main.spl")
step("Verify: check-arch is wired in main.spl")
val result = shell("grep -rc 'check-arch' src/app/cli/main.spl src/app/cli/_CliMain/main_and_help.spl 2>/dev/null | awk -F: '{s+=$2} END {print s}'")
val trimmed = result.stdout.trim()
val count = int(trimmed)
expect(count > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 74 |
| Active scenarios | 74 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-ARCH-CHECK-STR-TRIM-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e95db8dabf11974ae5d8a4b7342e88e31cfa87c7cc2658fce923c23156682f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e95db8dabf11974ae5d8a4b7342e88e31cfa87c7cc2658fce923c23156682f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e95db8dabf11974ae5d8a4b7342e88e31cfa87c7cc2658fce923c23156682f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/arch_check_spec.spl
mirror: doc/06_spec/unit/app/arch_check_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/arch_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/arch_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/arch_check_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/arch_check_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims leading spaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/arch_check_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims trailing spaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/arch_check_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
