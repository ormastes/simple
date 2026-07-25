# Arch Check Specification

> <details>

<!-- sdn-diagram:id=arch_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arch_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arch_check_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arch_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 74 | 74 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arch Check Specification

## Scenarios

### arch_check: _str_trim

#### trims leading spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("  hello")
expect(result).to_equal("hello")
```

</details>

#### trims trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("hello  ")
expect(result).to_equal("hello")
```

</details>

#### trims both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("  hello world  ")
expect(result).to_equal("hello world")
```

</details>

#### returns unchanged string when no whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("hello")
expect(result).to_equal("hello")
```

</details>

#### returns empty string for all whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("   ")
expect(result).to_equal("")
```

</details>

### arch_check: _parse_pattern_list

#### parses single pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = [\"core\"]")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("core")
```

</details>

#### parses multiple patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = [\"core\", \"std\"]")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("core")
expect(result[1]).to_equal("std")
```

</details>

#### parses glob patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("deny = [\"compiler/**\", \"app.io\"]")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("compiler/**")
```

</details>

#### returns empty for missing brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = core")
expect(result.len()).to_equal(0)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("deny = []")
expect(result.len()).to_equal(0)
```

</details>

### arch_check: _parse_string_value

#### parses double-quoted value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_string_value("dimension = \"entity\"")
expect(result).to_equal("entity")
```

</details>

#### parses single-quoted value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_string_value("dimension = 'transform'")
expect(result).to_equal("transform")
```

</details>

#### returns empty when no equals sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_string_value("no equals here")
expect(result).to_equal("")
```

</details>

#### trims whitespace around value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_string_value("dimension =   \"feature\"  ")
expect(result).to_equal("feature")
```

</details>

### arch_check: _parse_arch_block

#### returns false when no arch block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "mod simple\nexport foo.*\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(false)
```

</details>

#### returns true when arch block exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  dimension = \"entity\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
```

</details>

#### parses allow patterns from imports block

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  dimension = \"transform\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.3).to_equal("transform")
```

</details>

#### parses transform allow_from

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/home/user/project/src/compiler/10.frontend/core/entity/__init__.spl"
val root = "/home/user/project"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src/compiler/10.frontend/core/entity")
```

</details>

#### handles top-level init file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/project/src/__init__.spl"
val root = "/project"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src")
```

</details>

#### handles deeply nested path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/root/src/compiler/10.frontend/feature/lexing/__init__.spl"
val root = "/root"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src/compiler/10.frontend/feature/lexing")
```

</details>

### arch_check: _parse_imports_from_content

#### extracts simple use statements

1. var content = "use app io mod
2. content = content + "fn main
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `app/io/mod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "use app.io.mod (file_read)\n"
content = content + "fn main():\n"
content = content + "    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("app/io/mod")
```

</details>

#### extracts multiple use statements

1. var content = "use app io mod
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `app/io/mod`
   - Expected: result[1] equals `std/text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "use app.io.mod (file_read)\n"
content = content + "use std.text.\n\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("app/io/mod")
expect(result[1]).to_equal("std/text")
```

</details>

#### converts dots to slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. content = content + "fn foo
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "# Comment\n"
content = content + "fn foo():\n"
content = content + "    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### handles use with wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use app.io.*\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("app/io")
```

</details>

### arch_check: _match_pattern

#### matches exact paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("core/ast", "core/ast")).to_equal(true)
```

</details>

#### does not match different paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("core/ast", "std/text")).to_equal(false)
```

</details>

#### matches glob with /** for sub-paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("compiler/feature/lexing", "compiler/**")).to_equal(true)
```

</details>

#### matches glob /** for direct child

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("compiler/backend", "compiler/**")).to_equal(true)
```

</details>

#### does not match sibling with /**

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("core/ast", "compiler/**")).to_equal(false)
```

</details>

#### matches prefix with / boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("compiler/backend/jit", "compiler/backend")).to_equal(true)
```

</details>

#### does not match partial prefix without boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("compiler_other/ast", "compiler")).to_equal(false)
```

</details>

#### matches exact with no subpath

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_match_pattern("std", "std")).to_equal(true)
```

</details>

### arch_check: _is_import_allowed

#### allows import when no allow or deny rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "/project/src/compiler/10.frontend/core/entity/ast.spl"
val result = _file_is_under_module(file, "src/compiler/10.frontend/core/entity", "/project")
expect(result).to_equal(true)
```

</details>

#### returns false for file not under module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "/project/src/compiler/70.backend/backend.spl"
val result = _file_is_under_module(file, "src/compiler/10.frontend/core/entity", "/project")
expect(result).to_equal(false)
```

</details>

#### returns true for empty module path (matches all)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "/project/src/anything/file.spl"
val result = _file_is_under_module(file, "", "/project")
expect(result).to_equal(true)
```

</details>

### arch_check: _infer_dimension_from_file

#### infers feature from feature/ directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _infer_dimension_from_file("/project/src/feature/Auth/Login.spl", "/project")
expect(result).to_equal("feature")
```

</details>

#### infers entity from entity/ directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _infer_dimension_from_file("/project/src/entity/Identity/User.spl", "/project")
expect(result).to_equal("entity")
```

</details>

#### infers transform from transform/ directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _infer_dimension_from_file("/project/src/transform/Auth/LoginFlow.spl", "/project")
expect(result).to_equal("transform")
```

</details>

#### returns unknown for compiler/core/ directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _infer_dimension_from_file("/project/src/compiler/10.frontend/core/parser.spl", "/project")
expect(result).to_equal("unknown")
```

</details>

#### returns unknown for app/ directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _infer_dimension_from_file("/project/src/app/cli/main.spl", "/project")
expect(result).to_equal("unknown")
```

</details>

#### infers correct dimension for deeply nested path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _infer_dimension_from_file("/project/src/entity/User/Profile/Address.spl", "/project")
expect(result).to_equal("entity")
```

</details>

### arch_check: _infer_dimension_from_import

#### infers feature from feature/ prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_infer_dimension_from_import("feature/Auth/login")).to_equal("feature")
```

</details>

#### infers entity from entity/ prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_infer_dimension_from_import("entity/Identity/user")).to_equal("entity")
```

</details>

#### infers transform from transform/ prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_infer_dimension_from_import("transform/Auth/flow")).to_equal("transform")
```

</details>

#### returns unknown for std/ prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_infer_dimension_from_import("std/text")).to_equal("unknown")
```

</details>

#### returns unknown for bare module name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_infer_dimension_from_import("core/ast")).to_equal("unknown")
```

</details>

### arch_check: _dim_allows_import

#### feature cannot import entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("feature", "entity")).to_equal(false)
```

</details>

#### feature can import transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("feature", "transform")).to_equal(true)
```

</details>

#### entity cannot import feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("entity", "feature")).to_equal(false)
```

</details>

#### entity cannot import transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("entity", "transform")).to_equal(false)
```

</details>

#### entity can import entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("entity", "entity")).to_equal(true)
```

</details>

#### transform cannot import feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("transform", "feature")).to_equal(false)
```

</details>

#### transform can import entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("transform", "entity")).to_equal(true)
```

</details>

#### unknown dimension allows any import

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("unknown", "entity")).to_equal(true)
```

</details>

#### any import from unknown dimension is allowed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dim_allows_import("feature", "unknown")).to_equal(true)
```

</details>

### arch_check: _arch_explicitly_allows

#### returns true when applicable rule allows the import

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("test -f src/app/cli/arch_check.spl && echo yes")
expect(result.stdout.trim()).to_equal("yes")
```

</details>

#### check-arch is wired in main.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("grep -rc 'check-arch' src/app/cli/main.spl src/app/cli/main_part2.spl 2>/dev/null | awk -F: '{s+=$2} END {print s}'")
val trimmed = result.stdout.trim()
val count = int(trimmed)
expect(count > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/arch_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- arch_check: _str_trim
- arch_check: _parse_pattern_list
- arch_check: _parse_string_value
- arch_check: _parse_arch_block
- arch_check: _module_path_from_init_file
- arch_check: _parse_imports_from_content
- arch_check: _match_pattern
- arch_check: _is_import_allowed
- arch_check: _file_is_under_module
- arch_check: _infer_dimension_from_file
- arch_check: _infer_dimension_from_import
- arch_check: _dim_allows_import
- arch_check: _arch_explicitly_allows
- arch_check: implementation file exists

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 74 |
| Active scenarios | 74 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
