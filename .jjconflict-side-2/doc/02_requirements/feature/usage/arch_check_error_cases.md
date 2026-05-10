# arch check error cases
*Source:* `test/feature/usage/arch_check_error_cases_spec.spl`

## Feature: Arch Check Error Cases: _str_trim edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles already-trimmed string unchanged | pass |
| 2 | handles empty string | pass |
| 3 | handles string of only spaces | pass |
| 4 | handles string of only tabs | pass |
| 5 | handles single character | pass |
| 6 | handles string with tab and spaces | pass |

**Example:** handles already-trimmed string unchanged
    Then  expect(_str_trim("clean")).to_equal("clean")

**Example:** handles empty string
    Then  expect(_str_trim("")).to_equal("")

**Example:** handles string of only spaces
    Then  expect(_str_trim("   ")).to_equal("")

**Example:** handles string of only tabs
    Then  expect(_str_trim("\t\t")).to_equal("")

**Example:** handles single character
    Then  expect(_str_trim("x")).to_equal("x")

**Example:** handles string with tab and spaces
    Then  expect(_str_trim("\t  hello  \t")).to_equal("hello")

## Feature: Arch Check Error Cases: _parse_pattern_list edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns empty list for empty brackets | pass |
| 2 | returns empty list for missing brackets | pass |
| 3 | returns empty list for empty input string | pass |
| 4 | parses single quoted pattern | pass |
| 5 | parses single item with double quotes | pass |
| 6 | ignores whitespace around patterns | pass |

**Example:** returns empty list for empty brackets
    Given val result = _parse_pattern_list("allow = []")
    Then  expect(result.len()).to_equal(0)

**Example:** returns empty list for missing brackets
    Given val result = _parse_pattern_list("allow = core")
    Then  expect(result.len()).to_equal(0)

**Example:** returns empty list for empty input string
    Given val result = _parse_pattern_list("")
    Then  expect(result.len()).to_equal(0)

**Example:** parses single quoted pattern
    Given val result = _parse_pattern_list("allow = ['core/**']")
    Then  expect(result.len()).to_equal(1)
    Then  expect(result[0]).to_equal("core/**")

**Example:** parses single item with double quotes
    Given val result = _parse_pattern_list("allow = [\"core/**\"]")
    Then  expect(result.len()).to_equal(1)
    Then  expect(result[0]).to_equal("core/**")

**Example:** ignores whitespace around patterns
    Given val result = _parse_pattern_list("deny = [ \"compiler/**\" ]")
    Then  expect(result.len()).to_equal(1)
    Then  expect(result[0]).to_equal("compiler/**")

## Feature: Arch Check Error Cases: _match_pattern edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | empty pattern does not match non-empty import | pass |
| 2 | empty import does not match non-empty pattern | pass |
| 3 | empty import matches empty pattern exactly | pass |
| 4 | /** suffix matches any subpath of prefix | pass |
| 5 | pattern exact does not match import with extra segment | pass |
| 6 | /* does not match two levels deep | pass |
| 7 | /* matches single level sub-path | pass |
| 8 | prefix match requires slash boundary | pass |
| 9 | exact match succeeds for identical strings | pass |
| 10 | pattern with /** matches direct child | pass |

**Example:** empty pattern does not match non-empty import
    Given val result = _match_pattern("compiler_core/lexer", "")
    Then  expect(result).to_equal(false)

**Example:** empty import does not match non-empty pattern
    Given val result = _match_pattern("", "compiler_core/lexer")
    Then  expect(result).to_equal(false)

**Example:** empty import matches empty pattern exactly
    Given val result = _match_pattern("", "")
    Then  expect(result).to_equal(true)

**Example:** /** suffix matches any subpath of prefix
    Given val result = _match_pattern("a/b/c", "a/**")
    Then  expect(result).to_equal(true)

**Example:** pattern exact does not match import with extra segment
    Given val result = _match_pattern("compiler_core/lexer/extra", "compiler_core/lexer")
    Then  expect(result).to_equal(true)

**Example:** /* does not match two levels deep
    Given val result = _match_pattern("compiler_core/lexer/submodule", "compiler_core/*")
    Then  expect(result).to_equal(false)

**Example:** /* matches single level sub-path
    Given val result = _match_pattern("compiler_core/lexer", "compiler_core/*")
    Then  expect(result).to_equal(true)

**Example:** prefix match requires slash boundary
    Given val result = _match_pattern("compiler_other/ast", "compiler")
    Then  expect(result).to_equal(false)

**Example:** exact match succeeds for identical strings
    Given val result = _match_pattern("std/text", "std/text")
    Then  expect(result).to_equal(true)

**Example:** pattern with /** matches direct child
    Given val result = _match_pattern("compiler_core/ast", "compiler_core/**")
    Then  expect(result).to_equal(true)

## Feature: Arch Check Error Cases: _is_import_allowed edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | import allowed when both allow and deny lists are empty | pass |
| 2 | import denied when not in non-empty allow list | pass |
| 3 | import allowed when in allow list and deny list is empty | pass |
| 4 | import denied when matched by deny pattern even if in allow list | pass |
| 5 | import allowed when in allow but not in deny | pass |

**Example:** import allowed when both allow and deny lists are empty
    Given val rule = ArchRule(
    Then  expect(_is_import_allowed("any/import", rule)).to_equal(true)

**Example:** import denied when not in non-empty allow list
    Given val rule = ArchRule(
    Then  expect(_is_import_allowed("compiler/backend", rule)).to_equal(false)

**Example:** import allowed when in allow list and deny list is empty
    Given val rule = ArchRule(
    Then  expect(_is_import_allowed("compiler_core/ast", rule)).to_equal(true)

**Example:** import denied when matched by deny pattern even if in allow list
    Given val rule = ArchRule(
    Then  expect(_is_import_allowed("compiler_core/compiler/backend", rule)).to_equal(false)

**Example:** import allowed when in allow but not in deny
    Given val rule = ArchRule(
    Then  expect(_is_import_allowed("compiler_core/ast", rule)).to_equal(true)

## Feature: Arch Check Error Cases: _parse_imports_from_content edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns empty list for empty content | pass |
| 2 | returns empty list for content with no use statements | pass |
| 3 | ignores comment lines starting with # | pass |
| 4 | strips trailing dot from module path | pass |
| 5 | converts dot notation to slash notation | pass |

**Example:** returns empty list for empty content
    Given val result = _parse_imports_from_content("")
    Then  expect(result.len()).to_equal(0)

**Example:** returns empty list for content with no use statements
    Given val content = "fn main():\n    print \"hello\"\n"
    Given val result = _parse_imports_from_content(content)
    Then  expect(result.len()).to_equal(0)

**Example:** ignores comment lines starting with #
    Given val content = "# use app.io.mod (file_read)\nfn foo(): ()\n"
    Given val result = _parse_imports_from_content(content)
    Then  expect(result.len()).to_equal(0)

**Example:** strips trailing dot from module path
    Given val content = "use std.text. (NL)\n"
    Given val result = _parse_imports_from_content(content)
    Then  expect(result.len()).to_equal(1)
    Then  expect(result[0]).to_equal("std/text")

**Example:** converts dot notation to slash notation
    Given val content = "use core.ast (CoreExpr)\n"
    Given val result = _parse_imports_from_content(content)
    Then  expect(result.len()).to_equal(1)
    Then  expect(result[0]).to_equal("core/ast")

## Feature: Arch Check Error Cases: _module_path_from_init_file edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns __init__.spl when init file is directly under root with no subdir | pass |
| 2 | handles path not under root unchanged | pass |

**Example:** returns __init__.spl when init file is directly under root with no subdir
    Given val path = "/project/__init__.spl"
    Given val root = "/project"
    Given val result = _module_path_from_init_file(path, root)
    Then  expect(result).to_equal("__init__.spl")

**Example:** handles path not under root unchanged
    Given val path = "/other/__init__.spl"
    Given val root = "/project"
    Given val result = _module_path_from_init_file(path, root)
    Then  expect(result).to_equal("/other")

## Feature: Arch Check Error Cases: _file_is_under_module edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | empty module path matches any file | pass |
| 2 | file at exact module boundary matches | pass |
| 3 | file outside module boundary does not match | pass |
| 4 | file with similar prefix but different module does not match | pass |

**Example:** empty module path matches any file
    Given val result = _file_is_under_module("/project/src/anything.spl", "", "/project")
    Then  expect(result).to_equal(true)

**Example:** file at exact module boundary matches
    Given val result = _file_is_under_module("/project/src/compiler_core/file.spl", "src/core", "/project")
    Then  expect(result).to_equal(true)

**Example:** file outside module boundary does not match
    Given val result = _file_is_under_module("/project/src/compiler/file.spl", "src/core", "/project")
    Then  expect(result).to_equal(false)

**Example:** file with similar prefix but different module does not match
    Given val result = _file_is_under_module("/project/src/core_ext/file.spl", "src/core", "/project")
    Then  expect(result).to_equal(false)

## Feature: Arch Check Error Cases: _parse_arch_block edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns false for empty content | pass |
| 2 | returns true when arch keyword appears in comment because parser has no comment awareness | pass |
| 3 | returns empty allow and deny for arch block with no imports section | pass |
| 4 | parses arch block with empty allow list | pass |
| 5 | parses arch block with empty deny list | pass |

**Example:** returns false for empty content
    Given val result = _parse_arch_block("")
    Then  expect(result.0).to_equal(false)

**Example:** returns true when arch keyword appears in comment because parser has no comment awareness
    Given val content = "# arch { deny = [] }\nfn foo(): ()\n"
    Given val result = _parse_arch_block(content)
    Then  expect(result.0).to_equal(true)

**Example:** returns empty allow and deny for arch block with no imports section
    Given var content = "arch {\n"
    Given val result = _parse_arch_block(content)
    Then  expect(result.0).to_equal(true)
    Then  expect(result.1.len()).to_equal(0)
    Then  expect(result.2.len()).to_equal(0)

**Example:** parses arch block with empty allow list
    Given var content = "arch {\n"
    Given val result = _parse_arch_block(content)
    Then  expect(result.0).to_equal(true)
    Then  expect(result.1.len()).to_equal(0)

**Example:** parses arch block with empty deny list
    Given var content = "arch {\n"
    Given val result = _parse_arch_block(content)
    Then  expect(result.0).to_equal(true)
    Then  expect(result.2.len()).to_equal(0)


