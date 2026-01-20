# Doctest README.md Specification

**Version:** 1.0
**Status:** Draft
**Date:** 2025-01-09

---

## Overview

README.md files serve as doctest configuration, similar to CMakeLists.txt for CMake. Each README.md defines which subdirectories and files should be scanned for doctests within its directory scope.

### Design Principles

1. **Natural markdown** - Links render as navigation
2. **Exclude at front** - Fast parsing, invisible in render
3. **Section-based** - Clear separation of subdirs and files
4. **Hierarchical** - Each README.md controls its subtree

---

## File Structure

```markdown
<!--doctest:exclude
<pattern>
<pattern>
...
-->

<!--doctest:config
<key>: <value>
...
-->

# <Title>

## Subdirectory

- [<Name>](<dir>/)
- [<Name>](<dir>/)

## Files

- [<Name>](<file>.md)
- [<Name>](<file>.md)

---

<regular documentation content>
```

---

## Front Matter

Front matter MUST appear at the beginning of the file, before any markdown content. It consists of invisible HTML comments.

### Exclude Block

Specifies paths to exclude from doctest discovery.

**Syntax:**
```markdown
<!--doctest:exclude
<pattern>
<pattern>
...
-->
```

**Rules:**
- MUST be first non-whitespace content in file (if present)
- One pattern per line
- Empty lines and lines starting with `#` are ignored
- Patterns are relative to the README.md directory

**Pattern Syntax:**

| Pattern | Matches |
|---------|---------|
| `dirname/` | Directory named "dirname" |
| `*.draft.md` | Files ending in ".draft.md" |
| `**/*.md` | All .md files recursively |
| `dir/**` | Everything under "dir/" |
| `*_WIP.md` | Files ending in "_WIP.md" |
| `!pattern` | Negate (un-exclude) a pattern |

**Example:**
```markdown
<!--doctest:exclude
drafts/
archive/
*_DRAFT.md
*_WIP.md
internal/**
-->
```

### Config Block

Specifies doctest configuration options.

**Syntax:**
```markdown
<!--doctest:config
<key>: <value>
...
-->
```

**Supported Keys:**

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `lang` | string | `simple` | Default language for untagged code blocks |
| `timeout` | int | `5000` | Timeout in milliseconds per doctest |
| `disabled` | bool | `false` | Disable all doctests in this scope |
| `inherit` | bool | `true` | Inherit parent config |

**Example:**
```markdown
<!--doctest:config
lang: simple
timeout: 10000
-->
```

**Shorthand** (single config):
```markdown
<!--doctest:lang simple-->
<!--doctest:timeout 10000-->
<!--doctest:disabled-->
```

---

## Doctest Sections

### Section: `## Subdirectory`

Lists directories to recursively scan. Each listed directory MUST contain a README.md file.

**Syntax:**
```markdown
## Subdirectory

- [<Display Name>](<directory>/)
```

**Rules:**
- Links MUST end with `/` to indicate directory
- Directory MUST contain README.md
- Links are relative to current README.md location
- Standard markdown link syntax: `[Text>(path/)`

**Example:**
```markdown
## Subdirectory

- [Language Spec>(spec/)
- [Developer Guides>(guides/)
- [Tutorials>(tutorials/)
```

### Section: `## Files`

Lists individual markdown files to scan for doctests.

**Syntax:**
```markdown
## Files

- [<Display Name>](<filename>.md)
```

**Rules:**
- Links MUST NOT end with `/`
- Links are relative to current README.md location
- Files must have `.md` extension
- Standard markdown link syntax: `[Text>(file.md)`

**Example:**
```markdown
## Files

- [API Reference>(api_reference.md)
- [Feature Index>(feature_index.md)
- [Getting Started>(getting_started.md)
```

### Section Termination

Doctest sections end when:
1. A horizontal rule `---` is encountered
2. A heading not matching `## Subdirectory` or `## Files` is encountered
3. End of file is reached

---

## Link Format

### Valid Link Formats

| Format | Type | Example |
|--------|------|---------|
| `[Name>(dir/)` | Subdirectory | `[Spec>(spec/)` |
| `[Name>(file.md)` | File | `[API>(api.md)` |
| `[Name>(sub/dir/)` | Nested subdir | `[Testing>(spec/testing/)` |
| `[Name>(sub/file.md)` | Nested file | `[Types>(spec/types.md)` |

### Ignored Links

| Format | Reason |
|--------|--------|
| `[Name>(https://...)` | External URL |
| `[Name>(#anchor)` | Internal anchor |
| `[Name>(mailto:...)` | Email link |
| `[Name>()` | Empty href |

---

## Discovery Algorithm

```
FUNCTION discover(root_path) -> List<DoctestFile>:
    readme = root_path / "README.md"
    IF NOT readme.exists():
        RETURN []

    config = parse_front_matter(readme)
    results = []

    # Add current README if it has doctests
    IF has_code_blocks(readme):
        results.append(DoctestFile(readme, config))

    # Process ## Subdirectory section
    FOR link IN parse_subdirectory_section(readme):
        subdir = root_path / link.path
        IF is_excluded(subdir, config.excludes):
            CONTINUE
        IF NOT (subdir / "README.md").exists():
            WARN "Subdirectory {subdir} missing README.md"
            CONTINUE
        results.extend(discover(subdir))

    # Process ## Files section
    FOR link IN parse_files_section(readme):
        file = root_path / link.path
        IF is_excluded(file, config.excludes):
            CONTINUE
        IF NOT file.exists():
            WARN "File {file} not found"
            CONTINUE
        file_config = merge_config(config, parse_front_matter(file))
        results.append(DoctestFile(file, file_config))

    RETURN results
```

---

## Parsing Rules

### Order of Parsing

1. **Exclude block** - First `<!--doctest:exclude ... -->`
2. **Config block** - First `<!--doctest:config ... -->`
3. **Subdirectory section** - `## Subdirectory` heading and links
4. **Files section** - `## Files` heading and links

### Fast Parsing Mode

For performance, parsers MAY use fast parsing:

1. Read file until `---` or first non-doctest heading
2. Extract only front matter and doctest sections
3. Skip remaining file content

### Link Extraction Regex

```
LINK_PATTERN = r'^\s*[-*]\s*\[([^\]]+)\]\(([^)]+)\)\s*$'

Match groups:
  1: Display name
  2: Path (with or without trailing /)
```

---

## Code Block Language

### Default Language

Untagged code blocks use the `lang` config value (default: `simple`).

````markdown
```
fn add(a: Int, b: Int) -> Int:
    return a + b
```
````

Treated as Simple code.

### Explicit Language

````markdown
```simple
fn add(a: Int, b: Int) -> Int:
    return a + b
```
````

### Skip Doctest

````markdown
```simple:skip
# This code is not tested
fn untested():
    pass
```
````

### Language Modifiers

| Tag | Behavior |
|-----|----------|
| `simple` | Test as Simple code |
| `simple:skip` | Skip this block |
| `simple:ignore-output` | Run but don't check output |
| `simple:should-fail` | Expect compilation/runtime error |
| `rust`, `python`, etc. | Not tested by Simple doctest |

---

## Config Inheritance

Child README.md files inherit parent config unless `inherit: false`.

```
doc/README.md          # lang: simple, timeout: 5000
├── spec/README.md     # inherits: lang: simple, timeout: 5000
│   └── testing/README.md  # inherits from spec/
└── guides/README.md   # timeout: 10000 (override)
```

### Merge Rules

| Key | Merge Behavior |
|-----|----------------|
| `lang` | Override |
| `timeout` | Override |
| `disabled` | Override |
| `excludes` | Append to parent |

---

## Complete Example

### doc/README.md

```markdown
<!--doctest:exclude
report/
drafts/
plans/
*_DRAFT.md
*_WIP.md
-->

<!--doctest:config
lang: simple
timeout: 5000
-->

# Simple Language Documentation

## Subdirectory

- [Language Specification>(spec/)
- [Developer Guides>(guides/)
- [Tutorials>(tutorials/)

## Files

- [Feature Index>(feature_index.md)
- [API Reference>(api_reference.md)
- [FAQ>(faq.md)

---

## Welcome

Welcome to Simple language documentation.

## Quick Example

```
fn greet(name: String) -> String:
    return "Hello, {name}!"

# doctest
assert greet("World") == "Hello, World!"
```
```

### doc/spec/README.md

```markdown
<!--doctest:exclude
gpu_simd/
graphics_3d/
-->

# Language Specification

## Subdirectory

- [Testing>(testing/)
- [Tooling>(tooling/)

## Files

- [Syntax>(syntax.md)
- [Types>(types.md)
- [Functions>(functions.md)
- [Memory>(memory.md)
- [Concurrency>(concurrency.md)

---

## Overview

This section contains formal language specifications.
```

### doc/spec/syntax.md

```markdown
<!--doctest:config
timeout: 3000
-->

# Syntax Specification

## String Literals

All double-quoted strings support interpolation:

```
let name = "World"
let greeting = "Hello, {name}!"

# doctest
assert greeting == "Hello, World!"
```

## Raw Strings

Single-quoted strings have no interpolation:

```
let raw = 'Hello, {name}!'

# doctest
assert raw == "Hello, {name}!"
```
```

---

## Error Handling

### Missing README.md in Subdirectory

```
WARNING: Subdirectory 'spec/gpu_simd/' listed but contains no README.md
         Skipping subdirectory.
```

### Missing Linked File

```
WARNING: File 'api_reference.md' listed but not found
         Skipping file.
```

### Invalid Link Format

```
WARNING: Invalid link format in ## Subdirectory section:
         '- Invalid link without proper markdown'
         Expected: '- [Name>(path/)'
```

---

## Grammar (EBNF)

```ebnf
readme_file     = front_matter? title doctest_sections? content? ;

front_matter    = exclude_block? config_block? ;
exclude_block   = "<!--doctest:exclude" newline pattern_list "-->" ;
config_block    = "<!--doctest:config" newline config_list "-->" ;
config_shorthand = "<!--doctest:" key value? "-->" ;

pattern_list    = (pattern newline)* ;
pattern         = glob_pattern | "!" glob_pattern ;

config_list     = (config_entry newline)* ;
config_entry    = key ":" value ;

title           = "#" text newline ;

doctest_sections = subdirectory_section? files_section? section_end ;
subdirectory_section = "## Subdirectory" newline link_list ;
files_section   = "## Files" newline link_list ;
section_end     = "---" | heading | EOF ;

link_list       = (link_item newline)* ;
link_item       = "-" "[" text "]" "(" path ")" ;

heading         = "#"+ text newline ;
content         = .* ;
```

---

## Implementation Notes

### File System Layout

```
doc/
├── README.md              # Root doctest config
├── feature_index.md       # Linked file
├── spec/
│   ├── README.md          # Subdir config
│   ├── syntax.md          # Linked file
│   └── testing/
│       ├── README.md      # Nested subdir config
│       └── sdoctest.md    # Linked file
└── guides/
    ├── README.md          # Subdir config
    └── getting_started.md # Linked file
```

### Runner Command

```bash
# Run doctests starting from doc/
simple doctest doc/

# Run doctests for specific subdirectory
simple doctest doc/spec/

# Run with verbose output
simple doctest doc/ --verbose

# Dry run (list files only)
simple doctest doc/ --dry-run
```

---

## Changelog

- **1.0** (2025-01-09): Initial specification
