# simple_grep - AST-aware Code Search

## Overview

Search Simple code with awareness of language constructs (functions, classes, imports, etc.).

## Usage

```bash
simple_grep "pattern" .                    # Basic text search
simple_grep --fn "parse" .                 # Find functions named "parse"
simple_grep --class "Handler" .            # Find classes named "Handler"
simple_grep --import "json" .              # Find imports of "json"
simple_grep --call "print" .               # Find calls to "print"
simple_grep --def "x" .                    # Find definitions of "x"
simple_grep --ref "x" .                    # Find references to "x"
```

## Options

| Flag | Description |
|------|-------------|
| `--fn <name>` | Search function definitions |
| `--class <name>` | Search class definitions |
| `--struct <name>` | Search struct definitions |
| `--enum <name>` | Search enum definitions |
| `--trait <name>` | Search trait definitions |
| `--import <name>` | Search import statements |
| `--call <name>` | Search function calls |
| `--def <name>` | Search all definitions |
| `--ref <name>` | Search all references |
| `-i, --ignore-case` | Case-insensitive search |
| `-l, --files-only` | Only print file names |
| `-c, --count` | Only print match count |
| `--json` | JSON output format |

## Output Format

### Default

```
src/parser/lexer.spl:42: fn parse_token(input: String) -> Token:
src/parser/parser.spl:156: fn parse_expression(tokens: List[Token]) -> Expr:
src/compiler_core/json.spl:23: fn parse(text: String) -> Result[Value, Error]:
```

### With Context (-A, -B, -C)

```
src/compiler_core/json.spl:
  21│ """Parse JSON text into a Value."""
  22│
  23│ fn parse(text: String) -> Result[Value, Error]:
  24│     let lexer = JsonLexer.new(text)
  25│     let parser = JsonParser.new(lexer)
```

### JSON

```json
{
  "matches": [
    {
      "file": "src/compiler_core/json.spl",
      "line": 23,
      "column": 4,
      "kind": "function",
      "name": "parse",
      "signature": "fn parse(text: String) -> Result[Value, Error]",
      "context": ["...", "fn parse...", "..."]
    }
  ],
  "count": 3
}
```

## Search Kinds

| Kind | Pattern | Matches |
|------|---------|---------|
| `--fn` | `fn <name>` | Function definitions |
| `--class` | `class <name>` | Class definitions |
| `--call` | `<name>(` | Function/method calls |
| `--import` | `import.*<name>` | Import statements |
| `--def` | All definitions | fn, class, struct, enum, let |
| `--ref` | All references | Variables, function calls |

## Implementation Notes

1. For basic search: line-by-line pattern matching
2. For AST-aware search: use regex patterns for declarations
3. Match patterns:
   - Function: `(pub\s+)?(async\s+)?fn\s+<name>\s*\(`
   - Class: `class\s+<name>`
   - Import: `import\s+.*<name>`
   - Call: `<name>\s*\(`

## Dependencies

- `native_fs_read_string` - File reading
- `sys_get_args` - Command-line arguments
- `core.regex` (optional) - Pattern matching

## Examples

```bash
# Find all async functions
$ simple_grep --fn "" . | grep "async fn"

# Find classes with "Handler" suffix
$ simple_grep --class "Handler" .

# Find all imports of json module
$ simple_grep --import "json" .

# Find all calls to print
$ simple_grep --call "print" .

# Count functions per file
$ simple_grep --fn "" . --count
```
