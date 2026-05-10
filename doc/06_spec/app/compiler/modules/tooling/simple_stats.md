# simple_stats - Code Statistics

## Overview

Calculates code statistics for Simple source files: lines of code, functions, classes, etc.

## Usage

```bash
simple_stats <file.spl>            # Stats for single file
simple_stats <directory>           # Stats for all .spl files
simple_stats . --format table      # Table format (default)
simple_stats . --format json       # JSON format
simple_stats . --format csv        # CSV format
simple_stats . --detailed          # Show per-file breakdown
```

## Options

| Flag | Description |
|------|-------------|
| `--format <fmt>` | Output format: table, json, csv |
| `--detailed` | Show per-file breakdown |
| `--sort <field>` | Sort by: loc, functions, classes, file |
| `--exclude <pattern>` | Exclude files matching pattern |

## Metrics

| Metric | Description |
|--------|-------------|
| Files | Number of .spl files |
| LOC | Lines of code (non-blank, non-comment) |
| Blank | Blank lines |
| Comments | Comment lines |
| Total | Total lines |
| Functions | Number of `fn` declarations |
| Classes | Number of `class` declarations |
| Structs | Number of `struct` declarations |
| Enums | Number of `enum` declarations |
| Traits | Number of `trait` declarations |
| Imports | Number of `import` statements |

## Output Format

### Table (default)

```
Simple Code Statistics
======================

Files:      42
Total:      3,456 lines
  Code:     2,891 (83.6%)
  Blank:    342 (9.9%)
  Comments: 223 (6.5%)

Declarations:
  Functions: 156
  Classes:   23
  Structs:   12
  Enums:     8
  Traits:    5
  Imports:   89

Average per file:
  LOC: 68.8
  Functions: 3.7
```

### Detailed Table

```
File                          LOC  Blank  Comment  Fn  Class
------------------------------------------------------------
src/compiler_core/json.spl             456     45       23  12      2
src/compiler_core/collections.spl      312     32       18   8      3
src/parser/lexer.spl          234     28       15   6      1
...
------------------------------------------------------------
Total                        2891    342      223 156     23
```

### JSON

```json
{
  "summary": {
    "files": 42,
    "loc": 2891,
    "blank": 342,
    "comments": 223,
    "total": 3456,
    "functions": 156,
    "classes": 23,
    "structs": 12,
    "enums": 8,
    "traits": 5,
    "imports": 89
  },
  "files": [
    {
      "path": "src/compiler_core/json.spl",
      "loc": 456,
      "blank": 45,
      "comments": 23,
      "functions": 12,
      "classes": 2
    }
  ]
}
```

## Implementation Notes

1. Read files line-by-line
2. Count blank lines: `line.trim().is_empty()`
3. Count comments: `line.trim().starts_with("#")`
4. Count declarations with simple pattern matching:
   - `fn ` or `async fn ` → function
   - `class ` → class
   - `struct ` → struct
   - `enum ` → enum
   - `trait ` → trait
   - `import ` → import

## Dependencies

- `native_fs_read_string` - File reading
- `native_fs_exists` - File existence check
- `sys_get_args` - Command-line arguments

## Example

```bash
$ simple_stats simple/std_lib/src/

Simple Code Statistics
======================

Files:      67
Total:      8,234 lines
  Code:     6,891 (83.7%)
  Blank:    892 (10.8%)
  Comments: 451 (5.5%)

Declarations:
  Functions: 312
  Classes:   45
  Structs:   28
  Enums:     19
  Traits:    12
  Imports:   156
```
