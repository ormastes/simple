# simple_todo - TODO Tracker

## Overview

Extracts TODO, FIXME, HACK, XXX, and NOTE comments from Simple source files.

## Usage

```bash
simple_todo <file.spl>             # Show TODOs in file
simple_todo <directory>            # Show TODOs in all .spl files
simple_todo . --type TODO          # Only show TODO comments
simple_todo . --type FIXME,HACK    # Show FIXME and HACK
simple_todo . --json               # Output as JSON
simple_todo . --summary            # Show count summary only
```

## Options

| Flag | Description |
|------|-------------|
| `--type <types>` | Filter by type (comma-separated) |
| `--json` | Output as JSON |
| `--summary` | Show count summary only |
| `--sort priority` | Sort by priority (FIXME > TODO > HACK > NOTE) |
| `--sort file` | Sort by file (default) |
| `--sort line` | Sort by line number |

## Supported Tags

| Tag | Priority | Description |
|-----|----------|-------------|
| `FIXME` | 1 (High) | Bug or critical issue |
| `TODO` | 2 | Planned task |
| `HACK` | 3 | Temporary workaround |
| `XXX` | 3 | Needs attention |
| `NOTE` | 4 (Low) | Information for developers |

## Output Format

### Default (Text)

```
src/parser.spl:42: TODO: Add error recovery
src/parser.spl:156: FIXME: Handle edge case for empty input
src/lexer.spl:23: HACK: Workaround for unicode handling
src/main.spl:10: NOTE: This is the entry point

Summary: 2 TODO, 1 FIXME, 1 HACK, 1 NOTE (5 total)
```

### JSON

```json
{
  "items": [
    {
      "file": "src/parser.spl",
      "line": 42,
      "type": "TODO",
      "message": "Add error recovery",
      "priority": 2
    }
  ],
  "summary": {
    "TODO": 2,
    "FIXME": 1,
    "HACK": 1,
    "NOTE": 1,
    "total": 5
  }
}
```

## Implementation Notes

1. Read file line-by-line
2. Match pattern: `#\s*(TODO|FIXME|HACK|XXX|NOTE):?\s*(.*)$`
3. Also match: `//\s*(TODO|FIXME|...)` for inline comments
4. Track file path and line number
5. Sort and format output

## Pattern Matching

```simple
# TODO: This is a TODO comment
# FIXME: Critical bug here
# HACK: Temporary workaround
# XXX: Needs review
# NOTE: Important information

fn example():  # TODO: Refactor this
    pass
```

## Dependencies

- `native_fs_read_string` - File reading
- `native_fs_exists` - File existence check
- `sys_get_args` - Command-line arguments
- `core.regex` (optional) - Pattern matching

## Example

```bash
$ simple_todo simple/std_lib/src/

simple/std_lib/src/core/json.spl:45: TODO: Add streaming parser
simple/std_lib/src/core/json.spl:123: FIXME: Handle escaped quotes
simple/std_lib/src/io/fs.spl:67: TODO: Add async file watching
simple/std_lib/src/net/http.spl:89: HACK: Workaround for TLS

Summary: 2 TODO, 1 FIXME, 1 HACK (4 total)
```

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success, items found or no items |
| 1 | Error (file not found, etc.) |
| 2 | FIXME items found (with `--fail-on-fixme`) |
