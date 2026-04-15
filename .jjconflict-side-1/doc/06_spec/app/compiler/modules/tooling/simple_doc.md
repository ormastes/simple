# simple_doc - Documentation Generator

## Overview

Generates markdown documentation from Simple source files by extracting docstrings (`"""..."""`).

## Usage

```bash
simple_doc <file.spl>              # Print docs to stdout
simple_doc <directory>             # Generate docs for all .spl files
simple_doc <file.spl> -o docs/     # Output to directory
simple_doc <file.spl> --json       # Output as JSON
```

## Options

| Flag | Description |
|------|-------------|
| `-o, --output <dir>` | Output directory (default: stdout) |
| `--json` | Output as JSON instead of markdown |
| `--private` | Include private items (no `pub`) |
| `--no-source` | Don't include source links |

## Output Format

### Markdown (default)

```markdown
# module_name

Module-level docstring here.

## Functions

### `fn example(x: Int) -> String`

Function docstring here.

**Parameters:**
- `x: Int` - Parameter description

**Returns:** `String` - Return description

## Classes

### `class MyClass`

Class docstring here.

#### Fields
- `field1: Int` - Field description

#### Methods
- `fn method(self) -> Bool` - Method description
```

### JSON

```json
{
  "module": "module_name",
  "doc": "Module docstring",
  "functions": [
    {
      "name": "example",
      "signature": "fn example(x: Int) -> String",
      "doc": "Function docstring",
      "params": [{"name": "x", "type": "Int", "doc": "..."}],
      "returns": {"type": "String", "doc": "..."}
    }
  ],
  "classes": [...]
}
```

## Implementation Notes

1. Parse source file line-by-line (no AST needed initially)
2. Extract `"""..."""` docstrings before declarations
3. Parse function/class signatures with regex
4. Support `@param`, `@returns`, `@example` tags in docstrings

## Docstring Format

```simple
"""
Brief description on first line.

Longer description follows after blank line.

@param x: Description of parameter x
@param y: Description of parameter y
@returns: Description of return value
@raises ValueError: When input is invalid
@example:
    let result = example(42)
    assert result == "42"
"""
fn example(x: Int) -> String:
    return x.to_string()
```

## Dependencies

- `native_fs_read_string` - File reading
- `native_fs_exists` - File existence check
- `sys_get_args` - Command-line arguments

## Example

Input (`math.spl`):
```simple
"""
Math utilities for Simple programs.
"""

"""
Calculate the factorial of n.

@param n: Non-negative integer
@returns: n! (factorial)
@raises ValueError: If n < 0
"""
pub fn factorial(n: Int) -> Int:
    if n <= 1:
        return 1
    return n * factorial(n - 1)
```

Output:
```markdown
# math

Math utilities for Simple programs.

## Functions

### `pub fn factorial(n: Int) -> Int`

Calculate the factorial of n.

**Parameters:**
- `n: Int` - Non-negative integer

**Returns:** `Int` - n! (factorial)

**Raises:** `ValueError` - If n < 0
```
