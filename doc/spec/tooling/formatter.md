# Canonical Formatter Specification (#908-910)

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** High  
**Difficulty:** 2-3

## Overview

Canonical code formatter with "single correct style" (gofmt-style) that eliminates stylistic variance, making LLM output predictable and diffs meaningful.

## Motivation

**Problem:**
- LLMs generate code with varying styles
- Manual formatting is inconsistent
- Code reviews waste time on style debates
- Diffs show formatting noise instead of logic changes

**Solution:**
- One canonical style for all Simple code
- Automatic formatting with `simple fmt`
- Format-on-save integration
- No configuration options (opinionated)

## Features

### #908: `simple fmt` Command (Difficulty: 2)

**Basic Usage:**
```bash
# Format single file (in-place)
simple fmt app.spl

# Format entire directory
simple fmt src/

# Check without modifying (CI mode)
simple fmt --check app.spl

# Show diff instead of formatting
simple fmt --diff app.spl

# Format to stdout
simple fmt --stdout app.spl

# Multiple files
simple fmt app.spl lib.spl utils.spl
```

**Exit Codes:**
- `0` - No formatting needed (or successfully formatted)
- `1` - Files need formatting (`--check` mode)
- `2` - Syntax errors found

**Output:**
```
Formatted: app.spl
Formatted: lib.spl
✓ 2 files formatted
```

**Check Mode:**
```bash
simple fmt --check src/
Output:
  ✗ src/app.spl needs formatting
  ✗ src/lib.spl needs formatting
  ✓ src/utils.spl is correctly formatted
  
  2 files need formatting
Exit: 1
```

### #909: Single Correct Style (Difficulty: 3)

**Design Principles:**

1. **Opinionated** - No configuration options
2. **Consistent** - One style for all code
3. **Readable** - Optimized for humans
4. **Compact** - Minimize vertical space
5. **Predictable** - LLMs can learn the style

**Formatting Rules:**

**Indentation:**
```simple
# Always 4 spaces (no tabs)
fn example():
    if condition:
        do_something()
        do_another()
```

**Line Length:**
```simple
# Preferred: 100 characters
# Hard limit: 120 characters
# Break long lines intelligently
fn long_function(
    param1: String,
    param2: i64,
    param3: bool
) -> Result<Value>:
    ...
```

**Function Definitions:**
```simple
# Space after colon
fn calculate(x: i64, y: i64) -> i64:
    return x + y

# Long signatures wrap after opening paren
fn complex_function(
    param1: String,
    param2: i64,
    param3: Option<User>
) -> Result<Value, Error>:
    ...
```

**Control Flow:**
```simple
# No spaces inside parens
if condition:
    do_something()

# Space around operators
if x > 0 and y < 10:
    ...

# Multi-line conditions align at operator
if very_long_condition
   and another_condition
   or third_condition:
    ...
```

**Collections:**
```simple
# Short arrays inline
let nums = [1, 2, 3, 4]

# Long arrays wrap
let long_array = [
    "first",
    "second",
    "third",
    "fourth"
]

# Trailing comma on multi-line
let data = [
    item1,
    item2,
    item3,  # ← trailing comma
]
```

**Expressions:**
```simple
# Space around binary operators
let result = x + y * z

# No space for unary operators
let negative = -x
let not_value = !flag

# Chain method calls
user
    .validate()
    .save()
    .notify()
```

**Blank Lines:**
```simple
# One blank line between top-level items
fn first():
    ...

fn second():
    ...


# Two blank lines only before major sections
# First section

fn helper1():
    ...


# Second section

fn helper2():
    ...
```

**Comments:**
```simple
# Comments on their own line
# (not trailing)
fn example():
    # Good: comment above
    let x = 42
    
    # Bad (reformatted):
    # let y = 24  # inline comment
    # becomes:
    # inline comment
    let y = 24
```

**Imports:**
```simple
# Sorted alphabetically
use core.io
use core.math
use std.collections
use std.text

# Grouped by prefix (stdlib, external, local)
use std.io
use std.math

use http.client
use json.parser

use app.models
use app.utils
```

### #910: Format-on-Save Integration (Difficulty: 2)

**Editor Integration:**

**VS Code:**
```json
// .vscode/settings.json
{
  "simple.formatOnSave": true,
  "simple.formatter.path": "/usr/bin/simple",
  "editor.formatOnSave": true,
  "editor.defaultFormatter": "simple-lang.simple"
}
```

**Vim/Neovim:**
```vim
" Auto-format on save
autocmd BufWritePre *.spl :!simple fmt %

" Format current buffer
nnoremap <leader>f :!simple fmt %<CR>
```

**Emacs:**
```elisp
;; Format on save
(add-hook 'simple-mode-hook
  (lambda ()
    (add-hook 'before-save-hook 'simple-format nil t)))

(defun simple-format ()
  (when (eq major-mode 'simple-mode)
    (shell-command-on-region
      (point-min) (point-max)
      "simple fmt --stdin"
      (current-buffer) t)))
```

**Git Hooks:**
```bash
#!/bin/sh
# .git/hooks/pre-commit
# Format staged Simple files

files=$(git diff --cached --name-only --diff-filter=ACM | grep '\.spl$')

if [ -n "$files" ]; then
    echo "Formatting Simple files..."
    simple fmt $files
    git add $files
fi
```

**CI Integration:**
```yaml
# .github/workflows/ci.yml
- name: Check formatting
  run: simple fmt --check src/
  
# .gitlab-ci.yml
format-check:
  script:
    - simple fmt --check src/
```

## Implementation

### Architecture

```
┌─────────────────┐
│  Input Source   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Parser → AST   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Formatter      │ Apply canonical rules
│  - Indentation  │
│  - Spacing      │
│  - Line breaks  │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Pretty Printer │ Emit formatted text
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Output File    │
└─────────────────┘
```

### Formatting Algorithm

**Phase 1: Parse**
```rust
let source = fs::read_to_string(path)?;
let mut parser = Parser::new(&source);
let ast = parser.parse()?;
```

**Phase 2: Format**
```rust
struct Formatter {
    indent_level: usize,
    line_length: usize,
    current_column: usize,
}

impl Formatter {
    fn format_module(&mut self, module: &Module) -> String {
        let mut output = String::new();
        
        // Sort imports
        let imports = self.sort_imports(&module.imports);
        for import in imports {
            output.push_str(&self.format_import(&import));
            output.push('\n');
        }
        
        // Format items with blank lines
        for (i, item) in module.items.iter().enumerate() {
            if i > 0 {
                output.push('\n');
            }
            output.push_str(&self.format_item(item));
        }
        
        output
    }
    
    fn format_function(&mut self, func: &FunctionDef) -> String {
        let mut output = String::new();
        
        // Format signature
        output.push_str("fn ");
        output.push_str(&func.name);
        
        // Parameters
        if self.should_wrap_params(&func.params) {
            output.push_str("(\n");
            self.indent_level += 1;
            for param in &func.params {
                output.push_str(&self.indent());
                output.push_str(&self.format_param(param));
                output.push_str(",\n");
            }
            self.indent_level -= 1;
            output.push_str(&self.indent());
            output.push_str(")");
        } else {
            output.push('(');
            output.push_str(&self.format_params(&func.params));
            output.push(')');
        }
        
        // Return type
        if let Some(ret) = &func.return_type {
            output.push_str(" -> ");
            output.push_str(&self.format_type(ret));
        }
        
        output.push_str(":\n");
        
        // Body
        self.indent_level += 1;
        for stmt in &func.body {
            output.push_str(&self.indent());
            output.push_str(&self.format_statement(stmt));
            output.push('\n');
        }
        self.indent_level -= 1;
        
        output
    }
}
```

**Phase 3: Write**
```rust
// Check mode: compare
if check_mode {
    if formatted != original {
        eprintln!("✗ {} needs formatting", path);
        return Err(FormatError::NeedsFormatting);
    }
}

// Format mode: write
fs::write(path, formatted)?;
```

### Line Breaking Rules

**Prefer Keeping Things Inline:**
```simple
# Good: short signatures inline
fn add(x: i64, y: i64) -> i64:
    return x + y
```

**Wrap When Over Limit:**
```simple
# Long signatures wrap
fn process_user_registration_with_validation(
    username: String,
    email: String,
    password: String
) -> Result<User, ValidationError>:
    ...
```

**Intelligent Breaking:**
```simple
# Break at commas
let result = calculate(
    param1,
    param2,
    param3
)

# Break at operators (align)
if very_long_condition_one
   and very_long_condition_two
   or very_long_condition_three:
    ...

# Break chains
user
    .validate()
    .save()
    .send_notification()
```

## Benefits for LLM Tools

1. **Predictability** - LLMs learn one style
2. **Consistency** - All generated code looks the same
3. **No Configuration** - Zero decisions to make
4. **Meaningful Diffs** - Only logic changes visible
5. **Auto-fix** - Format fixes style issues automatically

## Implementation Plan

### Phase 1: Core Formatter (3 days)
- [ ] AST pretty-printer
- [ ] Basic indentation
- [ ] Function formatting
- [ ] Expression formatting
- [ ] Statement formatting

### Phase 2: Advanced Rules (2 days)
- [ ] Line breaking algorithm
- [ ] Intelligent wrapping
- [ ] Import sorting
- [ ] Comment formatting
- [ ] Blank line rules

### Phase 3: CLI Integration (1 day)
- [ ] `simple fmt` command
- [ ] `--check` mode
- [ ] `--diff` mode
- [ ] `--stdin` mode
- [ ] Exit codes

### Phase 4: Editor Integration (2 days)
- [ ] VS Code extension
- [ ] Vim/Neovim plugin
- [ ] Emacs integration
- [ ] Generic LSP support
- [ ] Format-on-save

### Phase 5: Testing & Refinement (2 days)
- [ ] Format all stdlib code
- [ ] Test edge cases
- [ ] Performance optimization
- [ ] Documentation
- [ ] Examples

**Total Estimated Effort:** 10 days

## File Structure

```
src/compiler/src/formatter/
├── mod.rs                # Main formatter
├── rules.rs              # Formatting rules
├── indent.rs             # Indentation logic
├── line_break.rs         # Line breaking
├── comments.rs           # Comment formatting
├── imports.rs            # Import sorting
└── pretty_print.rs       # Pretty printer

src/compiler/src/bin/simple-fmt.rs   # Standalone binary

src/app/nvim_plugin/      # Neovim plugin
src/app/vscode_extension/  # VS Code extension
# (old editors/ moved to src/app/)
├── vscode/               # VS Code extension
├── vim/                  # Vim plugin
├── emacs/                # Emacs mode
└── lsp/                  # LSP integration

tests/formatter/
├── basic_spec.rs
├── functions_spec.rs
├── expressions_spec.rs
└── edge_cases_spec.rs
```

## Example Transformations

### Before Formatting
```simple
fn calculate(x:i64,y:i64)->i64:
  return x+y

fn another_function(  param1: String,param2:i64,param3:bool  )  ->  Result<Value>:
  if  condition:
      do_something(  )
  return value
```

### After Formatting
```simple
fn calculate(x: i64, y: i64) -> i64:
    return x + y

fn another_function(
    param1: String,
    param2: i64,
    param3: bool
) -> Result<Value>:
    if condition:
        do_something()
    return value
```

## CI/CD Integration

**GitHub Actions:**
```yaml
name: Format Check
on: [pull_request]
jobs:
  format:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Check formatting
        run: simple fmt --check src/
```

**Pre-commit:**
```yaml
# .pre-commit-config.yaml
repos:
  - repo: local
    hooks:
      - id: simple-fmt
        name: Simple Formatter
        entry: simple fmt
        language: system
        files: \.spl$
```

## Related Features

- #889: Semantic diff (works with formatted code)
- #906: Lint CLI (complements formatting)
- #885-887: IR export (formatting preserves semantics)

## Success Metrics

- [ ] 100% of stdlib formatted consistently
- [ ] <100ms to format typical file
- [ ] Zero configuration needed
- [ ] 95%+ developer satisfaction
- [ ] LLMs generate correctly formatted code

## References

- **gofmt** (Go) - Original opinionated formatter
- **rustfmt** (Rust) - Rust formatter
- **black** (Python) - "Uncompromising" Python formatter
- **prettier** (JavaScript) - Opinionated JS formatter

---

**Next Steps:**
1. Review and approve specification
2. Implement core formatter
3. Test with stdlib code
4. Add editor integrations
5. Mark #908-910 complete
