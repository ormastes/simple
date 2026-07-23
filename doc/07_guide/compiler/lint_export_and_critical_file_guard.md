# Lint: Star Wildcard Warnings & Critical File Guard

## Star Wildcard Lint (`star_import.spl`)

Unified module detecting both wildcard imports and exports using a single
`StarWildcardWarning` struct and shared `_is_facade_file()` helper.

| Code | Pattern | Message |
|------|---------|---------|
| W0406 | `use module.*` | wildcard import — prefer explicit named imports |
| W0407 | `export module.*` | wildcard export — prefer explicit named exports |

### Behavior
- Fires on any `use X.*` or `export X.*` in regular `.spl` files
- **Exempt**: `__init__.spl` and `mod.spl` (facade modules via `_is_facade_file()`)
- **Exempt**: Pure facade files (only wildcard use+export declarations)

### Fix
Replace wildcards with explicit named symbols:
```
# Before (triggers W0406/W0407)
use some_module.*
export some_module.*

# After
use some_module.{MyClass, my_function}
export MyClass, my_function, CONSTANT
```

### Architecture
- `StarWildcardWarning` — single struct for both W0406 and W0407
- `_is_facade_file(path)` — shared helper (deduplicates __init__/mod check)
- Production lint keeps W0406 in its text/EasyFix owner and adds W0407 through
  the parsed AST adapter, preventing duplicate wildcard-import diagnostics.
- `_emit_wildcard_warnings(warnings, lines, file, format, keyword)` — shared emit in query_lint
- `_find_decl_line_in_source(lines, keyword, path)` — generic line finder
- Backwards-compatible aliases: `StarImportWarning = StarWildcardWarning`, `StarExportWarning = StarWildcardWarning`

---

## CFG001/CFG002: Critical File Guard

Protects important files from accidental deletion or significant shrinkage.

### Config: `config/critical_files.sdn`

```sdn
critical_files:
  entries:
    - path: src/compiler/00.common/error.spl
      min_lines: 100
  protected_dirs:
    - path: src/compiler/35.semantics/lint/
      action: warn_on_delete
```

| Field | Description |
|-------|-------------|
| `path` | Relative path from repo root |
| `min_lines` | Minimum acceptable line count |
| `action` | `warn_on_delete` for directory-level protection |

### Warning Codes
| Code | Severity | Meaning |
|------|----------|---------|
| CFG001 | ERROR | Critical file deleted/missing |
| CFG002 | WARNING | File shrunk below `min_lines` threshold |

### Integration Points
1. **Lint time**: `bin/simple build lint` runs `check_all_critical_files()`
2. **Sync/rebase time**: `/sync` skill checks after `jj rebase` — aborts if critical files deleted or shrunk >50%

### Adding Protected Files
Edit `config/critical_files.sdn` and add an entry under `entries:`.
