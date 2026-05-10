# Lint: Export Star Warning & Critical File Guard

## W0407: Wildcard Export Warning

Detects `export module.*` in non-facade files. Wildcard re-exports obscure symbol provenance.

### Behavior
- Fires on any `export X.*` in regular `.spl` files
- **Exempt**: `__init__.spl` and `mod.spl` (facade modules)
- **Exempt**: Files containing ONLY wildcard use+export declarations (pure facades)

### Fix
Replace `export some_module.*` with explicit named exports:
```
# Before (triggers W0407)
export some_module.*

# After
export MyClass, my_function, CONSTANT
```

### Configuration
The warning has no suppression mechanism yet. Use `__init__.spl` or `mod.spl` naming for legitimate re-export facades.

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
