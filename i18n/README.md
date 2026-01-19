# Simple Compiler i18n Catalogs

This directory contains localized error messages for the Simple compiler.

## Architecture Design

### Language-Agnostic Catalogs

The i18n system uses a **constant-based design** where:
- **Language strings** are defined as constants in `__init__.spl` (English) and `__init__.ko.spl` (Korean)
- **Error catalogs** (`parser.spl`, `compiler.spl`, etc.) reference these constants and remain language-agnostic

This approach:
- ✅ Eliminates file duplication (no `.ko.spl` files for each domain)
- ✅ Keeps translations in sync (both languages visible in `__init__` files)
- ✅ Makes catalogs truly reusable across languages
- ✅ Simplifies adding new languages (just add `__init__.{lang}.spl`)

### File Structure

```
i18n/
├── __init__.spl          # English constants (titles, messages, labels, help)
├── __init__.ko.spl       # Korean constants (same structure as English)
├── parser.spl            # Parser errors (references constants) - LANGUAGE-AGNOSTIC
├── compiler.spl          # Compiler errors (references constants) - LANGUAGE-AGNOSTIC
├── verification.spl      # Verification errors (references constants) - LANGUAGE-AGNOSTIC
├── lint.spl              # Lint messages (references constants) - LANGUAGE-AGNOSTIC
├── explanations.spl      # Error explanations (references constants) - LANGUAGE-AGNOSTIC
└── runtime.spl           # Runtime errors (references constants) - LANGUAGE-AGNOSTIC
```

## Example

### `__init__.spl` (English)
```simple
val severity = {
    "ERROR": "error",
    "WARNING": "warning"
}

val UNEXPECTED_TOKEN = "Unexpected Token"
val UNEXPECTED_TOKEN_MSG = "unexpected token: expected {expected}, found {found}"
val UNEXPECTED_TOKEN_LABEL = "expected {expected} here"
val UNEXPECTED_TOKEN_HELP = "try adding `{expected}` before this token"
```

### `__init__.ko.spl` (Korean)
```simple
val severity = {
    "ERROR": "오류",
    "WARNING": "경고"
}

val UNEXPECTED_TOKEN = "예상치 못한 토큰"
val UNEXPECTED_TOKEN_MSG = "{expected}을(를) 예상했지만 {found}을(를) 발견했습니다"
val UNEXPECTED_TOKEN_LABEL = "여기에 {expected}이(가) 필요합니다"
val UNEXPECTED_TOKEN_HELP = "이 토큰 앞에 `{expected}`를 추가해 보세요"
```

### `parser.spl` (Language-Agnostic)
```simple
val messages = {
    "E0002": {
        "id": "E0002",
        "title": UNEXPECTED_TOKEN,
        "message": UNEXPECTED_TOKEN_MSG,
        "label": UNEXPECTED_TOKEN_LABEL,
        "help": UNEXPECTED_TOKEN_HELP
    }
}
```

When the locale is set to `ko`, the i18n system:
1. Loads `__init__.ko.spl` instead of `__init__.spl`
2. Loads `parser.spl` (same file for all languages)
3. Constants resolve to Korean values
4. Error E0002 displays in Korean automatically!

## Supported Languages

| Language | Code | __init__ File | Status |
|----------|------|---------------|--------|
| English | en | `__init__.spl` | ✅ Complete |
| Korean | ko | `__init__.ko.spl` | ✅ Complete |

## Adding a New Language

To add Japanese support:

1. **Create `__init__.ja.spl`** with all constants translated to Japanese
2. **No other files needed!** All catalog files (`parser.spl`, `compiler.spl`, etc.) work automatically

Example `__init__.ja.spl`:
```simple
val severity = {
    "ERROR": "エラー",
    "WARNING": "警告"
}

val UNEXPECTED_TOKEN = "予期しないトークン"
val UNEXPECTED_TOKEN_MSG = "{expected}を期待しましたが、{found}が見つかりました"
# ... etc
```

## Usage

```bash
# English (default)
simple build main.spl

# Korean
simple build main.spl --lang ko

# Japanese (when implemented)
simple build main.spl --lang ja
```

## Error Coverage

| Domain | Codes | File | Status |
|--------|-------|------|--------|
| UI Strings | severity levels | `__init__.spl` / `__init__.ko.spl` | ✅ Complete |
| Parser | E0001-E0012 (12 errors) | `parser.spl` | ✅ Complete |
| Compiler | E1001-E3009 (33 errors) | `compiler.spl` | ✅ Complete |
| Verification | V-AOP, V-MACRO, V-TERM, etc. (21 errors) | `verification.spl` | ✅ Complete |
| Lint | 8 lint codes | `lint.spl` | ✅ Complete |
| Explanations | 8 detailed explanations | `explanations.spl` | ✅ Complete |
| Runtime | E4xxx-E6xxx (24 errors) | `runtime.spl` | ✅ Complete |

**Total**: ~98 error codes fully localized in English and Korean

## Constant Naming Convention

All error messages follow a consistent naming pattern for their constants:

### Error Message Constants

```simple
# Pattern: {ERROR_CODE}_{FIELD}
val E1001_TITLE = "Undefined Variable"
val E1001_MSG = "cannot find variable `{name}` in this scope"
val E1001_LABEL = "not found in this scope"
val E1001_HELP = "check the spelling or declare the variable before use"
val E1001_NOTE = "optional note field"  # Not all errors have this
```

### Lint Message Constants

```simple
# Pattern: LINT_{LINT_ID}_{FIELD}
val LINT_PRIMITIVE_API_TITLE = "Primitive Type in Public API"
val LINT_PRIMITIVE_API_MSG = "bare primitive type in public API signature"
val LINT_PRIMITIVE_API_LABEL = "primitive type lacks semantic meaning"
val LINT_PRIMITIVE_API_HELP = "use semantic unit types or newtype wrappers instead"
```

### Verification Error Constants

```simple
# Pattern: {ERROR_CODE_WITH_UNDERSCORES}_{FIELD}
# Note: Hyphens in error codes are replaced with underscores
val V_AOP_001_TITLE = "Non-Ghost Aspect Targets Verified Code"
val V_AOP_001_MSG = "non-ghost aspect targets verified join point"
val V_AOP_001_LABEL = "aspect targets verified code here"
val V_AOP_001_HELP = "mark the aspect with `ghost` to allow it in verified context"
```

### Explanation Constants

```simple
# Pattern: {ERROR_CODE}_EXPL_{FIELD}
val E1001_EXPL_TITLE = "Undefined Variable"
val E1001_EXPL_DESCRIPTION = "Attempted to use a variable that hasn't been declared..."
val E1001_EXPL_CAUSES = ["Variable name was misspelled", "Variable was used before declaration", ...]
val E1001_EXPL_FIXES = ["Check the spelling", "Declare the variable with 'let' or 'var'", ...]
val E1001_EXPL_EXAMPLE_BAD = "fn main():\n    print(count)  # Error: count not defined"
val E1001_EXPL_EXAMPLE_GOOD = "fn main():\n    let count = 0\n    print(count)  # OK"
val E1001_EXPL_RELATED = ["E1002", "E1008"]
```

### String Interpolation

All message strings support variable interpolation using `{variable_name}` syntax:

```simple
val E1001_MSG = "cannot find variable `{name}` in this scope"
val E1003_MSG = "expected type `{expected}`, found `{found}`"
```

At runtime, the i18n system will use the `.inst()` method to instantiate strings with actual values:

```simple
# Runtime usage (conceptual)
val msg = E1001_MSG.inst({"name": "foo"})
# Result: "cannot find variable `foo` in this scope"
```

## Implementation Notes

### How It Works

1. **Locale Detection**: System reads `SIMPLE_LANG` environment variable or `--lang` flag
2. **Load Constants**: Loads appropriate `__init__.{lang}.spl` file
3. **Load Catalogs**: Loads domain catalogs (`parser.spl`, etc.) which reference constants
4. **Runtime Resolution**: Constants resolve to translated values at runtime

### Benefits

- **DRY Principle**: Each error message defined once, works for all languages
- **Type Safety**: References to undefined constants will fail at load time
- **Maintainability**: Adding/modifying errors requires updating only one catalog file
- **Scalability**: Adding a new language is just one file (`__init__.{lang}.spl`)

### Trade-offs

- **Constant Naming**: Must maintain consistent constant names across all `__init__` files
- **Initial Setup**: Requires defining all constants upfront
- **Flexibility**: Messages must fit the constant-based structure

These trade-offs are acceptable because:
- Error messages have predictable structure (title, message, label, help)
- Benefits of simplicity and maintainability far outweigh the constraints

## Contributing

See `doc/contributing/i18n.md` for translation guidelines.
