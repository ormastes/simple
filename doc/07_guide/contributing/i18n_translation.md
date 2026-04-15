# Contributing Translations to Simple

**Welcome!** This guide will help you contribute translations for the Simple compiler's error messages and UI text.

---

## Quick Start

### Prerequisites

- Native or fluent speaker of the target language
- Familiarity with Simple language syntax (basic level sufficient)
- Understanding of programming error terminology
- Git and GitHub account

### Overview

1. Copy English catalog files
2. Translate message content (keep structure unchanged)
3. Test with `--lang` flag
4. Submit pull request with native speaker review

---

## Step-by-Step Guide

### Step 1: Set Up Your Environment

```bash
# Clone the Simple repository
git clone https://github.com/simple-lang/simple.git
cd simple

# Build the compiler (ensures everything works)
cargo build --release

# Verify i18n files exist
ls src/i18n/
```

### Step 2: Choose Your Language

**Use ISO 639-1 two-letter codes**:
- Japanese: `ja`
- Chinese: `zh`
- Spanish: `es`
- French: `fr`
- German: `de`

For regional variants, use underscore:
- Chinese (Simplified): `zh_CN`
- Chinese (Traditional): `zh_TW`
- Spanish (Spain): `es_ES`
- Spanish (Latin America): `es_LA`

### Step 3: Copy English Catalogs

```bash
# Navigate to i18n directory
cd i18n

# Copy files for your language (example: Japanese)
cp __init__.spl __init__.ja.spl
cp parser.spl parser.ja.spl

# If compiler.spl exists
cp compiler.spl compiler.ja.spl
```

### Step 4: Translate Content

**Important rules**:
- ✅ **DO** translate title, message, label, help, note fields
- ✅ **DO** keep `{placeholders}` unchanged
- ✅ **DO** maintain error codes (E0001, E0002, etc.)
- ✅ **DO** use professional/formal tone
- ❌ **DON'T** translate placeholder names (`{expected}`, `{found}`)
- ❌ **DON'T** modify error code IDs
- ❌ **DON'T** change file structure or syntax

#### Example: Translating __init__.ja.spl

**Before (English)**:
```simple
# English UI strings for the Simple compiler
val severity = {
    "error": "error",
    "warning": "warning",
    "info": "info",
    "help": "help",
    "note": "note"
}
```

**After (Japanese)**:
```simple
# Simple コンパイラの日本語 UI 文字列
val severity = {
    "error": "エラー",
    "warning": "警告",
    "info": "情報",
    "help": "ヘルプ",
    "note": "注"
}
```

#### Example: Translating parser.ja.spl

**Before (English)**:
```simple
"E0002": {
    "id": "E0002",
    "title": "Unexpected Token",
    "message": "unexpected token: expected {expected}, found {found}",
    "label": "expected {expected} here",
    "help": "try adding `{expected}` before this token"
}
```

**After (Japanese)**:
```simple
"E0002": {
    "id": "E0002",
    "title": "予期しないトークン",
    "message": "予期しないトークン: {expected}を期待しましたが、{found}が見つかりました",
    "label": "ここに{expected}が必要です",
    "help": "このトークンの前に`{expected}`を追加してください"
}
```

**Notice**:
- `{expected}` and `{found}` are **unchanged**
- Error code "E0002" is **unchanged**
- "id" field is **unchanged**
- Japanese sentence structure naturally differs from English (SOV vs SVO)

### Step 5: Handle Placeholder Interpolation

#### English Placeholders
```
{expected}    # Token or syntax element expected
{found}       # What was actually found
{message}     # Generic message text
{literal}     # Code literal value
{sequence}    # Escape sequence
{name}        # Identifier or symbol name
```

#### Language-Specific Considerations

**Korean**: Particles (조사) change based on final consonant
```simple
# Simple approach (v1.0)
"label": "여기에 {expected}이(가) 필요합니다"  # Both forms shown

# Future enhancement (v2.0)
# Dynamic particle selection based on {expected} value
```

**Japanese**: Particles (助詞) are consistent
```simple
"label": "ここに{expected}が必要です"  # が is always used
```

**Chinese**: No particles needed
```simple
"label": "这里需要{expected}"  # Direct construction
```

### Step 6: Test Your Translation

```bash
# Build the compiler with your translation
cargo build --release

# Create a test file with errors
cat > test_error.spl << 'EOF'
fn main(
    # Missing closing parenthesis
    return 0
EOF

# Test your translation
./target/release/simple build test_error.spl --lang ja

# Expected output (Japanese example):
# エラー[E0010]: 必要なトークンが見つかりません: )
#   --> test_error.spl:1:9
#    |
#  1 | fn main(
#    |         ^ ここに)が必要です
```

### Step 7: Validate Syntax

```bash
# Simple parser can check your catalog files
./target/release/simple build src/i18n/__init__.ja.spl
./target/release/simple build src/i18n/parser.ja.spl

# Should output: "success" (no syntax errors)
```

### Step 8: Get Native Speaker Review

**Before submitting**:
1. Have at least one other native speaker review your translations
2. Check for:
   - ✅ Natural phrasing
   - ✅ Appropriate formality level
   - ✅ Consistent terminology
   - ✅ No typos or grammatical errors

**Review checklist**:
```
□ All error codes translated
□ Placeholders unchanged
□ No syntax errors in .spl files
□ Natural language flow
□ Professional tone maintained
□ Native speaker approval obtained
```

### Step 9: Submit Pull Request

```bash
# Create a new branch
git checkout -b src/i18n/japanese-translation

# Add your files
git add src/i18n/__init__.ja.spl
git add src/i18n/parser.ja.spl

# Commit with descriptive message
git commit -m "feat(i18n): Add Japanese translations for parser errors

- Translate __init__.ja.spl (severity names)
- Translate parser.ja.spl (E0001-E0012)
- Reviewed by: @native_speaker_username
- Tested with: simple build --lang ja"

# Push to your fork
git push origin src/i18n/japanese-translation
```

**PR Template**:
```markdown
## Description
Add Japanese translations for Simple compiler error messages.

## Translated Files
- `src/i18n/__init__.ja.spl` - UI strings (severity names)
- `src/i18n/parser.ja.spl` - Parser errors E0001-E0012

## Testing
- ✅ Syntax validated with Simple parser
- ✅ Tested with `--lang ja` flag
- ✅ All error codes display correctly
- ✅ Native speaker review: @reviewer_username

## Translation Quality
- Professional/formal tone maintained
- All placeholders preserved
- Error codes unchanged
- Natural Japanese sentence structure
```

---

## Translation Guidelines by Language

### Korean (한국어)

**Formality**: Use formal polite form (합니다체)
```simple
# ✅ Good
"message": "토큰이 누락되었습니다"

# ❌ Too casual
"message": "토큰이 없어"
```

**Particles**: Use neutral forms in v1.0
```simple
# v1.0: Show both forms
"label": "여기에 식별자가(이) 필요합니다"

# Future: Dynamic selection
```

**Terminology**:
- error → 오류 (not 에러)
- token → 토큰
- identifier → 식별자
- function → 함수

### Japanese (日本語)

**Formality**: Use です/ます form
```simple
# ✅ Good
"message": "トークンがありません"

# ❌ Too casual
"message": "トークンがない"
```

**Particles**: Consistent usage
- が (subject marker)
- を (object marker)
- に (direction/location)

**Terminology**:
- error → エラー
- token → トークン
- identifier → 識別子
- function → 関数

### Chinese (中文)

**Simplified vs Traditional**:
- Simplified: `zh_CN` (Mainland China)
- Traditional: `zh_TW` (Taiwan)

**Formality**: Use standard written Chinese
```simple
# ✅ Good
"message": "缺少标记"

# ❌ Too colloquial
"message": "没有标记"
```

**Terminology (Simplified)**:
- error → 错误
- token → 标记 or 令牌
- identifier → 标识符
- function → 函数

### Spanish (Español)

**Regional Variants**:
- Spain: `es_ES` (tú/vosotros)
- Latin America: `es_LA` (tú/ustedes)

**Formality**: Use formal imperative
```simple
# ✅ Good
"help": "intente agregar `{expected}` antes de este token"

# ❌ Too informal
"help": "agrega `{expected}` antes de este token"
```

**Terminology**:
- error → error
- token → token or elemento
- identifier → identificador
- function → función

### French (Français)

**Formality**: Use vous form
```simple
# ✅ Good
"help": "essayez d'ajouter `{expected}` avant ce token"

# ❌ Too informal
"help": "essaie d'ajouter `{expected}` avant ce token"
```

**Terminology**:
- error → erreur
- token → jeton or token
- identifier → identifiant
- function → fonction

### German (Deutsch)

**Formality**: Use Sie form
```simple
# ✅ Good
"help": "versuchen Sie, `{expected}` vor diesem Token hinzuzufügen"

# ❌ Too informal
"help": "versuch, `{expected}` vor diesem Token hinzuzufügen"
```

**Terminology**:
- error → Fehler
- token → Token
- identifier → Bezeichner
- function → Funktion

---

## Common Pitfalls

### ❌ Translating Placeholders

**Wrong**:
```simple
"message": "예상: {예상}, 발견: {발견}"  # DON'T translate placeholder names
```

**Right**:
```simple
"message": "{expected}을(를) 예상했지만 {found}을(를) 발견했습니다"  # Keep {expected}, {found}
```

### ❌ Changing Error Codes

**Wrong**:
```simple
"E0002": {
    "id": "J0002",  # DON'T change error codes
    ...
}
```

**Right**:
```simple
"E0002": {
    "id": "E0002",  # Keep original
    ...
}
```

### ❌ Breaking Syntax

**Wrong**:
```simple
val severity = {
    "error": "エラー"  # Missing comma
    "warning": "警告"
}
```

**Right**:
```simple
val severity = {
    "error": "エラー",  # Comma required
    "warning": "警告"
}
```

---

## Quality Checklist

Before submitting, verify:

### Content Quality
- [ ] All error codes (E0001-E0012) translated
- [ ] All fields (title, message, label, help, note) translated
- [ ] Natural phrasing in target language
- [ ] Appropriate formality level
- [ ] Consistent terminology throughout
- [ ] No typos or grammatical errors

### Technical Quality
- [ ] Placeholders (`{expected}`, `{found}`, etc.) unchanged
- [ ] Error code IDs unchanged
- [ ] File syntax valid (parses without errors)
- [ ] Files named correctly (`__init__.XX.spl`, `parser.XX.spl`)
- [ ] UTF-8 encoding

### Testing
- [ ] Tested with `--lang XX` flag
- [ ] All error messages display correctly
- [ ] Special characters (accents, CJK) render properly
- [ ] Terminal encoding configured (UTF-8)

### Review
- [ ] Native speaker review completed
- [ ] Reviewer credited in PR
- [ ] Screenshots of test output included
- [ ] PR description filled out

---

## Need Help?

### Questions About Translation
- **Terminology**: Check existing translations in other languages
- **Technical terms**: See `doc/glossary.md` (if available)
- **Language-specific**: Ask in #i18n channel on Discord

### Technical Issues
- **Build errors**: File an issue with label `i18n`
- **Syntax errors**: Run `simple build src/i18n/your_file.spl` for details
- **Testing**: See `doc/07_guide/apps/cli_tools.md` for usage guide

### Getting Review
- **Find reviewers**: Ask in #i18n channel
- **Multiple reviewers**: Better for quality
- **Quick review**: Tag maintainers in PR

---

## Recognition

Contributors who provide high-quality translations will be:
- Listed in `CONTRIBUTORS.md`
- Credited in release notes
- Given "Translator" badge on GitHub
- Mentioned in documentation

Thank you for helping make Simple accessible to developers worldwide! 🌍

---

## Examples

### Complete Translation: Japanese Parser Errors

See `src/i18n/parser.ja.spl` (when available) for a complete example of all E0001-E0012 errors translated to Japanese.

### Complete Translation: Korean Parser Errors

See `src/i18n/parser.ko.spl` for a complete example of all E0001-E0012 errors translated to Korean.

---

## Version History

| Version | Languages | Error Codes | Status |
|---------|-----------|-------------|--------|
| 0.1.0 | en, ko | E0001-E0012 | ✅ Complete |
| 0.2.0 | +ja | E0001-E0012 | 📋 Planned |
| 0.3.0 | +zh | E0001-E0012 | 📋 Planned |
| 1.0.0 | en, ko, ja, zh | E0001-E3xxx | 📋 Planned |

---

## Related Documentation

- **User Guide**: `doc/07_guide/apps/cli_tools.md` - How to use i18n in Simple
- **Specification**: `doc/05_design/i18n_complete_specification.md` - Technical details
- **Progress Report**: `doc/09_report/i18n_implementation_progress.md` - Implementation status

---

Thank you for contributing to Simple! 🎉
