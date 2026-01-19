# Simple Compiler i18n Catalogs

This directory contains localized error messages for the Simple compiler.

## Supported Languages

| Language | Code | Status |
|----------|------|--------|
| English | en | ✅ Complete |
| Korean | ko | ✅ Complete |

## File Structure

```
i18n/
├── __init__.spl          # English UI strings
├── __init__.ko.spl       # Korean UI strings  
├── parser.spl            # English parser errors
├── parser.ko.spl         # Korean parser errors
├── compiler.spl          # English compiler errors
└── compiler.ko.spl       # Korean compiler errors
```

## Adding Translations

See `doc/contributing/i18n.md` for detailed instructions.

## Usage

```bash
# English (default)
simple build main.spl

# Korean
simple build main.spl --lang ko
```
