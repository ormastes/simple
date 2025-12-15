# Documentation Refactoring (2025-12-15)

## Summary

Reorganized large markdown documentation files (>1000 lines) into focused index files with references to detailed content. This improves navigation, maintainability, and git diff readability.

## Changes

### Feature Documentation
- **doc/feature.md**: 1020 lines → 88 lines (91% reduction)
  - Now a concise overview with status summary and links
  - Created **doc/feature_index.md** (NEW) for complete catalog
  - Original preserved as `doc/feature.md.backup`

### API Design Documentation  
- **doc/research/improve_api.md**: 1019 lines → 203 lines (80% reduction)
  - Now focused on core principles and quick reference
  - Created **doc/research/api_design_index.md** (NEW) for detailed guidelines
  - Original preserved as `doc/research/improve_api.md.backup`

### Development Guide
- **CLAUDE.md**: Updated to reference new documentation structure
  - Added feature_index.md, codegen_status.md references
  - Added api_design_index.md reference
  - Added documentation reorganization note

## New Files

- `doc/feature_index.md` - Complete feature catalog (131+ features) with ratings, status, architecture impact
- `doc/research/api_design_index.md` - API design guidelines organized by topic

## Benefits

1. **Better Navigation**: Index files provide clear structure
2. **Easier Maintenance**: Smaller focused files are easier to update
3. **Preserved Content**: All original content saved in `.backup` files
4. **Improved Readability**: Key information visible without scrolling
5. **Better Git Diffs**: Smaller files = clearer change tracking

## Usage

```bash
# Quick lookups
cat doc/feature.md                    # Overview
cat doc/feature_index.md              # Full feature catalog

# API design
cat doc/research/improve_api.md       # Quick reference
cat doc/research/api_design_index.md  # Detailed guidelines

# Original content
cat doc/feature.md.backup
cat doc/research/improve_api.md.backup
```

## Future Work

Additional large files that could be refactored (>900 lines):
- `doc/spec/units.md` (960 lines) - Unit types specification
- `doc/plans/09_interpreter_like_workflow.md` (950 lines)
- `doc/spec/parser/lexer_parser_integration.md` (941 lines)
- `doc/plans/06_dynamic_reload.md` (939 lines)
- `doc/spec/primitive_as_obj.md` (899 lines)

These are less critical as they are more technical/specific and less frequently referenced.
