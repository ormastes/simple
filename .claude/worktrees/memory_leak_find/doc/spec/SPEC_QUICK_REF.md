# _spec.spl Quick Reference

**For:** Writing executable specification files  
**See:** [SPEC_GUIDELINES.md](SPEC_GUIDELINES.md) for full documentation

---

## Minimal Template

```simple
"""
# Feature Name Specification

**Status:** [Stable|Draft|Implementing|Planned]
**Feature IDs:** #XXX-YYY
**Keywords:** keyword1, keyword2

## Overview
Brief feature description.

## Specification
Detailed spec text with examples.
"""

test "basic_usage":
    """
    Test scenario description.
    """
    # Test code
    assert_compiles()
```

---

## Header Metadata (Required)

```simple
"""
# Feature Name Specification

**Status:** Stable              # Stable|Draft|Implementing|Planned
**Feature IDs:** #20-29         # Feature catalog reference
**Keywords:** types, generics   # Search terms
**Topics:** type-system         # High-level category (optional)
**Migrated From:** doc/...      # Original source (if migrated)
"""
```

---

## Test Structure

```simple
## Test: Section Name

"""
### Scenario: What this tests
Explanation of test scenario.
"""

test "descriptive_name":
    """
    Additional test details.
    """
    # Test code
    assert result == expected
```

---

## Test Naming

✅ **Good:** `basic_type_annotation`, `error_missing_capability`  
❌ **Bad:** `test1`, `it_works`

---

## Common Assertions

```simple
assert_compiles()                # Should compile successfully
assert_compile_error("msg")      # Should fail with message

assert x == y                    # Equality
assert x != y                    # Inequality
assert x in collection           # Membership
assert len(list) == 5            # Length

assert typeof(x) == "i64"        # Type checking
```

---

## Migration Command

```bash
# Dry run (preview)
python scripts/migrate_spec_to_spl.py --dry-run doc/spec/types.md tests/specs/types_spec.spl

# Actual migration
python scripts/migrate_spec_to_spl.py doc/spec/types.md tests/specs/types_spec.spl

# Migrate all Category A files
python scripts/migrate_spec_to_spl.py --all
```

---

## File Locations

```
tests/
├── specs/              # Feature specifications (NEW)
│   ├── syntax_spec.spl
│   ├── types_spec.spl
│   └── ...
├── system/             # Integration tests
└── meta/               # Meta/tool tests
```

---

## Quick Checks

**Before committing:**
- [ ] File compiles: `simple compile tests/specs/myfeature_spec.spl`
- [ ] All tests pass: `simple test tests/specs/myfeature_spec.spl`
- [ ] Metadata complete (Status, Feature IDs, Keywords)
- [ ] Overview section present
- [ ] At least 3 test cases

---

**Full Guide:** [SPEC_GUIDELINES.md](SPEC_GUIDELINES.md)
