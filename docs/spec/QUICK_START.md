# Quick Start Guide - Spec Documentation

**Last Updated:** 2026-01-08 12:56 UTC

## Overview

The Simple compiler uses native Simple specifications (`*_spec.spl`) for testing, with automatic Markdown documentation generation.

## Running Tests

```bash
# Run all Simple tests
cargo test -p simple-driver --test simple_stdlib_tests

# Run specific category
cargo test mixin
cargo test static_poly

# With output
cargo test -- --nocapture
```

## Generating Documentation

```bash
# Auto-generate all documentation
bash scripts/gen_spec_docs.sh

# Output files in docs/spec/:
# - MIXIN_FEATURES.md
# - SPEC_CATALOG.md
# - README.md (updated)
```

## Documentation Files

| File | Purpose | Lines |
|------|---------|-------|
| **README.md** | Main index | 211 |
| **SPEC_CATALOG.md** | Complete spec listing | 85 |
| **MIXIN_FEATURES.md** | Mixin documentation | 196 |
| **TEST_REPORT_2026-01-08.md** | Test report | 240 |
| **BDD_TEST_SPEC.md** | BDD guide | 286 |
| **MIGRATION_COMPLETE.md** | Migration report | 253 |
| **TEST_SUMMARY.txt** | Quick summary | 132 |

## Writing New Specs

```simple
import std.spec

describe "Feature Name":
    context "Scenario":
        it "should do something":
            let result = function_under_test()
            expect result == expected_value
```

## CI/CD Integration

Add to your workflow:

```yaml
- name: Run tests
  run: cargo test --workspace

- name: Generate docs
  run: bash scripts/gen_spec_docs.sh

- name: Commit docs
  run: |
    git add docs/spec/*.md
    git commit -m "Update spec documentation"
```

## File Locations

```
simple/
├── simple/std_lib/test/          # Test specs
│   ├── system/                   # System tests
│   │   ├── mixins/              # Mixin specs (7 files)
│   │   └── static_poly/         # Static poly specs (2 files)
│   ├── integration/              # Integration tests
│   └── unit/                     # Unit tests
├── docs/spec/                    # Generated documentation
└── scripts/
    └── gen_spec_docs.sh          # Doc generator
```

## Quick Reference

### Test Status
- **Total Tests:** 206 Simple + 1,438 Rust = 1,644
- **Pass Rate:** 100% ✅
- **Latest Run:** 2026-01-08

### Migration Status
- **Gherkin → Simple:** 8 features migrated
- **New Specs:** 7 files created
- **New Tests:** 69 tests added
- **Status:** ✅ Complete

### Documentation Status
- **Auto-Generated:** Yes ✅
- **Up-to-Date:** Yes ✅
- **Format:** Markdown
- **Generator:** `scripts/gen_spec_docs.sh`

## Getting Help

- **Test Issues:** Check `TEST_REPORT_2026-01-08.md`
- **BDD Questions:** See `BDD_TEST_SPEC.md`
- **Full Migration Details:** Read `MIGRATION_COMPLETE.md`
- **Spec Index:** Browse `SPEC_CATALOG.md`

---

**Quick Links:**
- [Full Documentation Index](README.md)
- [Test Report](TEST_REPORT_2026-01-08.md)
- [Mixin Features](MIXIN_FEATURES.md)
- [Spec Catalog](SPEC_CATALOG.md)
