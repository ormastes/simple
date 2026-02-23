# SSpec Templates

This directory contains templates for creating new SSpec test files.

## Available Templates

### `sspec_template.spl`

**Purpose:** Standard template for creating feature specification test files.

**Usage:**

```bash
# Create a new feature spec
cp .claude/templates/sspec_template.spl \
   simple/test/system/features/my_feature/my_feature_spec.spl

# Edit the file and fill in:
# 1. Feature name and metadata (Feature IDs, Category, Status)
# 2. Overview and documentation
# 3. Test cases
```

**Contains:**

- ✅ Required module-level docstring with metadata template
- ✅ Section markers for organizing tests
- ✅ Example test groups with documentation
- ✅ BDD structure (describe/context/it)
- ✅ Hook examples (before_each/after_each)
- ✅ Helper code section
- ✅ Comments explaining each part

**Required Edits:**

1. **Feature Name** - Replace "Feature Name Specification" with your feature
2. **Metadata:**
   - `Feature IDs:` - Your ID range (e.g., #450-455)
   - `Category:` - Choose: Infrastructure, Language, Syntax, Stdlib, Runtime, Testing, Tooling
   - `Status:` - Draft, In Progress, Implemented, or Complete
3. **Overview** - Explain what your feature does
4. **Test Code** - Replace placeholder tests with real test cases

## Complete Workflow

See `doc/guide/sspec_complete_example.md` for a full end-to-end example.

### Quick Steps

1. **Copy template** to your feature directory
2. **Fill in metadata** and overview
3. **Write tests** with `describe`/`context`/`it` blocks
4. **Add docstrings** to document behavior
5. **Run tests:** `cargo test -p simple-driver simple_stdlib`
6. **Generate docs:** `cargo run --bin gen-sspec-docs -- path/to/*_spec.spl`

## Documentation Requirements

Every spec file MUST have:

1. **Module-level docstring** at the top with:
   - Feature IDs (required)
   - Category (required)
   - Status (required)
   - Overview (required)

2. **Test group docstrings** in `describe` blocks (recommended)

3. **Scenario docstrings** in `context` blocks (recommended)

Example:

```simple
"""
# My Feature Specification

**Feature IDs:** #100-105
**Category:** Language
**Status:** Implemented

## Overview
Explains what this feature does...
"""

import std.spec

describe "MyFeature":
    """
    ## Basic Usage
    Explains this test group...
    """

    context "when condition":
        """
        ### Scenario: Specific case
        Explains this scenario...
        """

        it "does something":
            expect(true).to(eq(true))
```

## Tips

- **Start simple** - Copy template, run tests, iterate
- **Document as you write** - Add docstrings while writing tests
- **Test first** - Ensure tests pass before generating docs
- **Check generated docs** - Review output to ensure it reads well

## See Also

- `/sspec` skill - Quick reference
- `doc/guide/sspec_complete_example.md` - Complete walkthrough
- `doc/guide/sspec_writing.md` - Writing guide
- `doc/spec/sspec_format.md` - Format specification
