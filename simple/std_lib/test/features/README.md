# Feature Documentation Tests

This directory contains BDD tests that generate feature documentation.

## Purpose

These tests serve a dual purpose:
1. **Verify functionality**: Tests ensure features work correctly
2. **Generate documentation**: Tests automatically generate markdown docs in `doc/features/`

## Structure

Feature tests are organized by category, one file per category:

```
test/features/
├── README.md
├── infrastructure_spec.spl     # Infrastructure features (#1-#9)
├── language_spec.spl            # Core language features (#10-#49)
├── testing_spec.spl             # Testing framework features
└── ... (more categories)
```

## Writing Feature Tests

Each feature test follows this pattern:

```simple
use spec.feature_doc.feature_metadata

describe "Feature Name (#ID)":
    # Metadata for documentation generation
    feature_metadata(
        id: 1,
        name: "Feature Name",
        category: "Infrastructure",
        difficulty: 3,
        status: "✅ Complete",
        impl_type: "R",  # R=Rust, S=Simple, S+R=Both
        spec_ref: "doc/spec/spec_file.md",
        files: ["src/implementation/file.rs"],
        tests: ["src/tests/test_file.rs"],
        description: """
        Detailed description of the feature.
        What it does, how it works.
        """,
        dependencies: [2, 3],  # Feature IDs this depends on
        required_by: [5],       # Feature IDs that depend on this
        notes: "Additional notes"
    )

    # Real, executable tests
    context "Core Functionality":
        it "does something specific":
            # Import modules
            use module.being_tested

            # Setup test data
            let input = "test"

            # Execute
            let result = function_under_test(input)

            # Assert
            expect result to eq expected_value

    context "Edge Cases":
        it "handles invalid input":
            expect invalid_input() to raise_error

    context "Performance":
        it "completes in reasonable time":
            expect benchmark() to be_lt 100  # ms
```

## Scaffolding New Tests

Use the scaffold script to generate test templates:

```bash
# Generate scaffold for a feature
python scripts/scaffold_feature_test.py doc/old_features/infrastructure/0001_lexer.md \
    > simple/std_lib/test/features/infrastructure_spec.spl

# Then manually:
# 1. Review and clean up generated metadata
# 2. Replace `skip` placeholders with real assertions
# 3. Import required modules
# 4. Add comprehensive test cases
```

## Running Feature Tests

```bash
# Run all feature tests
cargo test -p simple-driver simple_stdlib_features

# Run specific category
cargo test -p simple-driver simple_stdlib_features_infrastructure

# Run directly with Simple interpreter
./target/debug/simple simple/std_lib/test/features/infrastructure_spec.spl
```

## Generating Documentation

Feature tests automatically generate documentation in `doc/features/` when run.

The generated docs include:
- Feature metadata table
- Description
- Specification references
- Implementation files
- Test files
- Code examples
- Dependencies

To regenerate all docs:

```bash
# Run all feature tests (generates docs as side effect)
cargo test -p simple-driver simple_stdlib_features

# Or use the Simple interpreter
./target/debug/simple -e "use spec.feature_doc; write_feature_docs()"
```

## Test Quality Guidelines

### DO:
- ✅ Write real, executable assertions
- ✅ Test actual functionality, not placeholders
- ✅ Include edge cases and error conditions
- ✅ Use descriptive test names
- ✅ Add code examples in tests (they appear in docs)
- ✅ Keep metadata accurate and complete

### DON'T:
- ❌ Leave `skip` placeholders in committed code
- ❌ Write tests that always pass without checking anything
- ❌ Duplicate existing Rust tests (focus on integration/behavior)
- ❌ Test implementation details (test public API behavior)

## Workflow

### Adding a New Feature

1. **Write the test first** (TDD approach):
   ```bash
   python scripts/scaffold_feature_test.py doc/old_features/category/0001_feature.md \
       > simple/std_lib/test/features/category_spec.spl
   ```

2. **Fill in the test**:
   - Add imports
   - Write real assertions
   - Test all major functionality
   - Test edge cases

3. **Run the test**:
   ```bash
   cargo test -p simple-driver simple_stdlib_features_category
   ```

4. **Generate docs**:
   - Docs are generated automatically when tests run
   - Review generated markdown in `doc/features/category/`

5. **Compare with baseline**:
   ```bash
   diff doc/old_features/category/0001_feature.md \
        doc/features/category/0001_feature.md
   ```

6. **Commit**:
   ```bash
   jj describe -m "feat(tests): Add feature test for Feature (#ID)"
   ```

## Migration Status

Track migration progress:

```bash
./scripts/compare_features.sh
```

This shows which categories have been migrated and how many files remain.

## See Also

- [Feature Documentation Plan](/home/ormastes/.claude/plans/dynamic-launching-reddy.md)
- [BDD Framework Guide](../../std_lib/src/spec/README.md)
- [Test Policy](../../../doc/guides/test.md)
