# Feature BDD Specs

This directory contains BDD spec files that:
1. Test feature implementations
2. Generate feature documentation

## Directory Structure

```
features/
├── README.md                    # This file
├── _feature_spec_template.spl   # Template for new feature specs
│
├── infrastructure/              # Infrastructure features (#1-#9)
│   ├── lexer_spec.spl
│   ├── parser_spec.spl
│   └── ...
│
├── language/
│   ├── core/                    # Core language (#10-#49)
│   │   ├── types_spec.spl
│   │   ├── functions_spec.spl
│   │   └── ...
│   ├── metaprogramming/         # Metaprogramming (#1300-#1324)
│   ├── types/                   # Type system (#1330-#1342)
│   └── pattern_matching/        # Pattern matching (#1325-#1329)
│
├── codegen/                     # Code generation (#95-#103)
├── concurrency/                 # Concurrency (#1104-#1115, #1730-#1779)
├── testing/                     # Testing frameworks (#180-#197)
├── verification/                # Formal verification (#950-#970)
├── aop/                         # AOP (#1000-#1050)
├── tooling/                     # Dev tools (#1156-#1199, #1359-#1368)
├── mcp/                         # MCP Protocol (#1200-#1358)
├── ui/                          # UI frameworks (#1369-#1450, #1830-#1839)
├── gpu/                         # GPU/SIMD (#400-#418, #1450-#1509)
├── graphics/                    # 3D graphics (#1780-#1829)
├── game_engine/                 # Game engines (#1520-#1649)
├── ml/                          # ML/PyTorch (#1650-#1729)
├── database/                    # Database (#700-#799)
├── sdn/                         # SDN format (#1051-#1060)
├── llm_friendly/                # LLM features (#880-#919)
├── formatting/                  # Formatter/lints (#1131-#1145)
├── ffi/                         # FFI/ABI (#1116-#1130)
├── optimization/                # Performance (#1970-#2049)
└── math/                        # Simple Math (#1910-#1969)
```

## Creating a Feature Spec

1. Copy `_feature_spec_template.spl` to the appropriate category folder
2. Rename to `{feature_name}_spec.spl`
3. Fill in the `@feature:` metadata
4. Write BDD tests that exercise the feature
5. Run tests: `simple test features/`

## Feature Metadata

The `@feature:` attribute defines metadata exported to documentation:

```simple
@feature:
    id: 1000                     # Unique feature ID
    name: "Predicate Grammar"    # Short name
    category: "aop"              # Category folder
    difficulty: 3                # 1-5 scale
    status: "complete"           # complete/in_progress/planned
    impl: "R"                    # R/S/S+R
    spec_link: "research/aop.md" # Specification document
    impl_files:                  # Implementation files
        - file: "src/compiler/src/predicate.rs"
          purpose: "Predicate evaluation"
    depends_on: [1, 2]           # Dependencies
    required_by: [1006, 1007]    # Dependents
```

## Documentation Generation

When tests run, the spec runner:
1. Reads `@feature:` metadata
2. Extracts descriptions from docstrings
3. Collects examples from `context "Usage examples"`
4. Writes to `doc/features/{category}/{id}_{name}.md`

## Running Tests

```bash
# Run all feature specs
cargo test -p simple-driver simple_stdlib_system_features

# Run specific category
cargo test -p simple-driver simple_stdlib_system_features_aop

# Run specific feature
cargo test -p simple-driver simple_stdlib_system_features_aop_predicate_grammar

# Generate documentation only
simple test features/ --export-docs
```

## Best Practices

1. **One spec per feature**: Keep specs focused
2. **Descriptive contexts**: Group related behaviors
3. **Clear docstrings**: Extracted into documentation
4. **Real examples**: Show actual usage patterns
5. **Edge cases**: Document error handling
6. **Performance notes**: Include timing expectations
