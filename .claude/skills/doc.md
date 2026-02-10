# Documentation Writing Skill

Documentation in Simple follows a "specification as code" philosophy - executable tests generate documentation, and research documents inform implementation.

## Documentation Types & Locations

| Type | Location | Format | Purpose |
|------|----------|--------|---------|
| Research | `doc/research/` | Markdown | Investigation, analysis, design exploration |
| Design | `doc/design/` | Markdown | Architecture decisions, system design |
| Guides | `doc/guide/` | Markdown | User-facing tutorials, how-to guides |
| Specifications | `src/std/test/features/` | SSpec (`.spl`) | Executable feature specs that generate docs |
| API Docs | Generated | Markdown | Auto-generated from SSpec tests |
| Reports | `doc/report/` | Markdown | Session summaries, completion reports |

## Critical Rules

### Specifications MUST be SSpec
- ❌ **NEVER write spec.md files** - write `*_spec.spl` instead
- ✅ Specifications are executable tests in `src/std/test/features/`
- ✅ Use SSpec framework to generate documentation from tests
- ✅ See `/sspec` skill for test writing guidelines

### Research Documents
- ✅ Write in `doc/research/` for investigation and analysis
- ✅ Include implementation roadmaps and design explorations
- ✅ Reference existing infrastructure and integration points
- ✅ Provide concrete code examples

### Documentation Hierarchy
```
doc/
├── research/          # Investigation, analysis
│   ├── torch_improvements.md
│   ├── async_ui_architecture.md
│   └── ...
├── design/            # Architecture decisions
│   ├── tensor_dimensions_design.md
│   └── ...
├── guide/             # User-facing guides
│   ├── tensor_dimensions_guide.md
│   └── ...
├── report/            # Session reports
└── spec/              # NON-executable specs only
    └── tooling/       # Tooling-specific (not feature specs)

src/std/test/features/  # EXECUTABLE feature specs
├── ml/
│   ├── config_system_spec.spl
│   ├── experiment_tracking_spec.spl
│   └── ...
├── data_structures/
│   ├── tensor_dimensions_spec.spl
│   └── ...
```

## SSpec Feature Specification Format

Feature specs are executable tests with metadata:

```simple
# Feature Name Feature Specification
# Feature #ID: Short description
# Category: Category | Difficulty: N | Status: Planned|Implementing|Complete

# =====================================================
# Feature Metadata
# =====================================================

class FeatureMetadata:
    id: Int
    name: String
    category: String
    difficulty: Int
    status: String
    impl_type: String
    spec_ref: String
    files: List<String>
    tests: List<String>
    description: String
    code_examples: List<String>
    dependencies: List<Int>
    required_by: List<Int>
    notes: String

let FEATURE = FeatureMetadata {
    id: 193,
    name: "Feature Name",
    category: "Category",
    difficulty: 4,
    status: "Implementing",
    impl_type: "Simple",
    spec_ref: "doc/spec/generated/feature_name.md",
    files: [
        "path/to/implementation.spl"
    ],
    tests: [
        "path/to/tests_spec.spl"
    ],
    description: "Clear, concise description of what this feature does.",
    code_examples: [
        "# Example 1",
        "let x = Feature.new()",
        "",
        "# Example 2",
        "x.do_something()"
    ],
    dependencies: [],
    required_by: [],
    notes: "Implementation notes, caveats, references."
}

# =====================================================
# BDD Specification Tests
# =====================================================

print("============================================================")
print("  FEATURE NAME SPECIFICATION")
print("  Category: Category | Status: Planned")
print("============================================================")
print("")

# describe "Feature behavior"
print("describe Feature behavior:")

# it "does something"
print("  it does something:")
# TODO: Implement test
print("    [TODO] Not yet implemented")

# =====================================================
# Implementation Roadmap
# =====================================================

# Phase 1: Core (Week 1-2)
# - [ ] Task 1
# - [ ] Task 2

# Phase 2: Advanced (Week 3-4)
# - [ ] Task 3
```

## Research Document Format

Research documents inform implementation with design analysis:

```markdown
# Title - Research & Implementation Plan

**Date:** YYYY-MM-DD
**Status:** Research Phase
**Related Specs:** Links to related spec files

---

## Executive Summary

1-2 paragraph overview of the research findings and proposed solution.

---

## 1. Problem Analysis

### 1.1 Current State
What exists now and what are the limitations?

### 1.2 Requirements
What needs to be achieved?

---

## 2. Proposed Solution

### 2.1 Architecture Overview
High-level design with ASCII diagrams if needed.

### 2.2 Key Components
Detailed description of each component.

### 2.3 Code Examples
```simple
# Concrete code examples showing the API
```

---

## 3. Integration with Existing Infrastructure

How does this harmonize with existing Simple code?

### 3.1 Existing Infrastructure
- `src/runtime/...` - What can be reused
- `src/compiler/...` - What needs extension

### 3.2 New Components
- What needs to be built from scratch

---

## 4. Implementation Roadmap

### Phase 1: Core (Week 1-2)
- [ ] Task 1
- [ ] Task 2

### Phase 2: Advanced (Week 3-4)
- [ ] Task 3

---

## 5. Testing Strategy

### 5.1 Unit Tests
```simple
# Example unit test structure
```

### 5.2 Integration Tests
```simple
# Example integration test
```

---

## 6. References

- Related documentation
- External inspirations
- Prior art
```

## Design Document Format

Design documents explain architectural decisions:

```markdown
# Component Design

**Status:** Draft | Review | Approved
**Owner:** Team/Person
**Last Updated:** YYYY-MM-DD

---

## Overview

What is this component and why does it exist?

## Design Principles

1. Principle 1 - Why it matters
2. Principle 2 - Why it matters

## Architecture

### Components

#### Component A
- **Responsibility:** What it does
- **Interface:** Key API surface
- **Implementation:** How it works

### Data Flow

```
Input → Component A → Component B → Output
```

### State Management

How is state handled?

## API Design

```simple
# Public API
class Component:
    fn do_something(self, arg: Type) -> Result
```

## Error Handling

How are errors propagated and handled?

## Performance Considerations

- Time complexity
- Space complexity
- Bottlenecks

## Security Considerations

What security implications exist?

## Alternatives Considered

### Alternative 1
- Pros
- Cons
- Why not chosen

## Open Questions

1. Question 1
2. Question 2

## References

- Related designs
- External resources
```

## User Guide Format

User guides teach how to use features:

```markdown
# Feature Name - User Guide

**Audience:** Developers using this feature
**Prerequisites:** What you need to know first

---

## Quick Start

5-minute minimal example to get started:

```simple
# Minimal working example
let x = Feature.new()
x.use()
```

---

## Core Concepts

### Concept 1
Explanation with examples

### Concept 2
Explanation with examples

---

## Common Patterns

### Pattern 1: Use Case Name

```simple
# Full example showing the pattern
```

**When to use:** Specific scenarios

**When NOT to use:** Anti-patterns

### Pattern 2: Another Use Case

```simple
# Another full example
```

---

## API Reference

### Core Functions

#### `function_name(arg: Type) -> Result`
Description of what it does.

**Parameters:**
- `arg` - What this parameter means

**Returns:**
- What is returned

**Errors:**
- When errors occur

**Example:**
```simple
# Usage example
```

---

## Advanced Usage

### Advanced Feature 1
For power users

### Advanced Feature 2
Complex scenarios

---

## Troubleshooting

### Problem 1
**Symptom:** What you see
**Cause:** Why it happens
**Solution:** How to fix

### Problem 2
...

---

## Best Practices

1. Do this
2. Don't do that
3. Consider this

---

## Examples

### Example 1: Real-World Scenario
Full working example with explanation

### Example 2: Another Scenario
Another complete example

---

## See Also

- Related guides
- API documentation
- Design documents
```

## SDN Configuration Format

Use SDN for configuration and structured data:

```sdn
# config.sdn - Human-readable configuration format

project = my-project
version = 1.0.0

# Nested configuration
server:
    host = localhost
    port = 8080
    workers = 4

# Arrays
features = [auth, logging, metrics]

# Tables for structured data
users |id, name, role|
    1, Alice, admin
    2, Bob, user
    3, Carol, user

# Comments are supported
# Interpolation works: ${project}/logs
```

## Documentation Standards

### Writing Style
- **Clear and concise** - No fluff
- **Active voice** - "The function returns X" not "X is returned"
- **Present tense** - "The system does X" not "The system will do X"
- **Code examples** - Show, don't just tell
- **Real-world scenarios** - Practical, not theoretical

### Code Examples
- **Working examples** - Must be executable
- **Minimal examples** - Strip unnecessary complexity
- **Commented** - Explain non-obvious parts
- **Complete** - Include imports, setup, teardown

### Formatting
- **Headings** - Use semantic hierarchy (# → ## → ###)
- **Lists** - Bullet points for items, numbered for steps
- **Code blocks** - Always specify language (```simple, ```bash, ```sdn)
- **Tables** - For comparisons and reference data
- **Diagrams** - ASCII art for simple diagrams

### Cross-References
- **Relative links** - Use relative paths: `doc/design/feature.md`
- **Skill references** - Link skills: "See `/sspec` skill"
- **Feature references** - Link specs: "Feature #193"

## Documentation Workflow

### 1. Research Phase
Write research document exploring the problem and solutions.

Location: `doc/research/`

### 2. Design Phase
Create design document with architectural decisions.

Location: `doc/design/`

### 3. Specification Phase
Write executable SSpec feature specification.

Location: `src/std/test/features/*/`

### 4. Implementation Phase
Implement code with inline documentation.

### 5. Guide Phase
Write user guide once feature is stable.

Location: `doc/guide/`

### 6. Generation Phase
Run doc generator to create API docs from SSpec.

```bash
# Generate documentation from specs
bin/simple src/std/test/features/generate_docs.spl
```

## Common Pitfalls

### ❌ Don't: Write standalone spec.md files
Specs should be executable SSpec tests, not markdown documents.

### ❌ Don't: Mix research and specification
Research goes in `doc/research/`, executable specs in `test/features/`.

### ❌ Don't: Write vague examples
Show concrete, working code that users can copy-paste.

### ❌ Don't: Document implementation details
Document behavior and interfaces, not internal implementation.

### ✅ Do: Write executable specifications
Use SSpec format so tests validate the documentation.

### ✅ Do: Include roadmaps
Show implementation phases with checkboxes.

### ✅ Do: Reference existing infrastructure
Show how new code integrates with existing systems.

### ✅ Do: Provide complete examples
Include setup, usage, and cleanup in examples.

## Tools

### Doc Generation
```bash
# Generate docs from SSpec tests
bin/simple src/std/test/features/generate_docs.spl

# Outputs to: doc/spec/generated/
```

## Examples from Codebase

### Good: Executable Specification
`src/std/test/features/data_structures/tensor_dimensions_spec.spl`
- Executable test with metadata
- Generates documentation
- Includes code examples
- Has implementation roadmap

### Good: Research Document
`doc/research/async_ui_architecture.md`
- Thorough problem analysis
- Proposed solutions with examples
- Integration strategy
- Implementation roadmap

### Good: Design Document
`doc/design/tensor_dimensions_design.md`
- Clear architecture overview
- Component breakdown
- Design decisions explained
- Alternatives considered

### Good: User Guide
`doc/guide/tensor_dimensions_guide.md`
- Quick start example
- Core concepts explained
- Common patterns shown
- Real-world examples

## See Also

- `/sspec` - SSpec test writing
- `/test` - Test writing guidelines
- `/research` - Codebase exploration
- Feature DB: `doc/feature/feature_db.sdn`
