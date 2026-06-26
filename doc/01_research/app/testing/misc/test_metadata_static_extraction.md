# Research: Static Test Metadata Extraction

## Problem Statement

Currently, test metadata (skip, slow, ignore, tags) requires executing DSL code to discover tests. This means:
- `simple test --list` must execute all `describe/it` blocks
- Large test suites take significant time just to list tests
- No static analysis capability for IDE tooling

**Goal:** Extract test metadata at parse time (like formatted strings) without instantiating test classes/functions.

---

## Reference Pattern: Formatted String Metadata

### How FStrings Store Metadata

**File:** `src/rust/parser/src/ast/nodes/const_meta.rs`

The formatted string system extracts placeholder keys at parse time:

```rust
// Core structures for compile-time metadata
pub enum MetaValue {
    String(String),
    Integer(i64),
    Bool(bool),
    StringSet(Vec<String>),  // For const_keys: ["name", "count"]
    Dict(HashMap<String, MetaValue>),
    Null,
}

pub struct ConstMeta {
    pub entries: HashMap<String, MetaValue>,
}

pub struct TypeMeta {
    pub meta: ConstMeta,  // Type-level metadata (shared by all instances)
}

pub struct ObjMeta {
    pub meta: ConstMeta,
    pub has_explicit_meta: bool,  // Instance-specific metadata
}
```

### Key Pattern: Static Key Extraction

```rust
// Extract keys from FString parts WITHOUT execution
pub fn extract_fstring_keys(parts: &[FStringPart]) -> Vec<String> {
    parts.iter().filter_map(|part| match part {
        FStringPart::Expr(expr) => extract_expr_key(expr),
        FStringPart::Literal(_) => None,
    }).collect()
}
```

**Key insight:** The keys are extracted by analyzing AST structure, not by running code.

### Resolution Hierarchy

```
ObjMeta (instance) -> TypeMeta (type) -> DefaultMeta (fallback)
```

This allows compile-time validation without runtime instantiation.

---

## Current Test Framework Architecture

### Registry (Simple Language)

**File:** `src/lib/std/src/spec/registry.spl`

```simple
class Example:
    description: text
    block: fn()
    is_skipped: bool
    tags: List<text>
    timeout_seconds: Option<i32>
    resource_limits: Option<ResourceLimits>
```

### DSL Functions

**File:** `src/lib/std/src/spec/dsl.spl`

```simple
fn it(description: text, block: fn()):
    match current_group:
        case Some(group):
            val example = Example.new(description, block)
            group.add_example(example)

fn slow_it(description: text, block: fn()):
    match current_group:
        case Some(group):
            val limits = ResourceLimits.default_test_limits()
            val example = Example.new(description, block).slow().with_resource_limits(limits)
            group.add_example(example)
```

**Problem:** `Example.new()` is called at runtime, requiring DSL execution.

### Current Discovery

**File:** `src/rust/driver/src/cli/test_discovery.rs`

Uses regex to scan file content:
- `#[tag("name")]` decorator
- `@tag name` comment
- `@slow`, `@skip` shorthand
- File name patterns (`slow_spec.spl`)

This is file-level only, doesn't extract individual test metadata.

---

## Proposed Design: Static Test Metadata

### Reuse ConstMeta System

Create test-specific metadata using the same pattern:

```rust
// New file: src/rust/parser/src/ast/nodes/test_meta.rs

use super::const_meta::{ConstMeta, MetaValue};

/// Static test metadata (extracted at parse time)
#[derive(Debug, Clone, Default)]
pub struct TestMeta {
    pub meta: ConstMeta,
}

impl TestMeta {
    // Standard keys
    const KEY_DESCRIPTION: &'static str = "description";
    const KEY_IS_SKIPPED: &'static str = "is_skipped";
    const KEY_IS_SLOW: &'static str = "is_slow";
    const KEY_IS_IGNORED: &'static str = "is_ignored";
    const KEY_TAGS: &'static str = "tags";
    const KEY_TIMEOUT: &'static str = "timeout_seconds";

    pub fn description(&self) -> Option<&str> {
        self.meta.get(Self::KEY_DESCRIPTION)?.as_string()
    }

    pub fn is_skipped(&self) -> bool {
        self.meta.get(Self::KEY_IS_SKIPPED)
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }

    pub fn is_slow(&self) -> bool {
        self.meta.get(Self::KEY_IS_SLOW)
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }

    pub fn tags(&self) -> Option<&Vec<String>> {
        self.meta.get(Self::KEY_TAGS)?.as_string_set()
    }
}

/// Group metadata (describe/context)
#[derive(Debug, Clone)]
pub struct TestGroupMeta {
    pub meta: ConstMeta,
    pub tests: Vec<TestMeta>,
    pub children: Vec<TestGroupMeta>,
}

/// File-level metadata
#[derive(Debug, Clone, Default)]
pub struct FileTestMeta {
    pub groups: Vec<TestGroupMeta>,
}
```

### Static Analyzer

Extract metadata by walking AST:

```rust
// New file: src/rust/parser/src/test_analyzer.rs

pub fn extract_file_test_meta(stmts: &[Stmt]) -> FileTestMeta {
    let mut analyzer = TestMetaAnalyzer::new();
    analyzer.visit_stmts(stmts);
    analyzer.finish()
}

impl TestMetaAnalyzer {
    fn visit_call(&mut self, decorators: &[Decorator], callee: &Expr, args: &[Argument]) {
        if let Expr::Identifier(name) = callee {
            match name.as_str() {
                "describe" | "context" => self.visit_group(args),
                "it" => self.visit_test(decorators, args, TestKind::Normal),
                "slow_it" => self.visit_test(decorators, args, TestKind::Slow),
                "skip_it" | "skip" => self.visit_test(decorators, args, TestKind::Skipped),
                "ignore_it" => self.visit_test(decorators, args, TestKind::Ignored),
                _ => {}
            }
        }
    }

    fn visit_test(&mut self, decorators: &[Decorator], args: &[Argument], kind: TestKind) {
        let mut meta = ConstMeta::new();

        // Extract description from first argument
        if let Some(Argument::Positional(Expr::String(desc))) = args.first() {
            meta.set("description".into(), MetaValue::String(desc.clone()));
        }

        // Set flags based on DSL function
        match kind {
            TestKind::Slow => meta.set("is_slow".into(), MetaValue::Bool(true)),
            TestKind::Skipped => meta.set("is_skipped".into(), MetaValue::Bool(true)),
            TestKind::Ignored => meta.set("is_ignored".into(), MetaValue::Bool(true)),
            _ => {}
        }

        // Extract decorator metadata (@slow, @skip, @tag("name"))
        for decorator in decorators {
            self.apply_decorator_meta(&mut meta, decorator);
        }

        self.add_test(TestMeta { meta });
    }

    fn apply_decorator_meta(&self, meta: &mut ConstMeta, decorator: &Decorator) {
        match &decorator.name {
            Expr::Identifier(name) => match name.as_str() {
                "slow" => meta.set("is_slow".into(), MetaValue::Bool(true)),
                "skip" => meta.set("is_skipped".into(), MetaValue::Bool(true)),
                "ignore" => meta.set("is_ignored".into(), MetaValue::Bool(true)),
                "tag" => {
                    // Extract tag from @tag("name")
                    if let Some(args) = &decorator.args {
                        // Add to tags StringSet
                    }
                }
                _ => {}
            }
            _ => {}
        }
    }
}
```

---

## Benefits

1. **Fast listing:** `simple test --list` parses files, doesn't execute
2. **IDE support:** Static metadata enables hover info, test tree
3. **Compile-time validation:** Check for duplicate test names, invalid tags
4. **Consistent pattern:** Reuses existing `ConstMeta` infrastructure

---

## Implementation Phases

### Phase 1: Metadata Structures
- Create `TestMeta`, `TestGroupMeta`, `FileTestMeta`
- Reuse `ConstMeta` and `MetaValue`

### Phase 2: Static Analyzer
- Create `TestMetaAnalyzer` AST visitor
- Extract metadata from DSL calls and decorators

### Phase 3: Registry Integration
- Add `StaticTestRegistry` for fast queries
- Update test runner to use static registry for list mode

### Phase 4: DSL Enhancement
- Support decorator syntax: `@slow it "test":`
- Both approaches work (DSL functions + decorators)

---

## Files to Create/Modify

| File | Action | Purpose |
|------|--------|---------|
| `src/rust/parser/src/ast/nodes/test_meta.rs` | Create | Test metadata structures |
| `src/rust/parser/src/test_analyzer.rs` | Create | Static AST analyzer |
| `src/rust/driver/src/static_test_registry.rs` | Create | Fast query interface |
| `src/rust/parser/src/ast/nodes/mod.rs` | Modify | Export new module |
| `src/rust/driver/src/cli/test_runner/runner.rs` | Modify | Use static registry |
| `src/rust/driver/src/cli/test_discovery.rs` | Modify | Use static analyzer |
