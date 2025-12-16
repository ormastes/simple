# LLVM Coverage Integration Design

This document describes how to integrate LLVM-based code coverage into the Simple compiler.

## Overview

The Simple compiler uses LLVM as one of its backends. LLVM provides built-in support for code coverage through:

1. **Instrumentation-based profiling** - Inserts counters at compile time
2. **Source-based coverage mapping** - Maps coverage data back to source locations

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Simple Compilation Pipeline                   │
├─────────────────────────────────────────────────────────────────┤
│  Source (.spl) → AST → HIR → MIR → LLVM IR → Object Code       │
│                                      ↓                          │
│                              Coverage Instrumentation            │
│                                      ↓                          │
│                              .profraw files                      │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│                    Coverage Processing Pipeline                  │
├─────────────────────────────────────────────────────────────────┤
│  .profraw → llvm-profdata merge → .profdata                     │
│                                      ↓                          │
│  .profdata + binary → llvm-cov export → coverage.json           │
│                                      ↓                          │
│  coverage.json + public_api.yml → simple_mock_helper            │
│                                      ↓                          │
│                              Coverage Report                     │
└─────────────────────────────────────────────────────────────────┘
```

## Implementation Plan

### Phase 1: Basic Block Coverage (Current)

Enable LLVM's built-in instrumentation for basic block counting.

**Changes to LlvmBackend:**

```rust
pub struct LlvmBackend {
    target: Target,
    coverage_enabled: bool,  // NEW
    // ...
}

impl LlvmBackend {
    pub fn with_coverage(mut self, enabled: bool) -> Self {
        self.coverage_enabled = enabled;
        self
    }
}
```

**Instrumentation:**

When `coverage_enabled` is true:
1. Add `-fprofile-instr-generate` equivalent pass
2. Emit coverage mapping sections
3. Link with profiler runtime

### Phase 2: Source-Based Coverage Mapping

Map LLVM coverage regions back to Simple source locations.

**Coverage Mapping Data:**

```rust
pub struct CoverageRegion {
    pub file_id: u32,
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
    pub counter_id: u32,
}

pub struct CoverageMapping {
    pub files: Vec<String>,
    pub regions: Vec<CoverageRegion>,
}
```

**MIR Annotation:**

Add source location tracking to MIR instructions:

```rust
pub struct MirInst {
    pub kind: MirInstKind,
    pub span: Option<SourceSpan>,  // NEW - for coverage mapping
}
```

### Phase 3: Integration with Test Framework

Connect coverage data to BDD spec framework.

**Runtime API:**

```simple
# In std.spec
export fn with_coverage(block: Fn() -> Void) -> CoverageData:
    start_coverage()
    block()
    return stop_coverage()

export fn assert_coverage(data: CoverageData, threshold: Float):
    if data.percent() < threshold:
        panic("Coverage ${data.percent()}% below threshold ${threshold}%")
```

## LLVM API Usage

### Enabling Coverage in Module

```rust
#[cfg(feature = "llvm")]
fn enable_coverage(module: &Module) {
    // Set module flags for coverage
    module.add_module_flag(
        inkwell::module::FlagBehavior::Override,
        "ProfileData",
        1,  // Enable profile data
    );
}
```

### Creating Coverage Counters

```rust
#[cfg(feature = "llvm")]
fn create_coverage_counter(
    context: &Context,
    module: &Module,
    function: FunctionValue,
    block_id: u32,
) -> PointerValue {
    // Create global counter
    let counter_name = format!("__llvm_profile_counter_{}", block_id);
    let i64_type = context.i64_type();
    let counter = module.add_global(i64_type, None, &counter_name);
    counter.set_initializer(&i64_type.const_zero());
    counter.as_pointer_value()
}
```

### Incrementing Counters

At each basic block entry:

```rust
#[cfg(feature = "llvm")]
fn emit_counter_increment(
    builder: &Builder,
    counter_ptr: PointerValue,
) {
    let current = builder.build_load(counter_ptr, "counter");
    let one = context.i64_type().const_int(1, false);
    let incremented = builder.build_int_add(current, one, "inc");
    builder.build_store(counter_ptr, incremented);
}
```

## Integration with simple_mock_helper

The existing `simple_mock_helper::coverage` module already supports:

- Loading LLVM coverage JSON (`llvm-cov export -format=json`)
- Computing class/struct method coverage
- Checking coverage thresholds

### Usage Flow

```bash
# 1. Compile with coverage
simple build --coverage src/main.spl

# 2. Run tests (generates .profraw)
simple test

# 3. Merge profile data
llvm-profdata merge -o coverage.profdata *.profraw

# 4. Export coverage JSON
llvm-cov export -format=json -instr-profile=coverage.profdata ./target/main > coverage.json

# 5. Generate report
smh_coverage --cov coverage.json --api public_api.yml
```

## Configuration

### Cargo Feature

```toml
[features]
coverage = ["llvm"]
```

### CLI Flag

```bash
simple build --coverage    # Enable coverage instrumentation
simple test --coverage     # Run with coverage collection
```

### Environment Variable

```bash
SIMPLE_COVERAGE=1 simple test
```

## Files to Modify

| File | Changes |
|------|---------|
| `src/compiler/src/codegen/llvm/mod.rs` | Add coverage instrumentation |
| `src/compiler/src/codegen/llvm/coverage.rs` | NEW - Coverage mapping utilities |
| `src/compiler/src/mir/instructions.rs` | Add SourceSpan to instructions |
| `src/driver/src/cli/mod.rs` | Add --coverage flag |
| `Cargo.toml` | Add coverage feature |

## Testing

### Unit Tests

```rust
#[test]
fn test_coverage_counter_creation() {
    let backend = LlvmBackend::new(Target::host())
        .with_coverage(true);
    // Test counter is created
}

#[test]
fn test_coverage_increment_emitted() {
    // Test increment instruction is added to each block
}
```

### Integration Tests

```rust
#[test]
fn test_coverage_data_generated() {
    // Compile with coverage, run, verify .profraw exists
}
```

## See Also

- [LLVM Source-Based Code Coverage](https://clang.llvm.org/docs/SourceBasedCodeCoverage.html)
- [simple_mock_helper coverage module](../../src/util/simple_mock_helper/src/coverage.rs)
- [BDD Spec Framework](../spec/bdd_spec.md)
