//! Lifetime inference integration tests
//!
//! Tests for lifetime tracking during HIR lowering.

use simple_parser::Parser;

use crate::hir::lower::Lowerer;
use crate::hir::LifetimeViolation;

/// Helper to parse and lower with warnings
fn lower_with_warnings(source: &str) -> Result<crate::hir::LoweringOutput, crate::hir::LowerError> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    Lowerer::new().lower_module_with_warnings(&module)
}

/// Helper to check if lowering produces a lifetime violation error
fn has_lifetime_error(source: &str) -> bool {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    match Lowerer::new().lower_module_with_warnings(&module) {
        Err(crate::hir::LowerError::LifetimeViolation(_)) => true,
        Err(crate::hir::LowerError::LifetimeViolations(_)) => true,
        _ => false,
    }
}

#[test]
fn test_simple_function_lowers_without_lifetime_errors() {
    let source = r#"
fn add(a: i32, b: i32) -> i32:
    a + b
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Simple function should lower without errors");
}

#[test]
fn test_block_scope_tracking() {
    let source = r#"
fn test_blocks():
    val x = 1
    if x > 0:
        val y = 2
        y + x
    else:
        val z = 3
        z + x
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Block scopes should be tracked correctly");
}

#[test]
fn test_nested_blocks() {
    let source = r#"
fn nested_test():
    val outer = 1
    if outer > 0:
        val mid = 2
        if mid > 0:
            val inner = 3
            inner + mid + outer
        else:
            mid + outer
    else:
        outer
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Nested blocks should be tracked correctly");
}

#[test]
fn test_function_with_loop() {
    let source = r#"
fn loop_test() -> i32:
    var sum: i32 = 0
    var i: i32 = 0
    while i < 10:
        sum = sum + i
        i = i + 1
    sum
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Loops should be tracked correctly: {:?}", result.err());
}

#[test]
fn test_variable_registration() {
    let source = r#"
fn var_test():
    val x = 10
    val y = x * 2
    val z = y + x
    z
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Variables should be registered with lifetimes");
}

#[test]
fn test_parameter_lifetime() {
    let source = r#"
fn with_params(a: i32, b: i32) -> i32:
    val local: i32 = a
    local + b
"#;

    let result = lower_with_warnings(source);
    assert!(
        result.is_ok(),
        "Parameters should have 'static-like lifetimes: {:?}",
        result.err()
    );
}

#[test]
fn test_struct_method_lifetime() {
    let source = r#"
struct Point:
    x: i32
    y: i32

impl Point:
    fn magnitude() -> i32:
        self.x * self.x + self.y * self.y
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Struct methods should track lifetimes correctly");
}

#[test]
fn test_class_method_lifetime() {
    let source = r#"
class Counter:
    count: i32

    fn new() -> Counter:
        Counter { count: 0 }

    fn increment():
        self.count = self.count + 1

    fn get_count() -> i32:
        self.count
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Class methods should track lifetimes correctly");
}

#[test]
fn test_memory_warnings_no_false_positives() {
    // This code should not produce memory warnings
    let source = r#"
fn safe_code():
    val x = 10
    val y = x + 5
    y
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    assert!(!result.has_warnings(), "Safe code should have no warnings");
}

#[test]
fn test_lean4_generation_basic() {
    let source = r#"
fn simple():
    42
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");

    // Generate Lean 4 verification
    let lean = crate::codegen::lean::generate_memory_safety_lean(&result.module, None, Some(&result.warnings));

    // Check basic structure
    assert!(lean.contains("namespace"), "Should have namespace");
    assert!(lean.contains("MemorySafety"), "Should have MemorySafety namespace");
    assert!(lean.contains("inductive PointerKind"), "Should define PointerKind");
    assert!(lean.contains("def safeBorrow"), "Should define safeBorrow");
}

#[test]
fn test_lean4_generation_with_warnings() {
    let source = r#"
fn has_var():
    var x = 10
    x = x + 1
    x
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");

    // Generate Lean 4 verification
    let lean = crate::codegen::lean::generate_memory_safety_lean(&result.module, None, Some(&result.warnings));

    // Should still generate valid Lean code
    assert!(lean.contains("namespace"), "Should have namespace");
    assert!(lean.contains("end"), "Should have end namespace");
}

// ============================================================================
// Memory Safety Warning Tests (W1001-W1006)
// ============================================================================
// These tests demonstrate the compile-time memory safety checking.
// Currently emits warnings; in strict mode (Rust-level safety), these become errors.

/// Helper to lower with strict memory mode (warnings become errors)
fn lower_strict(source: &str) -> Result<crate::hir::LoweringOutput, crate::hir::LowerError> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    Lowerer::with_strict_memory_mode().lower_module_with_warnings(&module)
}

/// Helper to count warnings of a specific code
fn count_warnings(result: &crate::hir::LoweringOutput, code_prefix: &str) -> usize {
    result.warnings.warnings().iter()
        .filter(|w| w.code.to_string().starts_with(code_prefix))
        .count()
}

#[test]
fn test_w1003_mutable_shared_binding_warning() {
    // W1003: Mutable binding with shared pointer type
    // `var x: *T` is suspicious - shared pointers are reference counted,
    // reassigning the variable doesn't mutate the data
    let source = r#"
struct Data:
    value: i32

fn test_mutable_shared():
    var x: *Data = Data { value: 10 }
    x = Data { value: 20 }
    x.value
"#;

    let result = lower_with_warnings(source);
    // Should succeed but may have warnings about shared pointer semantics
    assert!(result.is_ok(), "Should compile: {:?}", result.err());
}

#[test]
fn test_safe_immutable_binding() {
    // val (immutable) binding is preferred for shared pointers
    let source = r#"
struct Data:
    value: i32

fn test_immutable_shared():
    val x: *Data = Data { value: 10 }
    x.value
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    // No memory warnings for proper immutable usage
    assert!(!result.has_warnings(), "Immutable shared pointer should have no warnings");
}

#[test]
fn test_unique_pointer_move_semantics() {
    // Unique pointers (&T) should be moved, not copied
    let source = r#"
struct Node:
    data: i32

fn test_unique():
    val node: &Node = Node { data: 42 }
    val alias = node
    alias.data
"#;

    let result = lower_with_warnings(source);
    // This may warn about implicit copy of unique pointer (W1002)
    assert!(result.is_ok(), "Should compile: {:?}", result.err());
}

#[test]
fn test_reference_capability_shared() {
    // T (Shared capability) - multiple readers allowed
    let source = r#"
fn test_shared_refs():
    val x: i32 = 42
    val r1 = x
    val r2 = x
    r1 + r2
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    assert!(!result.has_warnings(), "Multiple readers should be safe");
}

#[test]
fn test_basic_mutation_tracking() {
    // var allows mutation
    let source = r#"
fn test_mutation():
    var counter: i32 = 0
    counter = counter + 1
    counter = counter + 1
    counter
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    // Basic mutation of value types is always safe
    assert!(!result.has_warnings(), "Value type mutation should be safe");
}

#[test]
fn test_struct_field_mutation() {
    // Mutation through mut T capability
    let source = r#"
struct Counter:
    value: i32

fn test_field_mutation():
    var c = Counter { value: 0 }
    c.value = c.value + 1
    c.value
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Field mutation should compile: {:?}", result.err());
}

#[test]
fn test_no_aliasing_violation() {
    // No aliasing issues with value types
    let source = r#"
fn test_values():
    val a: i32 = 10
    val b: i32 = a
    val c: i32 = a
    a + b + c
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    assert!(!result.has_warnings(), "Value semantics should have no aliasing issues");
}

// ============================================================================
// Strict Mode Tests (Rust-Level Safety)
// ============================================================================
// When strict mode is enabled, memory warnings become errors.
// This achieves Rust-level memory safety guarantees.

#[test]
fn test_strict_mode_basic_safe_code() {
    // Safe code should pass even in strict mode
    let source = r#"
fn safe_add(a: i32, b: i32) -> i32:
    a + b
"#;

    let result = lower_strict(source);
    assert!(result.is_ok(), "Safe code should pass strict mode: {:?}", result.err());
}

#[test]
fn test_strict_mode_immutable_preferred() {
    // Immutable bindings are always safe
    let source = r#"
fn test_immutable():
    val x = 10
    val y = 20
    x + y
"#;

    let result = lower_strict(source);
    assert!(result.is_ok(), "Immutable code should pass strict mode");
}

// ============================================================================
// Capability System Tests
// ============================================================================

#[test]
fn test_capability_shared_read_only() {
    // T (Shared) capability allows reads
    let source = r#"
struct Point:
    x: i32
    y: i32

fn read_point(p: Point) -> i32:
    p.x + p.y
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    assert!(!result.has_warnings(), "Reading shared data should be safe");
}

#[test]
fn test_capability_exclusive_mutation() {
    // mut T (Exclusive) capability allows mutation
    let source = r#"
struct Counter:
    value: i32

impl Counter:
    me increment():
        self.value = self.value + 1
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Exclusive mutation should compile: {:?}", result.err());
}

// ============================================================================
// Summary: Path to Rust-Level Memory Safety
// ============================================================================
//
// Current State:
// - Memory safety checks exist (W1001-W1006)
// - Emit warnings by default for gradual adoption
// - Strict mode available to promote warnings to errors
//
// To achieve Rust-level safety:
// 1. Enable strict mode by default
// 2. Integrate capability checking with all assignments
// 3. Complete borrow checker integration
// 4. Verify all violations produce errors, not just warnings
//
// The theoretical foundation is proven in Lean 4 (MemoryCapabilities.lean)
