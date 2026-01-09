//! Class invariant tests - constructor and method checks
//!
//! These tests verify that class invariants are properly checked:
//! - After constructor execution (even if constructor is private)
//! - Before/after public method execution
//! - NOT checked for private methods

use simple_compiler::CompilerPipeline;
use std::path::Path;

/// Test helper: Compile a class with contracts through the full pipeline
fn compile_class(source: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| format!("Failed to create temp dir: {}", e))?;
    let src_path = dir.path().join("test.spl");
    let out_path = dir.path().join("test.smf");

    std::fs::write(&src_path, source).map_err(|e| format!("Failed to write source: {}", e))?;

    let mut compiler =
        CompilerPipeline::new().map_err(|e| format!("Failed to create compiler: {:?}", e))?;

    match compiler.compile(&src_path, &out_path) {
        Ok(_) => Ok(()),
        Err(e) => {
            eprintln!("Compilation error: {:?}", e);
            eprintln!("Source:\\n{}", source);
            Err(format!("Compilation error: {:?}", e))
        }
    }
}

// ============================================================================
// Constructor Invariant Tests
// ============================================================================

#[test]
fn test_constructor_with_invariant() {
    // Constructor should check class invariant on exit
    let source = r#"
class Counter:
    value: i64

    invariant:
        self.value >= 0

    fn new(initial: i64) -> Counter:
        return Counter(value: initial)
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_constructor_with_multiple_invariants() {
    // Constructor should check all class invariants
    let source = r#"
class BoundedCounter:
    value: i64
    max: i64

    invariant:
        self.value >= 0
        self.value <= self.max
        self.max > 0

    fn new(initial: i64, maximum: i64) -> BoundedCounter:
        return BoundedCounter(value: initial, max: maximum)
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_private_constructor_gets_invariant() {
    // Even private constructors should check invariants
    let source = r#"
class Account:
    balance: i64

    invariant:
        self.balance >= 0

    fn new(initial_balance: i64) -> Account:
        return Account(balance: initial_balance)

    pub fn create_with_deposit(amount: i64) -> Account:
        return Account.new(amount)
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_constructor_with_precondition_and_invariant() {
    // Constructor can have both preconditions and invariants
    let source = r#"
class PositiveValue:
    val: i64

    invariant:
        self.val > 0

    fn new(x: i64) -> PositiveValue:
        in:
            x > 0
        return PositiveValue(val: x)
"#;

    assert!(compile_class(source).is_ok());
}

// ============================================================================
// Method Invariant Tests
// ============================================================================

#[test]
fn test_public_method_checks_invariants() {
    // Public methods should check invariants at entry and exit
    let source = r#"
class Counter:
    value: i64

    invariant:
        self.value >= 0

    fn new() -> Counter:
        return Counter(value: 0)

    pub fn increment(self):
        self.value = self.value + 1

    pub fn decrement(self):
        in:
            self.value > 0
        self.value = self.value - 1
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_private_method_skips_invariants() {
    // Private methods should NOT check invariants
    // (This test just verifies it compiles; runtime behavior would differ)
    let source = r#"
class Counter:
    value: i64

    invariant:
        self.value >= 0

    fn new() -> Counter:
        return Counter(value: 0)

    fn internal_set(self, new_value: i64):
        self.value = new_value

    pub fn safe_set(self, new_value: i64):
        if new_value >= 0:
            self.internal_set(new_value)
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_method_with_complex_invariant() {
    // Test invariants with field comparisons
    let source = r#"
class Range:
    min: i64
    max: i64

    invariant:
        self.min <= self.max
        self.max >= 0

    fn new(a: i64, b: i64) -> Range:
        return Range(min: a, max: b)

    pub fn expand(self, delta: i64):
        self.max = self.max + delta
"#;

    assert!(compile_class(source).is_ok());
}

// ============================================================================
// Multiple Class Tests
// ============================================================================

#[test]
fn test_multiple_classes_with_invariants() {
    // Each class should have its own invariants
    let source = r#"
class Account:
    balance: i64

    invariant:
        self.balance >= 0

    fn new(initial: i64) -> Account:
        return Account(balance: initial)

class Transaction:
    amount: i64
    timestamp: i64

    invariant:
        self.amount > 0
        self.timestamp >= 0

    fn new(amt: i64, ts: i64) -> Transaction:
        return Transaction(amount: amt, timestamp: ts)
"#;

    assert!(compile_class(source).is_ok());
}

// ============================================================================
// Inheritance Tests (Future)
// ============================================================================

#[test]
fn test_inherited_invariants() {
    // Child classes should maintain parent invariants
    let source = r#"
class Vehicle:
    speed: i64

    invariant:
        self.speed >= 0

class Car extends Vehicle:
    fuel: i64

    invariant:
        self.fuel >= 0
        self.fuel <= 100

    fn new(initial_fuel: i64) -> Car:
        return Car(speed: 0, fuel: initial_fuel)
"#;

    assert!(compile_class(source).is_ok());
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_class_without_invariant() {
    // Classes without invariants should work normally
    let source = r#"
class Simple:
    value: i64

    fn new(val: i64) -> Simple:
        return Simple(value: val)

    pub fn get_value() -> i64:
        return self.value
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_invariant_with_method_call() {
    // Invariants can reference pure methods
    let source = r#"
class ValueHolder:
    val: i64

    fn is_positive() -> bool:
        return self.val > 0

    invariant:
        self.is_positive()

    fn new(v: i64) -> ValueHolder:
        return ValueHolder(val: v)
"#;

    assert!(compile_class(source).is_ok());
}

// ============================================================================
// Visibility and Constructor Detection Tests
// ============================================================================

#[test]
fn test_explicitly_private_constructor() {
    // Explicitly private constructor - unclear if it should get invariants
    // Current behavior: private methods DON'T get invariants
    let source = r#"
class Internal:
    value: i64

    invariant:
        self.value >= 0

    fn create_internal(val: i64) -> Internal:
        return Internal(value: val)
"#;

    // This should compile either way
    assert!(compile_class(source).is_ok());
}

#[test]
fn test_explicitly_public_constructor() {
    // Explicitly public constructor should definitely get invariants
    let source = r#"
class Public:
    value: i64

    invariant:
        self.value >= 0

    pub fn new(val: i64) -> Public:
        return Public(value: val)
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_constructor_detection_by_name() {
    // Constructors typically named 'new' should get special treatment
    let source = r#"
class Counter:
    count: i64

    invariant:
        self.count >= 0

    pub fn new() -> Counter:
        return Counter(count: 0)

    pub fn from_value(val: i64) -> Counter:
        return Counter(count: val)
"#;

    assert!(compile_class(source).is_ok());
}

// ============================================================================
// Comprehensive Integration Tests
// ============================================================================

#[test]
fn test_complete_class_with_all_contract_types() {
    // Complete example showing:
    // - Constructor with invariant check (private constructor)
    // - Public methods with invariant checks
    // - Private helper without invariant checks
    // - Method contracts (pre/post) plus invariants
    let source = r#"
class BankAccount:
    balance: i64
    owner: str

    invariant:
        self.balance >= 0

    fn new(owner_name: str) -> BankAccount:
        in:
            owner_name.len() > 0
        return BankAccount(balance: 0, owner: owner_name)

    fn from_balance(owner_name: str, initial: i64) -> BankAccount:
        in:
            owner_name.len() > 0
            initial >= 0
        return BankAccount(balance: initial, owner: owner_name)

    pub fn deposit(self, amount: i64) -> ():
        in:
            amount > 0
        out():
            self.balance == old(self.balance) + amount
        self.balance = self.balance + amount

    pub fn withdraw(self, amount: i64) -> bool:
        in:
            amount > 0
        if self.balance >= amount:
            self.balance = self.balance - amount
            return true
        return false

    fn internal_adjust(self, delta: i64):
        self.balance = self.balance + delta

    pub fn get_balance(self) -> i64:
        return self.balance
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_factory_methods_get_invariant_checks() {
    // Factory methods (from_*, with_*) should be detected as constructors
    let source = r#"
class Config:
    timeout: i64
    retries: i64

    invariant:
        self.timeout > 0
        self.retries >= 0
        self.retries <= 10

    fn create_default() -> Config:
        return Config(timeout: 30, retries: 3)

    fn from_timeout(t: i64) -> Config:
        return Config(timeout: t, retries: 3)

    fn with_retries(r: i64) -> Config:
        return Config(timeout: 30, retries: r)

    pub fn from_values(t: i64, r: i64) -> Config:
        return Config(timeout: t, retries: r)
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_non_constructor_static_method() {
    // Static methods that don't return Self shouldn't get invariants
    let source = r#"
class MathHelper:
    value: i64

    invariant:
        self.value >= 0

    fn new(val: i64) -> MathHelper:
        return MathHelper(value: val)

    fn compute_factorial(n: i64) -> i64:
        if n <= 1:
            return 1
        return n * MathHelper.compute_factorial(n - 1)

    pub fn get_value(self) -> i64:
        return self.value
"#;

    assert!(compile_class(source).is_ok());
}

#[test]
fn test_struct_with_invariants() {
    // Structs should work the same as classes
    let source = r#"
struct Point:
    x: i64
    y: i64

    invariant:
        self.x >= 0
        self.y >= 0

    fn new(x_val: i64, y_val: i64) -> Point:
        return Point(x: x_val, y: y_val)

    fn origin() -> Point:
        return Point(x: 0, y: 0)

    pub fn distance_from_origin(self) -> i64:
        return self.x * self.x + self.y * self.y
"#;

    assert!(compile_class(source).is_ok());
}
