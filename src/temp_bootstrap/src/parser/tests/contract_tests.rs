/// Contract block parsing tests for LLM-friendly feature #400
///
/// Tests for:
/// - requires: blocks (preconditions)
/// - ensures: blocks (postconditions)
/// - invariant: blocks (class invariants)
/// - old(expr) expressions
/// - result identifiers
use simple_parser::ast::*;
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

fn parse_err(src: &str) {
    let mut parser = Parser::new(src);
    assert!(parser.parse().is_err(), "should fail to parse");
}

/// Helper to validate function contract
fn assert_function_contract(items: &[Node], name: &str, requires_count: usize, ensures_count: usize) {
    assert_eq!(items.len(), 1);
    
    if let Node::Function(func) = &items[0] {
        assert_eq!(func.name, name);
        assert!(func.contract.is_some());
        
        let contract = func.contract.as_ref().unwrap();
        assert_eq!(contract.preconditions.len(), requires_count);
        assert_eq!(contract.postconditions.len(), ensures_count);
    } else {
        panic!("Expected Function node");
    }
}

// === Function Contracts ===

#[test]
fn test_function_with_requires() {
    let source = r#"
fn divide(a: i32, b: i32) -> i32
requires:
    b != 0
:
    a / b
"#;
    let items = parse(source);
    assert_function_contract(&items, "divide", 1, 0);
}

#[test]
fn test_function_with_ensures() {
    let source = r#"
fn abs(x: i32) -> i32
ensures:
    result >= 0
:
    return if x < 0: 0 - x else: x
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Function(func) = &items[0] {
        assert_eq!(func.name, "abs");
        assert!(func.contract.is_some());

        let contract = func.contract.as_ref().unwrap();
        assert_eq!(contract.preconditions.len(), 0);
        assert_eq!(contract.postconditions.len(), 1);
    } else {
        panic!("Expected Function node");
    }
}

#[test]
fn test_function_with_requires_and_ensures() {
    let source = r#"
fn divide(a: i32, b: i32) -> i32
requires:
    b != 0
ensures:
    result * b == a
:
    a / b
"#;
    let items = parse(source);
    assert_function_contract(&items, "divide", 1, 1);
}

#[test]
fn test_function_with_multiple_requires() {
    let source = r#"
fn transfer(sender: Account, recipient: Account, amount: i64) -> bool
requires:
    amount > 0
    sender.balance >= amount
    recipient.balance + amount <= MAX_BALANCE
:
    sender.balance -= amount
    recipient.balance += amount
    true
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Function(func) = &items[0] {
        assert_eq!(func.name, "transfer");
        assert!(func.contract.is_some());

        let contract = func.contract.as_ref().unwrap();
        assert_eq!(contract.preconditions.len(), 3);
    } else {
        panic!("Expected Function node");
    }
}

#[test]
fn test_function_with_old_expr() {
    let source = r#"
fn increment(x: &mut i32)
ensures:
    *x == old(*x) + 1
:
    *x += 1
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Function(func) = &items[0] {
        assert_eq!(func.name, "increment");
        assert!(func.contract.is_some());

        let contract = func.contract.as_ref().unwrap();
        assert_eq!(contract.postconditions.len(), 1);

        // Check that the condition contains an old() expression
        // The AST should contain ContractOld expression
        // (We'll verify this works when we implement the runtime)
    } else {
        panic!("Expected Function node");
    }
}

#[test]
fn test_function_without_contract() {
    let source = r#"
fn add(a: i32, b: i32) -> i32:
    a + b
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Function(func) = &items[0] {
        assert_eq!(func.name, "add");
        assert!(func.contract.is_none());
    } else {
        panic!("Expected Function node");
    }
}

// === Class Invariants ===

#[test]
fn test_class_with_invariant() {
    let source = r#"
class BankAccount:
    balance: i64
    
    invariant:
        balance >= 0
    
    fn deposit(amount: i64)
    requires:
        amount > 0
    :
        self.balance += amount
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Class(class) = &items[0] {
        assert_eq!(class.name, "BankAccount");
        assert!(class.invariant.is_some());

        let invariant = class.invariant.as_ref().unwrap();
        assert_eq!(invariant.conditions.len(), 1);
    } else {
        panic!("Expected Class node");
    }
}

#[test]
fn test_class_with_multiple_invariants() {
    let source = r#"
class Counter:
    count: i32
    max: i32
    
    invariant:
        count >= 0
        count <= max
        max > 0
    
    fn increment():
        self.count += 1
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Class(class) = &items[0] {
        assert_eq!(class.name, "Counter");
        assert!(class.invariant.is_some());

        let invariant = class.invariant.as_ref().unwrap();
        assert_eq!(invariant.conditions.len(), 3);
    } else {
        panic!("Expected Class node");
    }
}

#[test]
fn test_class_without_invariant() {
    let source = r#"
class Point:
    x: f64
    y: f64
    
    fn distance() -> f64:
        sqrt(self.x * self.x + self.y * self.y)
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Class(class) = &items[0] {
        assert_eq!(class.name, "Point");
        assert!(class.invariant.is_none());
    } else {
        panic!("Expected Class node");
    }
}

#[test]
fn test_class_method_with_contract() {
    let source = r#"
class Stack:
    items: [i32]
    
    fn push(item: i32)
    ensures:
        self.items.len() == old(self.items.len()) + 1
    :
        self.items.push(item)
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Class(class) = &items[0] {
        assert_eq!(class.name, "Stack");
        assert_eq!(class.methods.len(), 1);

        let method = &class.methods[0];
        assert_eq!(method.name, "push");
        assert!(method.contract.is_some());

        let contract = method.contract.as_ref().unwrap();
        assert_eq!(contract.postconditions.len(), 1);
    } else {
        panic!("Expected Class node");
    }
}

// === Error Cases ===

#[test]
fn test_multiple_invariants_error() {
    let source = r#"
class Bad:
    x: i32
    
    invariant:
        x >= 0
    
    invariant:
        x <= 100
"#;
    parse_err(source);
}

// === Integration Tests ===

#[test]
fn test_complex_contract_example() {
    let source = r#"
fn withdraw(account: &mut Account, amount: i64) -> bool
requires:
    amount > 0
    account.balance >= amount
    account.active
ensures:
    account.balance <= old(account.balance)
:
    if account.balance >= amount:
        account.balance -= amount
        return true
    return false
"#;
    let items = parse(source);
    assert_eq!(items.len(), 1);

    if let Node::Function(func) = &items[0] {
        assert_eq!(func.name, "withdraw");
        assert!(func.contract.is_some());

        let contract = func.contract.as_ref().unwrap();
        assert_eq!(contract.preconditions.len(), 3);
        assert_eq!(contract.postconditions.len(), 1);
    } else {
        panic!("Expected Function node");
    }
}
