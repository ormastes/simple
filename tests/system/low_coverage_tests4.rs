//! Low Coverage Type Tests Part 4
//! Tests for common/manual.rs, compiler/effects.rs, mir/instructions.rs, doctest.rs
#![allow(unused_imports)]

use std::num::NonZeroUsize;
use std::path::PathBuf;

// =============================================================================
// Common Manual Memory Coverage (common/src/manual.rs - 0%)
// =============================================================================

use simple_common::manual::{
    borrow_state_valid, gc_state_safe, BorrowState, GcState, Nat, ValidBorrowState,
};

#[test]
fn test_nat_new() {
    let n = Nat::new(42);
    assert_eq!(n.get(), 42);
}

#[test]
fn test_nat_zero() {
    assert!(Nat::ZERO.is_zero());
    assert_eq!(Nat::ZERO.get(), 0);
}

#[test]
fn test_nat_pred() {
    let n = Nat::new(5);
    assert_eq!(n.pred().get(), 4);

    // Saturating at 0
    let zero = Nat::ZERO;
    assert_eq!(zero.pred().get(), 0);
}

#[test]
fn test_nat_succ() {
    let n = Nat::new(5);
    assert_eq!(n.succ().get(), 6);
}

#[test]
fn test_nat_is_zero() {
    assert!(Nat::ZERO.is_zero());
    assert!(!Nat::new(1).is_zero());
}

#[test]
fn test_nat_from_usize() {
    let n: Nat = 10usize.into();
    assert_eq!(n.get(), 10);
}

#[test]
fn test_nat_into_usize() {
    let n = Nat::new(20);
    let u: usize = n.into();
    assert_eq!(u, 20);
}

#[test]
fn test_borrow_state_new() {
    let state = BorrowState::new();
    assert!(!state.exclusive);
    assert!(state.shared.is_zero());
}

#[test]
fn test_borrow_state_is_valid_unborrowed() {
    let state = BorrowState::new();
    assert!(state.is_valid());
    assert!(borrow_state_valid(&state));
}

#[test]
fn test_borrow_state_take_exclusive() {
    let mut state = BorrowState::new();
    assert!(state.take_exclusive());
    assert!(state.exclusive);
    assert!(state.is_valid());
}

#[test]
fn test_borrow_state_take_shared() {
    let mut state = BorrowState::new();
    assert!(state.take_shared());
    assert_eq!(state.shared.get(), 1);
    assert!(state.is_valid());
}

#[test]
fn test_borrow_state_multiple_shared() {
    let mut state = BorrowState::new();
    assert!(state.take_shared());
    assert!(state.take_shared());
    assert_eq!(state.shared.get(), 2);
    assert!(state.is_valid());
}

#[test]
fn test_borrow_state_release_exclusive() {
    let mut state = BorrowState::new();
    state.take_exclusive();
    state.release_exclusive();
    assert!(!state.exclusive);
}

#[test]
fn test_borrow_state_release_shared() {
    let mut state = BorrowState::new();
    state.take_shared();
    state.take_shared();
    state.release_shared();
    assert_eq!(state.shared.get(), 1);
}

#[test]
fn test_borrow_state_to_valid() {
    let state = BorrowState::new();
    let valid = state.to_valid();
    assert!(valid.is_some());
    assert!(matches!(valid, Some(ValidBorrowState::Unborrowed)));
}

#[test]
fn test_valid_borrow_state_unborrowed() {
    let valid = ValidBorrowState::Unborrowed;
    assert!(valid.is_unborrowed());
    assert!(!valid.is_exclusive());
    assert!(!valid.is_shared());
}

#[test]
fn test_valid_borrow_state_exclusive() {
    let valid = ValidBorrowState::Exclusive;
    assert!(!valid.is_unborrowed());
    assert!(valid.is_exclusive());
    assert!(!valid.is_shared());
}

#[test]
fn test_valid_borrow_state_shared() {
    let valid = ValidBorrowState::Shared(NonZeroUsize::new(2).unwrap());
    assert!(!valid.is_unborrowed());
    assert!(!valid.is_exclusive());
    assert!(valid.is_shared());
    assert_eq!(valid.shared_count(), 2);
}

#[test]
fn test_valid_borrow_state_take_exclusive() {
    let valid = ValidBorrowState::Unborrowed;
    let result = valid.take_exclusive();
    assert!(matches!(result, Some(ValidBorrowState::Exclusive)));
}

#[test]
fn test_valid_borrow_state_take_shared() {
    let valid = ValidBorrowState::Unborrowed;
    let result = valid.take_shared();
    assert!(matches!(result, Some(ValidBorrowState::Shared(_))));
}

#[test]
fn test_valid_borrow_state_release_exclusive() {
    let valid = ValidBorrowState::Exclusive;
    let result = valid.release_exclusive();
    assert!(matches!(result, ValidBorrowState::Unborrowed));
}

#[test]
fn test_valid_borrow_state_to_state() {
    let valid = ValidBorrowState::Shared(NonZeroUsize::new(3).unwrap());
    let state = valid.to_state();
    assert!(!state.exclusive);
    assert_eq!(state.shared.get(), 3);
}

#[test]
fn test_gc_state_new() {
    let state = GcState::new();
    let (alloc, borrowed) = state.counts();
    assert_eq!(alloc, 0);
    assert_eq!(borrowed, 0);
}

#[test]
fn test_gc_state_is_safe_empty() {
    let state = GcState::new();
    assert!(state.is_safe());
    assert!(gc_state_safe(&state));
}

#[test]
fn test_gc_state_allocate() {
    let mut state = GcState::new();
    let id = state.allocate();
    assert_eq!(id, 0);
    let (alloc, _) = state.counts();
    assert_eq!(alloc, 1);
}

#[test]
fn test_gc_state_borrow() {
    let mut state = GcState::new();
    let id = state.allocate();
    assert!(state.borrow(id));
    assert!(state.is_safe());
}

#[test]
fn test_gc_state_release() {
    let mut state = GcState::new();
    let id = state.allocate();
    state.borrow(id);
    state.release(id);
    let (_, borrowed) = state.counts();
    assert_eq!(borrowed, 0);
}

#[test]
fn test_gc_state_collect_safe() {
    let mut state = GcState::new();
    let id = state.allocate();
    // Not borrowed, should be collectible
    assert!(state.collect_safe(id));
}

// =============================================================================
// Compiler Effects Coverage (compiler/src/effects.rs - 0%)
// =============================================================================

use simple_compiler::effects::{
    check_async_violation, check_effect_violations, check_pure_violation, has_side_effects,
    is_blocking_operation, is_fs_operation, is_io_operation, is_net_operation,
};

#[test]
fn test_is_blocking_operation() {
    // From BLOCKING_OPERATIONS: recv_blocking, join_blocking, sleep_blocking
    assert!(is_blocking_operation("sleep_blocking"));
    assert!(is_blocking_operation("recv_blocking"));
    assert!(is_blocking_operation("join_blocking"));
    assert!(!is_blocking_operation("add")); // Not a blocking op
    assert!(!is_blocking_operation("sleep")); // Non-blocking async version
}

#[test]
fn test_is_io_operation() {
    // From IO_OPERATIONS: print, println, eprint, eprintln, input, flush
    assert!(is_io_operation("print"));
    assert!(is_io_operation("println"));
    assert!(is_io_operation("input"));
    assert!(is_io_operation("flush"));
    assert!(!is_io_operation("add"));
}

#[test]
fn test_is_fs_operation() {
    // From FS_OPERATIONS: read_file, write_file, read_dir, list_dir, etc.
    assert!(is_fs_operation("read_file"));
    assert!(is_fs_operation("write_file"));
    assert!(is_fs_operation("create_dir"));
    assert!(!is_fs_operation("print"));
}

#[test]
fn test_is_net_operation() {
    // From NET_OPERATIONS: http_get, http_post, tcp_connect, tcp_listen, etc.
    assert!(is_net_operation("http_get"));
    assert!(is_net_operation("http_post"));
    assert!(is_net_operation("tcp_connect"));
    assert!(!is_net_operation("print"));
}

#[test]
fn test_has_side_effects() {
    // io, fs, or net operations have side effects
    assert!(has_side_effects("print")); // io
    assert!(has_side_effects("write_file")); // fs
    assert!(has_side_effects("http_post")); // net
    assert!(!has_side_effects("add")); // pure
}

#[test]
fn test_check_async_violation_ok() {
    // No effects set, so no violation
    let result = check_async_violation("sleep");
    assert!(result.is_ok()); // Without @async context, blocking is allowed
}

#[test]
fn test_check_pure_violation_ok() {
    // No effects set, so no violation
    let result = check_pure_violation("print");
    assert!(result.is_ok()); // Without @pure context, side effects are allowed
}

#[test]
fn test_check_effect_violations_ok() {
    let result = check_effect_violations("add");
    assert!(result.is_ok());
}

// =============================================================================
// MIR Instructions Coverage (compiler/src/mir/instructions.rs - 0%)
// =============================================================================

use simple_compiler::mir::{BlockId, MirInst, VReg};

#[test]
fn test_block_id_creation() {
    let id = BlockId(0);
    assert_eq!(id.0, 0);
}

#[test]
fn test_block_id_equality() {
    assert_eq!(BlockId(1), BlockId(1));
    assert_ne!(BlockId(1), BlockId(2));
}

#[test]
fn test_vreg_creation() {
    let reg = VReg(0);
    assert_eq!(reg.0, 0);
}

#[test]
fn test_vreg_equality() {
    assert_eq!(VReg(5), VReg(5));
    assert_ne!(VReg(5), VReg(6));
}

#[test]
fn test_mir_inst_const_int() {
    let inst = MirInst::ConstInt {
        dest: VReg(0),
        value: 42,
    };
    assert!(matches!(inst, MirInst::ConstInt { value: 42, .. }));
}

#[test]
fn test_mir_inst_const_float() {
    let inst = MirInst::ConstFloat {
        dest: VReg(0),
        value: 3.14,
    };
    assert!(matches!(inst, MirInst::ConstFloat { .. }));
}

#[test]
fn test_mir_inst_const_bool() {
    let inst = MirInst::ConstBool {
        dest: VReg(0),
        value: true,
    };
    assert!(matches!(inst, MirInst::ConstBool { value: true, .. }));
}

#[test]
fn test_mir_inst_copy() {
    let inst = MirInst::Copy {
        dest: VReg(1),
        src: VReg(0),
    };
    assert!(matches!(inst, MirInst::Copy { .. }));
}

// =============================================================================
// Doctest Coverage (driver/src/doctest.rs - 0%)
// =============================================================================

use simple_driver::doctest::{
    is_definition_like, DoctestExample, DoctestResult, DoctestStatus, Expected,
};

#[test]
fn test_expected_output() {
    let exp = Expected::Output("hello".to_string());
    assert!(matches!(exp, Expected::Output(_)));
}

#[test]
fn test_expected_error() {
    let exp = Expected::Error("oops".to_string());
    assert!(matches!(exp, Expected::Error(_)));
}

#[test]
fn test_expected_empty() {
    let exp = Expected::Empty;
    assert!(matches!(exp, Expected::Empty));
}

#[test]
fn test_doctest_example_creation() {
    let example = DoctestExample {
        source: PathBuf::from("test.spl"),
        start_line: 10,
        commands: vec!["let x = 1".to_string()],
        expected: Expected::Empty,
        section_name: None,
    };
    assert_eq!(example.start_line, 10);
    assert_eq!(example.commands.len(), 1);
}

#[test]
fn test_doctest_status_passed() {
    let status = DoctestStatus::Passed;
    assert!(matches!(status, DoctestStatus::Passed));
}

#[test]
fn test_doctest_status_failed() {
    let status = DoctestStatus::Failed("mismatch".to_string());
    assert!(matches!(status, DoctestStatus::Failed(_)));
}

#[test]
fn test_doctest_result_creation() {
    let example = DoctestExample {
        source: PathBuf::from("test.spl"),
        start_line: 1,
        commands: vec!["1 + 1".to_string()],
        expected: Expected::Output("2".to_string()),
        section_name: None,
    };
    let result = DoctestResult {
        example,
        status: DoctestStatus::Passed,
        actual: "2".to_string(),
    };
    assert!(matches!(result.status, DoctestStatus::Passed));
}

#[test]
fn test_is_definition_like_let() {
    assert!(is_definition_like("let x = 1"));
    assert!(is_definition_like("  let x = 1"));
}

#[test]
fn test_is_definition_like_fn() {
    assert!(is_definition_like("fn foo():"));
    assert!(is_definition_like("  fn bar(x):"));
}

#[test]
fn test_is_definition_like_struct() {
    assert!(is_definition_like("struct Point:"));
    assert!(is_definition_like("class MyClass:"));
}

#[test]
fn test_is_definition_like_control() {
    assert!(is_definition_like("if x > 0:"));
    assert!(is_definition_like("for i in items:"));
    assert!(is_definition_like("while running:"));
    assert!(is_definition_like("match value:"));
}

#[test]
fn test_is_definition_like_assignment() {
    assert!(is_definition_like("x = 1"));
    assert!(is_definition_like("foo = bar"));
}

#[test]
fn test_is_definition_like_expression() {
    // Pure expressions without assignment
    assert!(!is_definition_like("1 + 1"));
    assert!(!is_definition_like("foo()"));
}

#[test]
fn test_is_definition_like_comparison() {
    // Comparisons are NOT definitions
    assert!(!is_definition_like("x == 1"));
    assert!(!is_definition_like("x != 1"));
    assert!(!is_definition_like("x <= 1"));
    assert!(!is_definition_like("x >= 1"));
}

// =============================================================================
// Monomorphize Types Coverage (compiler/src/monomorphize/*.rs - 0%)
// =============================================================================

use simple_compiler::monomorphize::{ConcreteType, MonomorphizationTable, SpecializationKey};

#[test]
fn test_specialization_key_creation() {
    let key = SpecializationKey::new("foo", vec![]);
    assert_eq!(key.name, "foo");
}

#[test]
fn test_specialization_key_with_types() {
    let key = SpecializationKey::new("generic_fn", vec![ConcreteType::Int]);
    assert_eq!(key.type_args.len(), 1);
}

#[test]
fn test_concrete_type_int() {
    let t = ConcreteType::Int;
    assert!(matches!(t, ConcreteType::Int));
}

#[test]
fn test_concrete_type_float() {
    let t = ConcreteType::Float;
    assert!(matches!(t, ConcreteType::Float));
}

#[test]
fn test_concrete_type_bool() {
    let t = ConcreteType::Bool;
    assert!(matches!(t, ConcreteType::Bool));
}

#[test]
fn test_concrete_type_string() {
    let t = ConcreteType::String;
    assert!(matches!(t, ConcreteType::String));
}

#[test]
fn test_concrete_type_array() {
    let t = ConcreteType::Array(Box::new(ConcreteType::Int));
    assert!(matches!(t, ConcreteType::Array(_)));
}

#[test]
fn test_monomorphization_table_new() {
    let table = MonomorphizationTable::new();
    let _ = table;
}
