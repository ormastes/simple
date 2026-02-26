//! Integration tests for the bytecode VM.

use super::opcodes::*;
use super::vm::{BytecodeVM, FunctionMetadata, VmError};
use crate::value::RuntimeValue;

/// Helper to create a simple function that adds two numbers.
fn create_add_function() -> (Vec<u8>, FunctionMetadata) {
    let mut encoder = InstructionEncoder::new();
    let code_offset = 0;

    // Function: fn add(a, b) -> i64 { a + b }
    //
    // Locals: [a=0, b=1, result=2]
    // Stack slots: [s0, s1, s2, ...]
    //
    // Bytecode:
    // LOAD s0, a       ; Load local a into stack slot 0
    // LOAD s1, b       ; Load local b into stack slot 1
    // PUSH s0          ; Push a to eval stack
    // PUSH s1          ; Push b to eval stack
    // ADD_I64          ; Pop b, pop a, push (a+b)
    // POP s2           ; Pop result into stack slot 2
    // RET s2           ; Return result

    encoder.emit_opcode(LOAD);
    encoder.emit_u16(0); // dest = s0
    encoder.emit_u16(0); // local = a (param 0)

    encoder.emit_opcode(LOAD);
    encoder.emit_u16(1); // dest = s1
    encoder.emit_u16(1); // local = b (param 1)

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0); // push s0

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1); // push s1

    encoder.emit_opcode(ADD_I64);

    encoder.emit_opcode(POP);
    encoder.emit_u16(2); // pop to s2

    encoder.emit_opcode(RET);
    encoder.emit_u16(2); // return s2

    let code = encoder.finish();
    let code_length = code.len();

    let metadata = FunctionMetadata {
        name: "add".to_string(),
        code_offset,
        code_length,
        param_count: 2,
        local_count: 3, // a, b, result
    };

    (code, metadata)
}

#[test]
fn test_vm_add_function() {
    let (code, metadata) = create_add_function();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    vm.set_functions(vec![metadata]);

    let args = [RuntimeValue::from_int(10), RuntimeValue::from_int(32)];
    let result = vm.call_function(0, &args).expect("Execution failed");

    assert_eq!(result.as_int(), 42);
}

/// Helper to create a factorial function (recursive).
fn create_factorial_function() -> (Vec<u8>, FunctionMetadata) {
    let mut encoder = InstructionEncoder::new();
    let code_offset = 0;

    // Function: fn factorial(n) -> i64 {
    //     if n <= 1: 1
    //     else: n * factorial(n - 1)
    // }
    //
    // Locals: [n=0, result=1]
    //
    // Bytecode:
    // LOAD s0, n           ; Load n
    // CONST_I64 s1, 1      ; Load constant 1
    // PUSH s0              ; Push n
    // PUSH s1              ; Push 1
    // LE                   ; n <= 1
    // POP s2               ; Pop condition to s2
    // JMP_IF_NOT <else>    ; If !(n <= 1), jump to else
    // ; then branch:
    // CONST_I64 s1, 1      ; result = 1
    // RET s1               ; Return 1
    // ; else branch:
    // <else>:
    // LOAD s0, n           ; Load n
    // CONST_I64 s3, 1      ; Load 1
    // PUSH s0              ; Push n
    // PUSH s3              ; Push 1
    // SUB_I64              ; n - 1
    // POP s4               ; result of (n-1) in s4
    // ; TODO: CALL factorial(s4) - For now, just return n
    // PUSH s0              ; Push n (simplified - should be n * factorial(n-1))
    // POP s1               ; Pop to result
    // RET s1               ; Return result

    // This is a simplified version without recursion support for now
    // We'll add CALL instruction support in Phase 2

    encoder.emit_opcode(LOAD);
    encoder.emit_u16(0); // dest = s0
    encoder.emit_u16(0); // local = n

    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1); // dest = s1
    encoder.emit_i64(1);

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0); // push s0 (n)

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1); // push s1 (1)

    encoder.emit_opcode(LE);

    encoder.emit_opcode(POP);
    encoder.emit_u16(2); // pop condition to s2

    // Calculate else offset
    let jmp_pos = encoder.position();
    encoder.emit_opcode(JMP_IF_NOT);
    let offset_pos = encoder.position();
    encoder.emit_i32(0); // Placeholder

    // Then branch
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1); // dest = s1
    encoder.emit_i64(1);

    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    // Else branch
    let else_pos = encoder.position();
    let offset = (else_pos - (offset_pos + 4)) as i32;
    encoder.patch_i32(offset_pos, offset);

    encoder.emit_opcode(LOAD);
    encoder.emit_u16(0); // dest = s0
    encoder.emit_u16(0); // local = n

    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();
    let code_length = code.len();

    let metadata = FunctionMetadata {
        name: "factorial_simple".to_string(),
        code_offset,
        code_length,
        param_count: 1,
        local_count: 2,
    };

    (code, metadata)
}

#[test]
fn test_vm_factorial_base_case() {
    let (code, metadata) = create_factorial_function();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    vm.set_functions(vec![metadata.clone()]);

    // Test base case: factorial(1) = 1
    let args = [RuntimeValue::from_int(1)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), 1);

    // Test base case: factorial(0) = 1
    let args = [RuntimeValue::from_int(0)];
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    vm.set_functions(vec![metadata]);
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), 1);
}

#[test]
fn test_vm_const_i64() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(42);
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_vm_const_f64() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_F64);
    encoder.emit_u16(0);
    encoder.emit_f64(3.14159);
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert!((result.as_float() - 3.14159).abs() < 1e-10);
}

#[test]
fn test_vm_arithmetic_operations() {
    // Test: (10 + 5) * 2 - 3 = 27
    let mut encoder = InstructionEncoder::new();

    // CONST_I64 s0, 10
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(10);

    // CONST_I64 s1, 5
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(5);

    // PUSH s0, PUSH s1, ADD_I64, POP s2
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1);
    encoder.emit_opcode(ADD_I64);
    encoder.emit_opcode(POP);
    encoder.emit_u16(2); // s2 = 15

    // CONST_I64 s3, 2
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(3);
    encoder.emit_i64(2);

    // PUSH s2, PUSH s3, MUL_I64, POP s4
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(2);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(3);
    encoder.emit_opcode(MUL_I64);
    encoder.emit_opcode(POP);
    encoder.emit_u16(4); // s4 = 30

    // CONST_I64 s5, 3
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(5);
    encoder.emit_i64(3);

    // PUSH s4, PUSH s5, SUB_I64, POP s6
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(4);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(5);
    encoder.emit_opcode(SUB_I64);
    encoder.emit_opcode(POP);
    encoder.emit_u16(6); // s6 = 27

    // RET s6
    encoder.emit_opcode(RET);
    encoder.emit_u16(6);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 27);
}

#[test]
fn test_vm_comparison() {
    // Test: 5 < 10
    let mut encoder = InstructionEncoder::new();

    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(5);

    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(10);

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1);
    encoder.emit_opcode(LT);
    encoder.emit_opcode(POP);
    encoder.emit_u16(2);

    encoder.emit_opcode(RET);
    encoder.emit_u16(2);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_bool(), true);
}

#[test]
fn test_vm_division_by_zero() {
    let mut encoder = InstructionEncoder::new();

    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(42);

    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(0);

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1);
    encoder.emit_opcode(DIV_I64);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute();
    assert!(matches!(result, Err(VmError::DivisionByZero)));
}

#[test]
fn test_vm_jump() {
    // Test unconditional jump
    let mut encoder = InstructionEncoder::new();

    // CONST_I64 s0, 10
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(10);

    // JMP <skip>
    encoder.emit_opcode(JMP);
    let jmp_offset_pos = encoder.position();
    encoder.emit_i32(0); // Placeholder

    // This should be skipped
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(999); // Should not execute

    // <skip>:
    let skip_pos = encoder.position();
    let offset = (skip_pos - (jmp_offset_pos + 4)) as i32;
    encoder.patch_i32(jmp_offset_pos, offset);

    // RET s0
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 10); // Should be 10, not 999
}

#[test]
fn test_vm_conditional_jump() {
    // Test: if true { 42 } else { 999 }
    let mut encoder = InstructionEncoder::new();

    encoder.emit_opcode(CONST_TRUE);
    encoder.emit_u16(0);

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);

    encoder.emit_opcode(JMP_IF_NOT);
    let else_offset_pos = encoder.position();
    encoder.emit_i32(0); // Placeholder

    // Then branch
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(42);
    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    // Else branch
    let else_pos = encoder.position();
    let offset = (else_pos - (else_offset_pos + 4)) as i32;
    encoder.patch_i32(else_offset_pos, offset);

    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(999);
    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_vm_logical_operations() {
    // Test: true && false
    let mut encoder = InstructionEncoder::new();

    encoder.emit_opcode(CONST_TRUE);
    encoder.emit_u16(0);
    encoder.emit_opcode(CONST_FALSE);
    encoder.emit_u16(1);

    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1);
    encoder.emit_opcode(AND);
    encoder.emit_opcode(POP);
    encoder.emit_u16(2);

    encoder.emit_opcode(RET);
    encoder.emit_u16(2);

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_bool(), false);
}

#[test]
fn test_vm_stack_overflow() {
    let mut encoder = InstructionEncoder::new();

    // Try to push more than MAX_STACK_DEPTH values
    for _ in 0..10_001 {
        encoder.emit_opcode(CONST_I64);
        encoder.emit_u16(0);
        encoder.emit_i64(1);
        encoder.emit_opcode(PUSH);
        encoder.emit_u16(0);
    }

    let code = encoder.finish();

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);

    let result = vm.execute();
    assert!(matches!(result, Err(VmError::StackOverflow)));
}

#[test]
fn test_vm_bytecode_call() {
    // Test CALL instruction: define two functions, call one from another
    // func 0: fn double(x) { x + x }
    // func 1: fn main() { double(21) }

    let mut double_enc = InstructionEncoder::new();
    // Load param x (local 0) to slot 0
    double_enc.emit_opcode(LOAD);
    double_enc.emit_u16(0);
    double_enc.emit_u16(0);
    // Push x twice, add
    double_enc.emit_opcode(PUSH);
    double_enc.emit_u16(0);
    double_enc.emit_opcode(PUSH);
    double_enc.emit_u16(0);
    double_enc.emit_opcode(ADD_I64);
    double_enc.emit_opcode(POP);
    double_enc.emit_u16(1);
    double_enc.emit_opcode(RET);
    double_enc.emit_u16(1);
    let double_code = double_enc.finish();
    let double_len = double_code.len();

    let mut main_enc = InstructionEncoder::new();
    // CONST_I64 s0, 21
    main_enc.emit_opcode(CONST_I64);
    main_enc.emit_u16(0);
    main_enc.emit_i64(21);
    // PUSH s0
    main_enc.emit_opcode(PUSH);
    main_enc.emit_u16(0);
    // CALL func_idx=0, argc=1
    main_enc.emit_opcode(CALL);
    main_enc.emit_u32(0); // function index
    main_enc.emit_u16(1); // 1 argument
                          // Pop result to s1
    main_enc.emit_opcode(POP);
    main_enc.emit_u16(1);
    // RET s1
    main_enc.emit_opcode(RET);
    main_enc.emit_u16(1);
    let main_code = main_enc.finish();
    let main_len = main_code.len();

    // Concatenate: [double_code][main_code]
    let mut all_code = double_code;
    let main_offset = all_code.len();
    all_code.extend_from_slice(&main_code);

    let double_meta = FunctionMetadata {
        name: "double".to_string(),
        code_offset: 0,
        code_length: double_len,
        param_count: 1,
        local_count: 2,
    };

    let main_meta = FunctionMetadata {
        name: "main".to_string(),
        code_offset: main_offset,
        code_length: main_len,
        param_count: 0,
        local_count: 2,
    };

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&all_code);
    vm.set_functions(vec![double_meta, main_meta]);

    let result = vm.call_function(1, &[]).expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_vm_ffi_call() {
    // Test CALL_FFI: call an FFI function that adds 100
    fn add_100(args: &[RuntimeValue]) -> super::vm::VmResult<RuntimeValue> {
        let x = args[0].as_int();
        Ok(RuntimeValue::from_int(x + 100))
    }

    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(42);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(CALL_FFI);
    encoder.emit_u16(0); // ffi index 0
    encoder.emit_u16(1); // 1 arg
    encoder.emit_opcode(POP);
    encoder.emit_u16(1);
    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    vm.set_ffi_table(vec![add_100]);

    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 142);
}

#[test]
fn test_vm_is_some() {
    // Test IS_SOME: check if a value is non-nil
    let mut encoder = InstructionEncoder::new();

    // Test with non-nil value
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(42);
    encoder.emit_opcode(IS_SOME);
    encoder.emit_u16(1); // dest
    encoder.emit_u16(0); // source
    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_bool(), true);
}

#[test]
fn test_vm_is_some_nil() {
    // Test IS_SOME with nil value
    let mut encoder = InstructionEncoder::new();

    encoder.emit_opcode(CONST_NONE);
    encoder.emit_u16(0);
    encoder.emit_opcode(IS_SOME);
    encoder.emit_u16(1);
    encoder.emit_u16(0);
    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_bool(), false);
}

// =============================================================================
// Super-Instruction Tests
// =============================================================================

#[test]
fn test_vm_const_i64_push() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(42);
    encoder.emit_opcode(POP);
    encoder.emit_u16(0);
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_vm_add_i64_pop() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(10);
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(32);
    encoder.emit_opcode(ADD_I64_POP);
    encoder.emit_u16(0);
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_vm_lt_jmp_if_not() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(5);
    // Push 5 and 10, test 5 < 10 (true, so don't jump)
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(5);
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(10);
    encoder.emit_opcode(LT_JMP_IF_NOT);
    let jmp_pos = encoder.position();
    encoder.emit_i32(0);
    // 5 < 10 is true, so we reach here and set s0 = 100
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(100);
    let skip_pos = encoder.position();
    encoder.patch_i32(jmp_pos, (skip_pos - (jmp_pos + 4)) as i32);
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 100);
}

// =============================================================================
// Stress Tests
// =============================================================================

#[test]
fn test_vm_stress_many_operations() {
    // Sum 1..1000 using a loop-like sequence of bytecodes
    let mut encoder = InstructionEncoder::new();
    // s0 = accumulator = 0
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(0);

    // Unroll: add 1, add 2, ..., add 100
    for i in 1..=100i64 {
        encoder.emit_opcode(PUSH);
        encoder.emit_u16(0);
        encoder.emit_opcode(CONST_I64_PUSH);
        encoder.emit_i64(i);
        encoder.emit_opcode(ADD_I64_POP);
        encoder.emit_u16(0);
    }

    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 5050); // sum 1..100
}

#[test]
fn test_vm_stress_deep_calls() {
    // Create a function that calls itself N times (countdown)
    // func0: if arg0 <= 0, return 0; else call func0(arg0 - 1) and add 1
    let mut encoder = InstructionEncoder::new();
    let func_start = 0usize;

    // LOAD s0, local0 (load param)
    encoder.emit_opcode(LOAD);
    encoder.emit_u16(0);
    encoder.emit_u16(0);

    // PUSH s0; CONST_I64_PUSH 0; LE
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(0);
    encoder.emit_opcode(LE);

    // JMP_IF_NOT <recurse>
    encoder.emit_opcode(JMP_IF_NOT);
    let jmp_pos = encoder.position();
    encoder.emit_i32(0);

    // Base case: return 0
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(0);
    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    // <recurse>:
    let recurse_pos = encoder.position();
    encoder.patch_i32(jmp_pos, (recurse_pos - (jmp_pos + 4)) as i32);

    // Compute arg0 - 1
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(1);
    encoder.emit_opcode(SUB_I64);

    // CALL func0, argc=1
    encoder.emit_opcode(CALL);
    encoder.emit_u32(0);
    encoder.emit_u16(1);

    // Result is on eval stack; pop to s1
    encoder.emit_opcode(POP);
    encoder.emit_u16(1);

    // s1 = s1 + 1
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1);
    encoder.emit_opcode(CONST_I64_PUSH);
    encoder.emit_i64(1);
    encoder.emit_opcode(ADD_I64_POP);
    encoder.emit_u16(1);

    encoder.emit_opcode(RET);
    encoder.emit_u16(1);

    let code = encoder.finish();
    let func = FunctionMetadata {
        name: "countdown".to_string(),
        code_offset: func_start,
        code_length: code.len(),
        param_count: 1,
        local_count: 2,
    };

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    vm.set_functions(vec![func]);

    // Call with 500 (deep recursion but within MAX_CALL_DEPTH=1000)
    let result = vm
        .call_function(0, &[RuntimeValue::from_int(500)])
        .expect("Execution failed");
    assert_eq!(result.as_int(), 500);
}

#[test]
fn test_vm_stress_call_stack_overflow() {
    // Same recursive function but with depth > MAX_CALL_DEPTH
    let mut encoder = InstructionEncoder::new();

    // Always recurse (no base case - will overflow)
    encoder.emit_opcode(LOAD);
    encoder.emit_u16(0);
    encoder.emit_u16(0);
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);
    encoder.emit_opcode(CALL);
    encoder.emit_u32(0);
    encoder.emit_u16(1);
    encoder.emit_opcode(POP);
    encoder.emit_u16(0);
    encoder.emit_opcode(RET);
    encoder.emit_u16(0);

    let code = encoder.finish();
    let func = FunctionMetadata {
        name: "infinite".to_string(),
        code_offset: 0,
        code_length: code.len(),
        param_count: 1,
        local_count: 1,
    };

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    vm.set_functions(vec![func]);

    let result = vm.call_function(0, &[RuntimeValue::from_int(0)]);
    assert!(matches!(result, Err(VmError::CallStackOverflow)));
}

#[test]
fn test_vm_stress_large_stack() {
    // Push many values onto the stack
    let mut encoder = InstructionEncoder::new();
    let count = 500;
    for i in 0..count {
        encoder.emit_opcode(CONST_I64);
        encoder.emit_u16(i);
        encoder.emit_i64(i as i64);
    }
    encoder.emit_opcode(RET);
    encoder.emit_u16((count - 1) as u16);

    let code = encoder.finish();
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), (count - 1) as i64);
}
