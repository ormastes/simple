//! Unit tests for bytecode instructions.

use super::opcodes::*;

#[test]
fn test_opcode_encoding_decoding() {
    // Test that all opcodes can be encoded and decoded
    let opcodes = [
        CONST_I64,
        CONST_F64,
        CONST_TRUE,
        CONST_FALSE,
        ADD_I64,
        SUB_I64,
        JMP,
        CALL,
        RET,
    ];

    for &opcode in &opcodes {
        let mut encoder = InstructionEncoder::new();
        encoder.emit_opcode(opcode);
        let bytes = encoder.finish();

        let mut decoder = InstructionDecoder::new(&bytes);
        let decoded = decoder.read_opcode().expect("Failed to decode opcode");
        assert_eq!(decoded, opcode, "Opcode mismatch for {}", opcode_name(opcode));
    }
}

#[test]
fn test_const_i64_encoding() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0); // dest register
    encoder.emit_i64(42); // value

    let bytes = encoder.finish();
    assert_eq!(bytes.len(), 12); // 2 (opcode) + 2 (dest) + 8 (value)

    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), CONST_I64);
    assert_eq!(decoder.read_u16().unwrap(), 0);
    assert_eq!(decoder.read_i64().unwrap(), 42);
}

#[test]
fn test_const_f64_encoding() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CONST_F64);
    encoder.emit_u16(1); // dest register
    encoder.emit_f64(3.14159); // value

    let bytes = encoder.finish();
    assert_eq!(bytes.len(), 12);

    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), CONST_F64);
    assert_eq!(decoder.read_u16().unwrap(), 1);
    assert!((decoder.read_f64().unwrap() - 3.14159).abs() < 1e-10);
}

#[test]
fn test_add_i64_encoding() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(ADD_I64);

    let bytes = encoder.finish();
    assert_eq!(bytes.len(), 2); // No operands for stack-based arithmetic

    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), ADD_I64);
}

#[test]
fn test_jmp_encoding() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(JMP);
    encoder.emit_i32(100); // Jump forward 100 bytes

    let bytes = encoder.finish();
    assert_eq!(bytes.len(), 6);

    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), JMP);
    assert_eq!(decoder.read_i32().unwrap(), 100);
}

#[test]
fn test_call_encoding() {
    let mut encoder = InstructionEncoder::new();
    encoder.emit_opcode(CALL);
    encoder.emit_u32(5); // function index
    encoder.emit_u16(3); // argument count

    let bytes = encoder.finish();
    assert_eq!(bytes.len(), 8);

    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), CALL);
    assert_eq!(decoder.read_u32().unwrap(), 5);
    assert_eq!(decoder.read_u16().unwrap(), 3);
}

#[test]
fn test_patch_jump_offset() {
    let mut encoder = InstructionEncoder::new();

    // Emit a JMP with placeholder offset
    encoder.emit_opcode(JMP);
    let offset_pos = encoder.position();
    encoder.emit_i32(0); // Placeholder

    // Emit some more instructions
    encoder.emit_opcode(ADD_I64);
    encoder.emit_opcode(RET_VOID);

    // Calculate actual offset and patch it
    let target_pos = encoder.position();
    let actual_offset = (target_pos - (offset_pos + 4)) as i32;
    encoder.patch_i32(offset_pos, actual_offset);

    let bytes = encoder.finish();

    // Verify the patched offset
    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), JMP);
    assert_eq!(decoder.read_i32().unwrap(), actual_offset);
}

#[test]
fn test_opcode_names() {
    assert_eq!(opcode_name(CONST_I64), "CONST_I64");
    assert_eq!(opcode_name(ADD_I64), "ADD_I64");
    assert_eq!(opcode_name(JMP), "JMP");
    assert_eq!(opcode_name(CALL), "CALL");
    assert_eq!(opcode_name(RET), "RET");
    assert_eq!(opcode_name(0xFFFF), "UNKNOWN");
}

#[test]
fn test_decoder_bounds_checking() {
    let bytes = vec![0x01, 0x00]; // Only 2 bytes (one opcode)

    let mut decoder = InstructionDecoder::new(&bytes);
    assert_eq!(decoder.read_opcode().unwrap(), 0x0001);
    assert!(decoder.read_opcode().is_none()); // Should fail
    assert!(decoder.read_u16().is_none()); // Should fail
    assert!(decoder.read_i32().is_none()); // Should fail
}

#[test]
fn test_multi_instruction_sequence() {
    let mut encoder = InstructionEncoder::new();

    // CONST_I64 0, 10
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(0);
    encoder.emit_i64(10);

    // CONST_I64 1, 32
    encoder.emit_opcode(CONST_I64);
    encoder.emit_u16(1);
    encoder.emit_i64(32);

    // PUSH 0
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(0);

    // PUSH 1
    encoder.emit_opcode(PUSH);
    encoder.emit_u16(1);

    // ADD_I64
    encoder.emit_opcode(ADD_I64);

    // POP 2
    encoder.emit_opcode(POP);
    encoder.emit_u16(2);

    // RET 2
    encoder.emit_opcode(RET);
    encoder.emit_u16(2);

    let bytes = encoder.finish();

    // Decode and verify
    let mut decoder = InstructionDecoder::new(&bytes);

    assert_eq!(decoder.read_opcode().unwrap(), CONST_I64);
    assert_eq!(decoder.read_u16().unwrap(), 0);
    assert_eq!(decoder.read_i64().unwrap(), 10);

    assert_eq!(decoder.read_opcode().unwrap(), CONST_I64);
    assert_eq!(decoder.read_u16().unwrap(), 1);
    assert_eq!(decoder.read_i64().unwrap(), 32);

    assert_eq!(decoder.read_opcode().unwrap(), PUSH);
    assert_eq!(decoder.read_u16().unwrap(), 0);

    assert_eq!(decoder.read_opcode().unwrap(), PUSH);
    assert_eq!(decoder.read_u16().unwrap(), 1);

    assert_eq!(decoder.read_opcode().unwrap(), ADD_I64);

    assert_eq!(decoder.read_opcode().unwrap(), POP);
    assert_eq!(decoder.read_u16().unwrap(), 2);

    assert_eq!(decoder.read_opcode().unwrap(), RET);
    assert_eq!(decoder.read_u16().unwrap(), 2);

    assert!(!decoder.has_more());
}
