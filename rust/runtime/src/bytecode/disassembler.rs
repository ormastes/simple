//! Bytecode disassembler for debugging and inspection.
//!
//! Converts raw bytecode into human-readable assembly-like output.

use super::opcodes::*;
use std::fmt::Write;

/// Disassemble bytecode into a human-readable string.
pub fn disassemble(code: &[u8]) -> String {
    let mut output = String::new();
    let mut decoder = InstructionDecoder::new(code);

    while decoder.has_more() {
        let offset = decoder.position();
        let Some(opcode) = decoder.read_opcode() else {
            break;
        };

        write!(output, "{:04X}  {:16}", offset, opcode_name(opcode)).unwrap();

        match opcode {
            // 12-byte: opcode + u16 + i64
            CONST_I64 => {
                let dest = decoder.read_u16().unwrap_or(0);
                let val = decoder.read_i64().unwrap_or(0);
                write!(output, " s{}, {}", dest, val).unwrap();
            }
            // 12-byte: opcode + u16 + f64
            CONST_F64 => {
                let dest = decoder.read_u16().unwrap_or(0);
                let val = decoder.read_f64().unwrap_or(0.0);
                write!(output, " s{}, {}", dest, val).unwrap();
            }
            // 4-byte: opcode + u16
            CONST_TRUE | CONST_FALSE | CONST_NONE | CONST_UNIT => {
                let dest = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}", dest).unwrap();
            }
            // 8-byte: opcode + u16 + u32
            LOAD_CONST | LOAD_STRING => {
                let dest = decoder.read_u16().unwrap_or(0);
                let idx = decoder.read_u32().unwrap_or(0);
                write!(output, " s{}, #{}", dest, idx).unwrap();
            }
            // Stack ops
            PUSH | POP => {
                let reg = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}", reg).unwrap();
            }
            DUP | SWAP => {
                let a = decoder.read_u16().unwrap_or(0);
                let b = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, s{}", a, b).unwrap();
            }
            // No-operand arithmetic/comparison/logical
            ADD_I64 | SUB_I64 | MUL_I64 | DIV_I64 | MOD_I64 | NEG_I64 |
            ADD_F64 | SUB_F64 | MUL_F64 | DIV_F64 |
            EQ | NE | LT | LE | GT | GE |
            AND | OR | NOT => {}
            // Jump: opcode + i32
            JMP => {
                let off = decoder.read_i32().unwrap_or(0);
                let target = decoder.position() as i32 + off;
                write!(output, " {:+} (-> {:04X})", off, target).unwrap();
            }
            JMP_IF | JMP_IF_NOT | LT_JMP_IF_NOT | EQ_JMP_IF_NOT => {
                let off = decoder.read_i32().unwrap_or(0);
                let target = decoder.position() as i32 + off;
                write!(output, " {:+} (-> {:04X})", off, target).unwrap();
            }
            // CALL: u32 + u16
            CALL | TAIL_CALL => {
                let idx = decoder.read_u32().unwrap_or(0);
                let argc = decoder.read_u16().unwrap_or(0);
                write!(output, " func#{}, argc={}", idx, argc).unwrap();
            }
            // RET: u16
            RET => {
                let reg = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}", reg).unwrap();
            }
            RET_VOID => {}
            // CALL_FFI/CALL_RUNTIME: u16 + u16
            CALL_FFI | CALL_RUNTIME => {
                let idx = decoder.read_u16().unwrap_or(0);
                let argc = decoder.read_u16().unwrap_or(0);
                write!(output, " ffi#{}, argc={}", idx, argc).unwrap();
            }
            CALL_INDIRECT => {
                let argc = decoder.read_u16().unwrap_or(0);
                write!(output, " argc={}", argc).unwrap();
            }
            // LOAD/STORE: u16 + u16
            LOAD => {
                let dest = decoder.read_u16().unwrap_or(0);
                let local = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, local{}", dest, local).unwrap();
            }
            STORE => {
                let local = decoder.read_u16().unwrap_or(0);
                let src = decoder.read_u16().unwrap_or(0);
                write!(output, " local{}, s{}", local, src).unwrap();
            }
            // Collections
            ARRAY_LIT => {
                let dest = decoder.read_u16().unwrap_or(0);
                let count = decoder.read_u16().unwrap_or(0);
                let _ty = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, count={}", dest, count).unwrap();
            }
            DICT_LIT | TUPLE_LIT => {
                let dest = decoder.read_u16().unwrap_or(0);
                let count = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, count={}", dest, count).unwrap();
            }
            INDEX_GET => {
                let dest = decoder.read_u16().unwrap_or(0);
                let coll = decoder.read_u16().unwrap_or(0);
                let idx = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, s{}[s{}]", dest, coll, idx).unwrap();
            }
            INDEX_SET => {
                let coll = decoder.read_u16().unwrap_or(0);
                let idx = decoder.read_u16().unwrap_or(0);
                let val = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}[s{}], s{}", coll, idx, val).unwrap();
            }
            LEN | IS_SOME => {
                let dest = decoder.read_u16().unwrap_or(0);
                let src = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, s{}", dest, src).unwrap();
            }
            APPEND => {
                let coll = decoder.read_u16().unwrap_or(0);
                let val = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, s{}", coll, val).unwrap();
            }
            // Pattern matching
            ENUM_MATCH => {
                let dest = decoder.read_u16().unwrap_or(0);
                let val = decoder.read_u16().unwrap_or(0);
                let disc = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, s{}, disc={}", dest, val, disc).unwrap();
            }
            ENUM_PAYLOAD => {
                let dest = decoder.read_u16().unwrap_or(0);
                let val = decoder.read_u16().unwrap_or(0);
                let field = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, s{}.field{}", dest, val, field).unwrap();
            }
            ENUM_NEW => {
                let dest = decoder.read_u16().unwrap_or(0);
                let disc = decoder.read_u16().unwrap_or(0);
                let count = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}, disc={}, fields={}", dest, disc, count).unwrap();
            }
            // Super-instructions
            CONST_I64_PUSH => {
                let val = decoder.read_i64().unwrap_or(0);
                write!(output, " {}", val).unwrap();
            }
            LOAD_PUSH | POP_STORE => {
                let local = decoder.read_u16().unwrap_or(0);
                write!(output, " local{}", local).unwrap();
            }
            ADD_I64_POP | SUB_I64_POP | MUL_I64_POP => {
                let dest = decoder.read_u16().unwrap_or(0);
                write!(output, " s{}", dest).unwrap();
            }
            _ => {
                write!(output, " ???").unwrap();
            }
        }

        output.push('\n');
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_disassemble_simple() {
        let mut encoder = InstructionEncoder::new();
        encoder.emit_opcode(CONST_I64);
        encoder.emit_u16(0);
        encoder.emit_i64(42);
        encoder.emit_opcode(RET);
        encoder.emit_u16(0);

        let output = disassemble(encoder.as_bytes());
        assert!(output.contains("CONST_I64"));
        assert!(output.contains("42"));
        assert!(output.contains("RET"));
    }

    #[test]
    fn test_disassemble_super_instructions() {
        let mut encoder = InstructionEncoder::new();
        encoder.emit_opcode(CONST_I64_PUSH);
        encoder.emit_i64(100);
        encoder.emit_opcode(ADD_I64_POP);
        encoder.emit_u16(0);

        let output = disassemble(encoder.as_bytes());
        assert!(output.contains("CONST_I64_PUSH"));
        assert!(output.contains("100"));
        assert!(output.contains("ADD_I64_POP"));
    }
}
