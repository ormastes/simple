//! Bytecode instruction set definitions and encoding.
//!
//! This module defines the 63 MVP bytecode instructions for the Simple language.
//! Instructions are encoded with 16-bit opcodes followed by operands.
//!
//! **Instruction Format:**
//! ```text
//! ┌──────────┬─────────────┬─────────────┬─────┐
//! │ Opcode   │ Operand 1   │ Operand 2   │ ... │
//! │ (2 bytes)│ (variable)  │ (variable)  │     │
//! └──────────┴─────────────┴─────────────┴─────┘
//! ```
//!
//! **Operand Types:**
//! - `u16` - Register/local index (2 bytes)
//! - `i32` - Jump offset (4 bytes)
//! - `i64` - Constant integer value (8 bytes)
//! - `f64` - Constant float value (8 bytes)
//! - `u32` - Function/FFI index (4 bytes)

use std::fmt;

/// Bytecode opcode (16-bit identifier).
///
/// Maximum of 65,536 instructions, but we only use 63 in the MVP.
pub type Opcode = u16;

// ============================================================================
// Constants (8 instructions)
// ============================================================================

/// Push a 64-bit integer constant to the stack.
///
/// **Encoding:** `CONST_I64 dest:u16 value:i64`
/// **Size:** 12 bytes
/// **Effect:** `stack[dest] = value`
pub const CONST_I64: Opcode = 0x0001;

/// Push a 64-bit float constant to the stack.
///
/// **Encoding:** `CONST_F64 dest:u16 value:f64`
/// **Size:** 12 bytes
/// **Effect:** `stack[dest] = value`
pub const CONST_F64: Opcode = 0x0002;

/// Push boolean `true` to the stack.
///
/// **Encoding:** `CONST_TRUE dest:u16`
/// **Size:** 4 bytes
/// **Effect:** `stack[dest] = true`
pub const CONST_TRUE: Opcode = 0x0003;

/// Push boolean `false` to the stack.
///
/// **Encoding:** `CONST_FALSE dest:u16`
/// **Size:** 4 bytes
/// **Effect:** `stack[dest] = false`
pub const CONST_FALSE: Opcode = 0x0004;

/// Push `nil` (None) to the stack.
///
/// **Encoding:** `CONST_NONE dest:u16`
/// **Size:** 4 bytes
/// **Effect:** `stack[dest] = nil`
pub const CONST_NONE: Opcode = 0x0005;

/// Push unit value `()` to the stack.
///
/// **Encoding:** `CONST_UNIT dest:u16`
/// **Size:** 4 bytes
/// **Effect:** `stack[dest] = ()`
pub const CONST_UNIT: Opcode = 0x0006;

/// Load constant from constant pool.
///
/// **Encoding:** `LOAD_CONST dest:u16 const_idx:u32`
/// **Size:** 8 bytes
/// **Effect:** `stack[dest] = constants[const_idx]`
pub const LOAD_CONST: Opcode = 0x0007;

/// Load string constant from constant pool.
///
/// **Encoding:** `LOAD_STRING dest:u16 const_idx:u32`
/// **Size:** 8 bytes
/// **Effect:** `stack[dest] = string_constants[const_idx]`
pub const LOAD_STRING: Opcode = 0x0008;

// ============================================================================
// Stack Operations (4 instructions)
// ============================================================================

/// Push a value from register onto the stack top.
///
/// **Encoding:** `PUSH src:u16`
/// **Size:** 4 bytes
/// **Effect:** `stack.push(stack[src])`
pub const PUSH: Opcode = 0x0010;

/// Pop the top value from the stack.
///
/// **Encoding:** `POP dest:u16`
/// **Size:** 4 bytes
/// **Effect:** `stack[dest] = stack.pop()`
pub const POP: Opcode = 0x0011;

/// Duplicate the value at the top of the stack.
///
/// **Encoding:** `DUP src:u16 dest:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[dest] = stack[src]`
pub const DUP: Opcode = 0x0012;

/// Swap two values on the stack.
///
/// **Encoding:** `SWAP a:u16 b:u16`
/// **Size:** 6 bytes
/// **Effect:** `swap(stack[a], stack[b])`
pub const SWAP: Opcode = 0x0013;

// ============================================================================
// Arithmetic (10 instructions)
// ============================================================================

/// Add two i64 values (stack-based).
///
/// **Encoding:** `ADD_I64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a + b)`
pub const ADD_I64: Opcode = 0x0020;

/// Subtract two i64 values (stack-based).
///
/// **Encoding:** `SUB_I64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a - b)`
pub const SUB_I64: Opcode = 0x0021;

/// Multiply two i64 values (stack-based).
///
/// **Encoding:** `MUL_I64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a * b)`
pub const MUL_I64: Opcode = 0x0022;

/// Divide two i64 values (stack-based).
///
/// **Encoding:** `DIV_I64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a / b)`
pub const DIV_I64: Opcode = 0x0023;

/// Modulo two i64 values (stack-based).
///
/// **Encoding:** `MOD_I64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a % b)`
pub const MOD_I64: Opcode = 0x0024;

/// Add two f64 values (stack-based).
///
/// **Encoding:** `ADD_F64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a + b)`
pub const ADD_F64: Opcode = 0x0025;

/// Subtract two f64 values (stack-based).
///
/// **Encoding:** `SUB_F64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a - b)`
pub const SUB_F64: Opcode = 0x0026;

/// Multiply two f64 values (stack-based).
///
/// **Encoding:** `MUL_F64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a * b)`
pub const MUL_F64: Opcode = 0x0027;

/// Divide two f64 values (stack-based).
///
/// **Encoding:** `DIV_F64`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a / b)`
pub const DIV_F64: Opcode = 0x0028;

/// Negate an i64 value (stack-based).
///
/// **Encoding:** `NEG_I64`
/// **Size:** 2 bytes
/// **Effect:** `a = pop(); push(-a)`
pub const NEG_I64: Opcode = 0x0029;

// ============================================================================
// Comparison (6 instructions)
// ============================================================================

/// Equal comparison (stack-based).
///
/// **Encoding:** `EQ`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a == b)`
pub const EQ: Opcode = 0x0030;

/// Not equal comparison (stack-based).
///
/// **Encoding:** `NE`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a != b)`
pub const NE: Opcode = 0x0031;

/// Less than comparison (stack-based).
///
/// **Encoding:** `LT`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a < b)`
pub const LT: Opcode = 0x0032;

/// Less than or equal comparison (stack-based).
///
/// **Encoding:** `LE`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a <= b)`
pub const LE: Opcode = 0x0033;

/// Greater than comparison (stack-based).
///
/// **Encoding:** `GT`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a > b)`
pub const GT: Opcode = 0x0034;

/// Greater than or equal comparison (stack-based).
///
/// **Encoding:** `GE`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a >= b)`
pub const GE: Opcode = 0x0035;

// ============================================================================
// Control Flow (8 instructions - Phase 1 uses 5)
// ============================================================================

/// Unconditional jump.
///
/// **Encoding:** `JMP offset:i32`
/// **Size:** 6 bytes
/// **Effect:** `ip += offset` (relative jump)
pub const JMP: Opcode = 0x0040;

/// Jump if true (pop condition from stack).
///
/// **Encoding:** `JMP_IF offset:i32`
/// **Size:** 6 bytes
/// **Effect:** `cond = pop(); if cond: ip += offset`
pub const JMP_IF: Opcode = 0x0041;

/// Jump if false (pop condition from stack).
///
/// **Encoding:** `JMP_IF_NOT offset:i32`
/// **Size:** 6 bytes
/// **Effect:** `cond = pop(); if !cond: ip += offset`
pub const JMP_IF_NOT: Opcode = 0x0042;

/// Call a function.
///
/// **Encoding:** `CALL func_idx:u32 argc:u16`
/// **Size:** 8 bytes
/// **Effect:** Push call frame, jump to function, args on stack
pub const CALL: Opcode = 0x0043;

/// Return from function.
///
/// **Encoding:** `RET value:u16`
/// **Size:** 4 bytes
/// **Effect:** Pop call frame, restore IP, push return value
pub const RET: Opcode = 0x0044;

/// Return void (unit value).
///
/// **Encoding:** `RET_VOID`
/// **Size:** 2 bytes
/// **Effect:** Pop call frame, restore IP, push unit value
pub const RET_VOID: Opcode = 0x0045;

/// Call indirect (function pointer on stack).
///
/// **Encoding:** `CALL_INDIRECT argc:u16`
/// **Size:** 4 bytes (Phase 2)
/// **Effect:** `func_ptr = pop(); call(func_ptr, args...)`
pub const CALL_INDIRECT: Opcode = 0x0046;

/// Tail call optimization.
///
/// **Encoding:** `TAIL_CALL func_idx:u32 argc:u16`
/// **Size:** 8 bytes (Phase 2)
/// **Effect:** Reuse current call frame for new call
pub const TAIL_CALL: Opcode = 0x0047;

// ============================================================================
// FFI (3 instructions - Phase 2)
// ============================================================================

/// Call FFI function.
///
/// **Encoding:** `CALL_FFI ffi_idx:u16 argc:u16`
/// **Size:** 6 bytes
/// **Effect:** Call runtime FFI function, args on stack
pub const CALL_FFI: Opcode = 0x0050;

/// Call runtime function (built-in operations).
///
/// **Encoding:** `CALL_RUNTIME rt_idx:u16 argc:u16`
/// **Size:** 6 bytes
/// **Effect:** Call runtime helper, args on stack
pub const CALL_RUNTIME: Opcode = 0x0051;

/// Call interpreted function (fallback to interpreter).
///
/// **Encoding:** `CALL_INTERP func_idx:u32 argc:u16`
/// **Size:** 8 bytes
/// **Effect:** Call function in interpreter mode
pub const CALL_INTERP: Opcode = 0x0052;

// ============================================================================
// Memory (6 instructions - Phase 2)
// ============================================================================

/// Load from local variable.
///
/// **Encoding:** `LOAD dest:u16 local_idx:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[dest] = locals[local_idx]`
pub const LOAD: Opcode = 0x0060;

/// Store to local variable.
///
/// **Encoding:** `STORE local_idx:u16 src:u16`
/// **Size:** 6 bytes
/// **Effect:** `locals[local_idx] = stack[src]`
pub const STORE: Opcode = 0x0061;

/// Get address of local variable.
///
/// **Encoding:** `LOCAL_ADDR dest:u16 local_idx:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[dest] = &locals[local_idx]`
pub const LOCAL_ADDR: Opcode = 0x0062;

/// Allocate GC object.
///
/// **Encoding:** `GC_ALLOC dest:u16 size:u32 type_id:u16`
/// **Size:** 10 bytes
/// **Effect:** `stack[dest] = gc.alloc(size, type_id)`
pub const GC_ALLOC: Opcode = 0x0063;

/// Load from heap (pointer dereference).
///
/// **Encoding:** `LOAD_HEAP dest:u16 ptr:u16 offset:u32`
/// **Size:** 10 bytes
/// **Effect:** `stack[dest] = *(stack[ptr] + offset)`
pub const LOAD_HEAP: Opcode = 0x0064;

/// Store to heap (pointer write).
///
/// **Encoding:** `STORE_HEAP ptr:u16 offset:u32 src:u16`
/// **Size:** 10 bytes
/// **Effect:** `*(stack[ptr] + offset) = stack[src]`
pub const STORE_HEAP: Opcode = 0x0065;

// ============================================================================
// Collections (8 instructions - Phase 2)
// ============================================================================

/// Create array literal.
///
/// **Encoding:** `ARRAY_LIT dest:u16 count:u16 type:u16`
/// **Size:** 8 bytes
/// **Effect:** Pop `count` elements from stack, create array
pub const ARRAY_LIT: Opcode = 0x0070;

/// Create dict literal.
///
/// **Encoding:** `DICT_LIT dest:u16 count:u16`
/// **Size:** 6 bytes
/// **Effect:** Pop `count*2` key-value pairs, create dict
pub const DICT_LIT: Opcode = 0x0071;

/// Create tuple literal.
///
/// **Encoding:** `TUPLE_LIT dest:u16 count:u16`
/// **Size:** 6 bytes
/// **Effect:** Pop `count` elements, create tuple
pub const TUPLE_LIT: Opcode = 0x0072;

/// Index get (array/dict access).
///
/// **Encoding:** `INDEX_GET dest:u16 container:u16 index:u16`
/// **Size:** 8 bytes
/// **Effect:** `stack[dest] = stack[container][stack[index]]`
pub const INDEX_GET: Opcode = 0x0073;

/// Index set (array/dict assignment).
///
/// **Encoding:** `INDEX_SET container:u16 index:u16 value:u16`
/// **Size:** 8 bytes
/// **Effect:** `stack[container][stack[index]] = stack[value]`
pub const INDEX_SET: Opcode = 0x0074;

/// Get array/list length.
///
/// **Encoding:** `LEN dest:u16 container:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[dest] = len(stack[container])`
pub const LEN: Opcode = 0x0075;

/// Append to array/list.
///
/// **Encoding:** `APPEND container:u16 value:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[container].append(stack[value])`
pub const APPEND: Opcode = 0x0076;

/// Slice collection.
///
/// **Encoding:** `SLICE dest:u16 container:u16 start:u16 end:u16`
/// **Size:** 10 bytes
/// **Effect:** `stack[dest] = stack[container][start:end]`
pub const SLICE: Opcode = 0x0077;

// ============================================================================
// Pattern Matching (6 instructions - Phase 2)
// ============================================================================

/// Test if value matches pattern.
///
/// **Encoding:** `PATTERN_TEST dest:u16 value:u16 pattern_idx:u32`
/// **Size:** 10 bytes
/// **Effect:** `stack[dest] = matches(stack[value], patterns[pattern_idx])`
pub const PATTERN_TEST: Opcode = 0x0080;

/// Bind pattern variables.
///
/// **Encoding:** `PATTERN_BIND value:u16 pattern_idx:u32 binding_count:u16`
/// **Size:** 10 bytes
/// **Effect:** Extract values from pattern match into locals
pub const PATTERN_BIND: Opcode = 0x0081;

/// Match enum discriminant.
///
/// **Encoding:** `ENUM_MATCH dest:u16 enum_val:u16 discriminant:u16`
/// **Size:** 8 bytes
/// **Effect:** `stack[dest] = (stack[enum_val].tag == discriminant)`
pub const ENUM_MATCH: Opcode = 0x0082;

/// Extract enum payload.
///
/// **Encoding:** `ENUM_PAYLOAD dest:u16 enum_val:u16 field_idx:u16`
/// **Size:** 8 bytes
/// **Effect:** `stack[dest] = stack[enum_val].payload[field_idx]`
pub const ENUM_PAYLOAD: Opcode = 0x0083;

/// Create enum value.
///
/// **Encoding:** `ENUM_NEW dest:u16 discriminant:u16 field_count:u16`
/// **Size:** 8 bytes
/// **Effect:** Pop fields from stack, create enum
pub const ENUM_NEW: Opcode = 0x0084;

/// Test if Option is Some.
///
/// **Encoding:** `IS_SOME dest:u16 opt:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[dest] = stack[opt].is_some()`
pub const IS_SOME: Opcode = 0x0085;

// ============================================================================
// Async (4 instructions - Phase 2)
// ============================================================================

/// Await a future/promise.
///
/// **Encoding:** `AWAIT dest:u16 future:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[dest] = await stack[future]`
pub const AWAIT: Opcode = 0x0090;

/// Yield from generator.
///
/// **Encoding:** `YIELD value:u16`
/// **Size:** 4 bytes
/// **Effect:** Suspend execution, return value to caller
pub const YIELD: Opcode = 0x0091;

/// Spawn actor.
///
/// **Encoding:** `ACTOR_SPAWN dest:u16 func_idx:u32`
/// **Size:** 8 bytes
/// **Effect:** `stack[dest] = spawn_actor(functions[func_idx])`
pub const ACTOR_SPAWN: Opcode = 0x0092;

/// Send message to actor.
///
/// **Encoding:** `ACTOR_SEND actor:u16 message:u16`
/// **Size:** 6 bytes
/// **Effect:** `stack[actor].send(stack[message])`
pub const ACTOR_SEND: Opcode = 0x0093;

// ============================================================================
// Logical Operations (3 instructions - added for completeness)
// ============================================================================

/// Logical AND.
///
/// **Encoding:** `AND`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a && b)`
pub const AND: Opcode = 0x00A0;

/// Logical OR.
///
/// **Encoding:** `OR`
/// **Size:** 2 bytes
/// **Effect:** `b = pop(); a = pop(); push(a || b)`
pub const OR: Opcode = 0x00A1;

/// Logical NOT.
///
/// **Encoding:** `NOT`
/// **Size:** 2 bytes
/// **Effect:** `a = pop(); push(!a)`
pub const NOT: Opcode = 0x00A2;

// ============================================================================
// Opcode Name Lookup (for debugging/disassembly)
// ============================================================================

/// Get the human-readable name of an opcode.
///
/// Used for debugging, disassembly, and error messages.
pub fn opcode_name(opcode: Opcode) -> &'static str {
    match opcode {
        // Constants
        CONST_I64 => "CONST_I64",
        CONST_F64 => "CONST_F64",
        CONST_TRUE => "CONST_TRUE",
        CONST_FALSE => "CONST_FALSE",
        CONST_NONE => "CONST_NONE",
        CONST_UNIT => "CONST_UNIT",
        LOAD_CONST => "LOAD_CONST",
        LOAD_STRING => "LOAD_STRING",
        // Stack Operations
        PUSH => "PUSH",
        POP => "POP",
        DUP => "DUP",
        SWAP => "SWAP",
        // Arithmetic
        ADD_I64 => "ADD_I64",
        SUB_I64 => "SUB_I64",
        MUL_I64 => "MUL_I64",
        DIV_I64 => "DIV_I64",
        MOD_I64 => "MOD_I64",
        ADD_F64 => "ADD_F64",
        SUB_F64 => "SUB_F64",
        MUL_F64 => "MUL_F64",
        DIV_F64 => "DIV_F64",
        NEG_I64 => "NEG_I64",
        // Comparison
        EQ => "EQ",
        NE => "NE",
        LT => "LT",
        LE => "LE",
        GT => "GT",
        GE => "GE",
        // Control Flow
        JMP => "JMP",
        JMP_IF => "JMP_IF",
        JMP_IF_NOT => "JMP_IF_NOT",
        CALL => "CALL",
        RET => "RET",
        RET_VOID => "RET_VOID",
        CALL_INDIRECT => "CALL_INDIRECT",
        TAIL_CALL => "TAIL_CALL",
        // FFI
        CALL_FFI => "CALL_FFI",
        CALL_RUNTIME => "CALL_RUNTIME",
        CALL_INTERP => "CALL_INTERP",
        // Memory
        LOAD => "LOAD",
        STORE => "STORE",
        LOCAL_ADDR => "LOCAL_ADDR",
        GC_ALLOC => "GC_ALLOC",
        LOAD_HEAP => "LOAD_HEAP",
        STORE_HEAP => "STORE_HEAP",
        // Collections
        ARRAY_LIT => "ARRAY_LIT",
        DICT_LIT => "DICT_LIT",
        TUPLE_LIT => "TUPLE_LIT",
        INDEX_GET => "INDEX_GET",
        INDEX_SET => "INDEX_SET",
        LEN => "LEN",
        APPEND => "APPEND",
        SLICE => "SLICE",
        // Pattern Matching
        PATTERN_TEST => "PATTERN_TEST",
        PATTERN_BIND => "PATTERN_BIND",
        ENUM_MATCH => "ENUM_MATCH",
        ENUM_PAYLOAD => "ENUM_PAYLOAD",
        ENUM_NEW => "ENUM_NEW",
        IS_SOME => "IS_SOME",
        // Async
        AWAIT => "AWAIT",
        YIELD => "YIELD",
        ACTOR_SPAWN => "ACTOR_SPAWN",
        ACTOR_SEND => "ACTOR_SEND",
        // Logical
        AND => "AND",
        OR => "OR",
        NOT => "NOT",
        _ => "UNKNOWN",
    }
}

// ============================================================================
// Instruction Encoder/Decoder
// ============================================================================

/// Bytecode instruction encoder.
///
/// Provides methods to encode instructions with their operands.
pub struct InstructionEncoder {
    code: Vec<u8>,
}

impl InstructionEncoder {
    /// Create a new instruction encoder.
    pub fn new() -> Self {
        Self { code: Vec::new() }
    }

    /// Get the current bytecode position (for jump fixups).
    pub fn position(&self) -> usize {
        self.code.len()
    }

    /// Emit a raw opcode.
    pub fn emit_opcode(&mut self, opcode: Opcode) {
        self.code.extend_from_slice(&opcode.to_le_bytes());
    }

    /// Emit a u16 operand.
    pub fn emit_u16(&mut self, value: u16) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit a u32 operand.
    pub fn emit_u32(&mut self, value: u32) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit an i32 operand.
    pub fn emit_i32(&mut self, value: i32) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit an i64 operand.
    pub fn emit_i64(&mut self, value: i64) {
        self.code.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit an f64 operand.
    pub fn emit_f64(&mut self, value: f64) {
        self.code.extend_from_slice(&value.to_bits().to_le_bytes());
    }

    /// Patch a u32 value at a specific position (for jump fixups).
    pub fn patch_u32(&mut self, position: usize, value: u32) {
        let bytes = value.to_le_bytes();
        self.code[position..position + 4].copy_from_slice(&bytes);
    }

    /// Patch an i32 value at a specific position (for jump fixups).
    pub fn patch_i32(&mut self, position: usize, value: i32) {
        let bytes = value.to_le_bytes();
        self.code[position..position + 4].copy_from_slice(&bytes);
    }

    /// Get the final bytecode.
    pub fn finish(self) -> Vec<u8> {
        self.code
    }

    /// Get a reference to the bytecode (without consuming).
    pub fn as_bytes(&self) -> &[u8] {
        &self.code
    }
}

impl Default for InstructionEncoder {
    fn default() -> Self {
        Self::new()
    }
}

/// Bytecode instruction decoder.
///
/// Provides methods to read instructions and operands from bytecode.
pub struct InstructionDecoder<'a> {
    code: &'a [u8],
    ip: usize,
}

impl<'a> InstructionDecoder<'a> {
    /// Create a new instruction decoder.
    pub fn new(code: &'a [u8]) -> Self {
        Self { code, ip: 0 }
    }

    /// Get the current instruction pointer.
    pub fn position(&self) -> usize {
        self.ip
    }

    /// Set the instruction pointer (for jumps).
    pub fn set_position(&mut self, position: usize) {
        self.ip = position;
    }

    /// Check if there are more bytes to read.
    pub fn has_more(&self) -> bool {
        self.ip < self.code.len()
    }

    /// Read an opcode.
    pub fn read_opcode(&mut self) -> Option<Opcode> {
        if self.ip + 2 > self.code.len() {
            return None;
        }
        let bytes = [self.code[self.ip], self.code[self.ip + 1]];
        self.ip += 2;
        Some(u16::from_le_bytes(bytes))
    }

    /// Read a u16 operand.
    pub fn read_u16(&mut self) -> Option<u16> {
        if self.ip + 2 > self.code.len() {
            return None;
        }
        let bytes = [self.code[self.ip], self.code[self.ip + 1]];
        self.ip += 2;
        Some(u16::from_le_bytes(bytes))
    }

    /// Read a u32 operand.
    pub fn read_u32(&mut self) -> Option<u32> {
        if self.ip + 4 > self.code.len() {
            return None;
        }
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 4]);
        self.ip += 4;
        Some(u32::from_le_bytes(bytes))
    }

    /// Read an i32 operand.
    pub fn read_i32(&mut self) -> Option<i32> {
        if self.ip + 4 > self.code.len() {
            return None;
        }
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 4]);
        self.ip += 4;
        Some(i32::from_le_bytes(bytes))
    }

    /// Read an i64 operand.
    pub fn read_i64(&mut self) -> Option<i64> {
        if self.ip + 8 > self.code.len() {
            return None;
        }
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 8]);
        self.ip += 8;
        Some(i64::from_le_bytes(bytes))
    }

    /// Read an f64 operand.
    pub fn read_f64(&mut self) -> Option<f64> {
        if self.ip + 8 > self.code.len() {
            return None;
        }
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 8]);
        self.ip += 8;
        Some(f64::from_bits(u64::from_le_bytes(bytes)))
    }
}

// ============================================================================
// Debugging
// ============================================================================

impl fmt::Display for InstructionEncoder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "InstructionEncoder({} bytes)", self.code.len())
    }
}

impl fmt::Debug for InstructionEncoder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InstructionEncoder")
            .field("code_len", &self.code.len())
            .field("code", &format!("{:02X?}", &self.code[..self.code.len().min(32)]))
            .finish()
    }
}
