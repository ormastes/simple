//! Stack-based bytecode virtual machine.
//!
//! This module implements the execution engine for Simple bytecode. It provides
//! a stack-based VM that executes bytecode instructions compiled from MIR.
//!
//! **Architecture:**
//! ```text
//! ┌─────────────────┐
//! │  Operand Stack  │ ← Temporary values
//! ├─────────────────┤
//! │   Call Stack    │ ← Function call frames
//! ├─────────────────┤
//! │  Local Variables│ ← Function locals (per frame)
//! ├─────────────────┤
//! │  Constants Pool │ ← Compile-time constants
//! ├─────────────────┤
//! │  FFI Table      │ ← Runtime function pointers
//! └─────────────────┘
//! ```

use super::opcodes::*;
use crate::value::RuntimeValue;
use std::fmt;

/// Maximum stack depth (prevents stack overflow).
const MAX_STACK_DEPTH: usize = 10_000;

/// Maximum call stack depth (prevents infinite recursion).
const MAX_CALL_DEPTH: usize = 1_000;

/// VM error types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VmError {
    /// Stack overflow (too many values on stack).
    StackOverflow,
    /// Stack underflow (attempted pop from empty stack).
    StackUnderflow,
    /// Call stack overflow (too many nested function calls).
    CallStackOverflow,
    /// Unknown opcode encountered.
    UnknownOpcode(Opcode),
    /// Invalid register access.
    InvalidRegister(u16),
    /// Division by zero.
    DivisionByZero,
    /// Invalid jump target.
    InvalidJumpTarget(isize),
    /// Invalid function index.
    InvalidFunctionIndex(u32),
    /// Invalid constant index.
    InvalidConstantIndex(u32),
    /// Invalid FFI function index.
    InvalidFfiIndex(u16),
    /// Type mismatch (expected one type, got another).
    TypeMismatch { expected: &'static str, got: &'static str },
    /// End of bytecode reached unexpectedly.
    UnexpectedEndOfCode,
    /// Runtime FFI call failed.
    FfiCallFailed(String),
}

impl fmt::Display for VmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VmError::StackOverflow => write!(f, "Stack overflow"),
            VmError::StackUnderflow => write!(f, "Stack underflow"),
            VmError::CallStackOverflow => write!(f, "Call stack overflow (max depth: {})", MAX_CALL_DEPTH),
            VmError::UnknownOpcode(opcode) => write!(f, "Unknown opcode: 0x{:04X}", opcode),
            VmError::InvalidRegister(reg) => write!(f, "Invalid register: r{}", reg),
            VmError::DivisionByZero => write!(f, "Division by zero"),
            VmError::InvalidJumpTarget(offset) => write!(f, "Invalid jump target: {}", offset),
            VmError::InvalidFunctionIndex(idx) => write!(f, "Invalid function index: {}", idx),
            VmError::InvalidConstantIndex(idx) => write!(f, "Invalid constant index: {}", idx),
            VmError::InvalidFfiIndex(idx) => write!(f, "Invalid FFI index: {}", idx),
            VmError::TypeMismatch { expected, got } => write!(f, "Type mismatch: expected {}, got {}", expected, got),
            VmError::UnexpectedEndOfCode => write!(f, "Unexpected end of bytecode"),
            VmError::FfiCallFailed(msg) => write!(f, "FFI call failed: {}", msg),
        }
    }
}

impl std::error::Error for VmError {}

/// VM result type.
pub type VmResult<T> = Result<T, VmError>;

/// Function call frame.
///
/// Represents a single function activation on the call stack.
#[derive(Debug, Clone)]
pub struct CallFrame {
    /// Function index in the module.
    pub function_index: u32,
    /// Return address (instruction pointer to resume at).
    pub return_address: usize,
    /// Frame pointer (start of locals for this frame).
    pub frame_pointer: usize,
    /// Number of local variables in this frame.
    pub local_count: u16,
}

/// Function metadata (describes a compiled function).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionMetadata {
    /// Function name (for debugging).
    pub name: String,
    /// Bytecode offset in the code section.
    pub code_offset: usize,
    /// Length of bytecode for this function.
    pub code_length: usize,
    /// Number of parameters.
    pub param_count: u16,
    /// Number of local variables (including parameters).
    pub local_count: u16,
}

/// FFI function pointer type.
///
/// Takes a slice of arguments and returns a result.
pub type FfiFunctionPtr = fn(&[RuntimeValue]) -> VmResult<RuntimeValue>;

/// Bytecode virtual machine.
///
/// Executes bytecode instructions using a stack-based architecture.
pub struct BytecodeVM {
    // =========================================================================
    // Execution State
    // =========================================================================
    /// Operand stack (for expression evaluation).
    stack: Vec<RuntimeValue>,

    /// Call stack (function activation records).
    call_stack: Vec<CallFrame>,

    /// Instruction pointer (current position in bytecode).
    ip: usize,

    /// Local variables (flat array, indexed by frame_pointer + local_index).
    locals: Vec<RuntimeValue>,

    // =========================================================================
    // Module Context
    // =========================================================================
    /// Bytecode being executed.
    code: Vec<u8>,

    /// Constant pool (compile-time constants).
    constants: Vec<RuntimeValue>,

    /// Function metadata table.
    functions: Vec<FunctionMetadata>,

    /// FFI function table (runtime native functions).
    ffi_table: Vec<FfiFunctionPtr>,
}

impl BytecodeVM {
    /// Create a new bytecode VM.
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(256),
            call_stack: Vec::with_capacity(64),
            ip: 0,
            locals: Vec::with_capacity(256),
            code: Vec::new(),
            constants: Vec::new(),
            functions: Vec::new(),
            ffi_table: Vec::new(),
        }
    }

    /// Load bytecode into the VM.
    ///
    /// This sets up the code, constants, and function tables.
    pub fn load_bytecode(&mut self, code: &[u8]) {
        self.code = code.to_vec();
        self.ip = 0;
        self.stack.clear();
        self.call_stack.clear();
        self.locals.clear();
    }

    /// Set the constant pool.
    pub fn set_constants(&mut self, constants: Vec<RuntimeValue>) {
        self.constants = constants;
    }

    /// Set the function table.
    pub fn set_functions(&mut self, functions: Vec<FunctionMetadata>) {
        self.functions = functions;
    }

    /// Set the FFI function table.
    pub fn set_ffi_table(&mut self, ffi_table: Vec<FfiFunctionPtr>) {
        self.ffi_table = ffi_table;
    }

    // =========================================================================
    // Stack Operations
    // =========================================================================

    /// Push a value onto the operand stack.
    #[inline]
    fn push(&mut self, value: RuntimeValue) -> VmResult<()> {
        if self.stack.len() >= MAX_STACK_DEPTH {
            return Err(VmError::StackOverflow);
        }
        self.stack.push(value);
        Ok(())
    }

    /// Pop a value from the operand stack.
    #[inline]
    fn pop(&mut self) -> VmResult<RuntimeValue> {
        self.stack.pop().ok_or(VmError::StackUnderflow)
    }

    /// Peek at the top of the stack without popping.
    #[inline]
    fn peek(&self) -> VmResult<RuntimeValue> {
        self.stack.last().copied().ok_or(VmError::StackUnderflow)
    }

    /// Get a stack slot by index.
    #[inline]
    fn get_stack(&self, index: u16) -> VmResult<RuntimeValue> {
        self.stack
            .get(index as usize)
            .copied()
            .ok_or(VmError::InvalidRegister(index))
    }

    /// Set a stack slot by index (auto-expands stack if needed).
    #[inline]
    fn set_stack(&mut self, index: u16, value: RuntimeValue) -> VmResult<()> {
        let index = index as usize;
        // Auto-expand stack if accessing beyond current size
        if index >= self.stack.len() {
            if index >= MAX_STACK_DEPTH {
                return Err(VmError::StackOverflow);
            }
            self.stack.resize(index + 1, RuntimeValue::NIL);
        }
        self.stack[index] = value;
        Ok(())
    }

    // =========================================================================
    // Local Variable Operations
    // =========================================================================

    /// Get a local variable.
    #[inline]
    fn get_local(&self, local_index: u16) -> VmResult<RuntimeValue> {
        // If no call frame, use direct indexing (for testing)
        let index = if let Some(frame) = self.call_stack.last() {
            frame.frame_pointer + (local_index as usize)
        } else {
            local_index as usize
        };

        self.locals
            .get(index)
            .copied()
            .ok_or(VmError::InvalidRegister(local_index))
    }

    /// Set a local variable.
    #[inline]
    fn set_local(&mut self, local_index: u16, value: RuntimeValue) -> VmResult<()> {
        // If no call frame, use direct indexing (for testing)
        let index = if let Some(frame) = self.call_stack.last() {
            frame.frame_pointer + (local_index as usize)
        } else {
            local_index as usize
        };

        // Auto-expand locals if needed
        if index >= self.locals.len() {
            self.locals.resize(index + 1, RuntimeValue::NIL);
        }
        self.locals[index] = value;
        Ok(())
    }

    // =========================================================================
    // Bytecode Reading
    // =========================================================================

    /// Read a u16 from bytecode.
    #[inline]
    fn read_u16(&mut self) -> VmResult<u16> {
        if self.ip + 2 > self.code.len() {
            return Err(VmError::UnexpectedEndOfCode);
        }
        let bytes = [self.code[self.ip], self.code[self.ip + 1]];
        self.ip += 2;
        Ok(u16::from_le_bytes(bytes))
    }

    /// Read a u32 from bytecode.
    #[inline]
    fn read_u32(&mut self) -> VmResult<u32> {
        if self.ip + 4 > self.code.len() {
            return Err(VmError::UnexpectedEndOfCode);
        }
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 4]);
        self.ip += 4;
        Ok(u32::from_le_bytes(bytes))
    }

    /// Read an i32 from bytecode.
    #[inline]
    fn read_i32(&mut self) -> VmResult<i32> {
        if self.ip + 4 > self.code.len() {
            return Err(VmError::UnexpectedEndOfCode);
        }
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 4]);
        self.ip += 4;
        Ok(i32::from_le_bytes(bytes))
    }

    /// Read an i64 from bytecode.
    #[inline]
    fn read_i64(&mut self) -> VmResult<i64> {
        if self.ip + 8 > self.code.len() {
            return Err(VmError::UnexpectedEndOfCode);
        }
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 8]);
        self.ip += 8;
        Ok(i64::from_le_bytes(bytes))
    }

    /// Read an f64 from bytecode.
    #[inline]
    fn read_f64(&mut self) -> VmResult<f64> {
        if self.ip + 8 > self.code.len() {
            return Err(VmError::UnexpectedEndOfCode);
        }
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.code[self.ip..self.ip + 8]);
        self.ip += 8;
        Ok(f64::from_bits(u64::from_le_bytes(bytes)))
    }

    // =========================================================================
    // Execution
    // =========================================================================

    /// Execute bytecode starting from the current IP.
    ///
    /// Returns the final value on the stack (return value).
    pub fn execute(&mut self) -> VmResult<RuntimeValue> {
        loop {
            // Check if we've reached the end
            if self.ip >= self.code.len() {
                // If call stack is empty, return top of stack
                if self.call_stack.is_empty() {
                    return self.pop();
                }
                return Err(VmError::UnexpectedEndOfCode);
            }

            // Read opcode
            let opcode = self.read_u16()?;

            // Execute instruction
            match opcode {
                // =============================================================
                // Constants
                // =============================================================
                CONST_I64 => {
                    let dest = self.read_u16()?;
                    let value = self.read_i64()?;
                    let rv = RuntimeValue::from_int(value);
                    self.set_stack(dest, rv)?;
                }

                CONST_F64 => {
                    let dest = self.read_u16()?;
                    let value = self.read_f64()?;
                    let rv = RuntimeValue::from_float(value);
                    self.set_stack(dest, rv)?;
                }

                CONST_TRUE => {
                    let dest = self.read_u16()?;
                    self.set_stack(dest, RuntimeValue::TRUE)?;
                }

                CONST_FALSE => {
                    let dest = self.read_u16()?;
                    self.set_stack(dest, RuntimeValue::FALSE)?;
                }

                CONST_NONE => {
                    let dest = self.read_u16()?;
                    self.set_stack(dest, RuntimeValue::NIL)?;
                }

                CONST_UNIT => {
                    let dest = self.read_u16()?;
                    self.set_stack(dest, RuntimeValue::NIL)?; // Unit is same as nil for now
                }

                LOAD_CONST => {
                    let dest = self.read_u16()?;
                    let const_idx = self.read_u32()?;
                    let value = *self
                        .constants
                        .get(const_idx as usize)
                        .ok_or(VmError::InvalidConstantIndex(const_idx))?;
                    self.set_stack(dest, value)?;
                }

                // =============================================================
                // Stack Operations
                // =============================================================
                PUSH => {
                    let src = self.read_u16()?;
                    let value = self.get_stack(src)?;
                    self.push(value)?;
                }

                POP => {
                    let dest = self.read_u16()?;
                    let value = self.pop()?;
                    self.set_stack(dest, value)?;
                }

                DUP => {
                    let src = self.read_u16()?;
                    let dest = self.read_u16()?;
                    let value = self.get_stack(src)?;
                    self.set_stack(dest, value)?;
                }

                SWAP => {
                    let a = self.read_u16()?;
                    let b = self.read_u16()?;
                    let val_a = self.get_stack(a)?;
                    let val_b = self.get_stack(b)?;
                    self.set_stack(a, val_b)?;
                    self.set_stack(b, val_a)?;
                }

                // =============================================================
                // Arithmetic (i64)
                // =============================================================
                ADD_I64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_int(a.as_int() + b.as_int());
                    self.push(result)?;
                }

                SUB_I64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_int(a.as_int() - b.as_int());
                    self.push(result)?;
                }

                MUL_I64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_int(a.as_int() * b.as_int());
                    self.push(result)?;
                }

                DIV_I64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    if b.as_int() == 0 {
                        return Err(VmError::DivisionByZero);
                    }
                    let result = RuntimeValue::from_int(a.as_int() / b.as_int());
                    self.push(result)?;
                }

                MOD_I64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    if b.as_int() == 0 {
                        return Err(VmError::DivisionByZero);
                    }
                    let result = RuntimeValue::from_int(a.as_int() % b.as_int());
                    self.push(result)?;
                }

                NEG_I64 => {
                    let a = self.pop()?;
                    let result = RuntimeValue::from_int(-a.as_int());
                    self.push(result)?;
                }

                // =============================================================
                // Arithmetic (f64)
                // =============================================================
                ADD_F64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_float(a.as_float() + b.as_float());
                    self.push(result)?;
                }

                SUB_F64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_float(a.as_float() - b.as_float());
                    self.push(result)?;
                }

                MUL_F64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_float(a.as_float() * b.as_float());
                    self.push(result)?;
                }

                DIV_F64 => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_float(a.as_float() / b.as_float());
                    self.push(result)?;
                }

                // =============================================================
                // Comparison
                // =============================================================
                EQ => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_bool(a == b);
                    self.push(result)?;
                }

                NE => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_bool(a != b);
                    self.push(result)?;
                }

                LT => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = if a.is_int() && b.is_int() {
                        RuntimeValue::from_bool(a.as_int() < b.as_int())
                    } else {
                        RuntimeValue::from_bool(a.as_float() < b.as_float())
                    };
                    self.push(result)?;
                }

                LE => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = if a.is_int() && b.is_int() {
                        RuntimeValue::from_bool(a.as_int() <= b.as_int())
                    } else {
                        RuntimeValue::from_bool(a.as_float() <= b.as_float())
                    };
                    self.push(result)?;
                }

                GT => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = if a.is_int() && b.is_int() {
                        RuntimeValue::from_bool(a.as_int() > b.as_int())
                    } else {
                        RuntimeValue::from_bool(a.as_float() > b.as_float())
                    };
                    self.push(result)?;
                }

                GE => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = if a.is_int() && b.is_int() {
                        RuntimeValue::from_bool(a.as_int() >= b.as_int())
                    } else {
                        RuntimeValue::from_bool(a.as_float() >= b.as_float())
                    };
                    self.push(result)?;
                }

                // =============================================================
                // Logical Operations
                // =============================================================
                AND => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_bool(a.as_bool() && b.as_bool());
                    self.push(result)?;
                }

                OR => {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    let result = RuntimeValue::from_bool(a.as_bool() || b.as_bool());
                    self.push(result)?;
                }

                NOT => {
                    let a = self.pop()?;
                    let result = RuntimeValue::from_bool(!a.as_bool());
                    self.push(result)?;
                }

                // =============================================================
                // Control Flow
                // =============================================================
                JMP => {
                    let offset = self.read_i32()?;
                    let new_ip = (self.ip as isize).checked_add(offset as isize)
                        .ok_or(VmError::InvalidJumpTarget(offset as isize))?;
                    if new_ip < 0 || new_ip > self.code.len() as isize {
                        return Err(VmError::InvalidJumpTarget(new_ip));
                    }
                    self.ip = new_ip as usize;
                }

                JMP_IF => {
                    let offset = self.read_i32()?;
                    let cond = self.pop()?;
                    if cond.as_bool() {
                        let new_ip = (self.ip as isize).checked_add(offset as isize)
                            .ok_or(VmError::InvalidJumpTarget(offset as isize))?;
                        if new_ip < 0 || new_ip > self.code.len() as isize {
                            return Err(VmError::InvalidJumpTarget(new_ip));
                        }
                        self.ip = new_ip as usize;
                    }
                }

                JMP_IF_NOT => {
                    let offset = self.read_i32()?;
                    let cond = self.pop()?;
                    if !cond.as_bool() {
                        let new_ip = (self.ip as isize).checked_add(offset as isize)
                            .ok_or(VmError::InvalidJumpTarget(offset as isize))?;
                        if new_ip < 0 || new_ip > self.code.len() as isize {
                            return Err(VmError::InvalidJumpTarget(new_ip));
                        }
                        self.ip = new_ip as usize;
                    }
                }

                RET => {
                    let value_reg = self.read_u16()?;
                    let return_value = self.get_stack(value_reg)?;

                    // If no call frame, just return the value (for direct execution)
                    if self.call_stack.is_empty() {
                        return Ok(return_value);
                    }

                    // Pop call frame
                    let frame = self.call_stack.pop().unwrap();
                    self.ip = frame.return_address;

                    // Restore locals (pop frame's locals)
                    self.locals.truncate(frame.frame_pointer);

                    // If this was the last frame, return the value
                    if self.call_stack.is_empty() {
                        return Ok(return_value);
                    }

                    // Otherwise, push return value to stack
                    self.push(return_value)?;
                }

                RET_VOID => {
                    // If no call frame, just return nil (for direct execution)
                    if self.call_stack.is_empty() {
                        return Ok(RuntimeValue::NIL);
                    }

                    // Pop call frame
                    let frame = self.call_stack.pop().unwrap();
                    self.ip = frame.return_address;

                    // Restore locals
                    self.locals.truncate(frame.frame_pointer);

                    // If this was the last frame, return nil
                    if self.call_stack.is_empty() {
                        return Ok(RuntimeValue::NIL);
                    }

                    // Otherwise, push nil to stack
                    self.push(RuntimeValue::NIL)?;
                }

                // =============================================================
                // Memory Operations (Phase 2)
                // =============================================================
                LOAD => {
                    let dest = self.read_u16()?;
                    let local_idx = self.read_u16()?;
                    let value = self.get_local(local_idx)?;
                    self.set_stack(dest, value)?;
                }

                STORE => {
                    let local_idx = self.read_u16()?;
                    let src = self.read_u16()?;
                    let value = self.get_stack(src)?;
                    self.set_local(local_idx, value)?;
                }

                LOAD_STRING => {
                    let dest = self.read_u16()?;
                    let const_idx = self.read_u32()?;
                    let value = *self
                        .constants
                        .get(const_idx as usize)
                        .ok_or(VmError::InvalidConstantIndex(const_idx))?;
                    self.set_stack(dest, value)?;
                }

                // =============================================================
                // Function Calls
                // =============================================================
                CALL => {
                    let func_idx = self.read_u32()?;
                    let argc = self.read_u16()?;

                    let func = self
                        .functions
                        .get(func_idx as usize)
                        .ok_or(VmError::InvalidFunctionIndex(func_idx))?
                        .clone();

                    // Pop arguments from eval stack
                    let mut args = Vec::with_capacity(argc as usize);
                    for _ in 0..argc {
                        args.push(self.pop()?);
                    }
                    args.reverse(); // Args were pushed L→R, popped R→L

                    // Set up locals for new frame
                    let frame_pointer = self.locals.len();
                    self.locals.resize(
                        frame_pointer + func.local_count as usize,
                        RuntimeValue::NIL,
                    );
                    for (i, arg) in args.iter().enumerate() {
                        self.locals[frame_pointer + i] = *arg;
                    }

                    // Push call frame
                    if self.call_stack.len() >= MAX_CALL_DEPTH {
                        return Err(VmError::CallStackOverflow);
                    }
                    self.call_stack.push(CallFrame {
                        function_index: func_idx,
                        return_address: self.ip,
                        frame_pointer,
                        local_count: func.local_count,
                    });

                    // Jump to function
                    self.ip = func.code_offset;
                }

                CALL_FFI => {
                    let ffi_idx = self.read_u16()?;
                    let argc = self.read_u16()?;

                    // Pop arguments from eval stack
                    let mut args = Vec::with_capacity(argc as usize);
                    for _ in 0..argc {
                        args.push(self.pop()?);
                    }
                    args.reverse();

                    let ffi_fn = self
                        .ffi_table
                        .get(ffi_idx as usize)
                        .ok_or(VmError::InvalidFfiIndex(ffi_idx))?;

                    let result = ffi_fn(&args)?;
                    self.push(result)?;
                }

                CALL_RUNTIME => {
                    let rt_idx = self.read_u16()?;
                    let argc = self.read_u16()?;

                    // Same as CALL_FFI for now
                    let mut args = Vec::with_capacity(argc as usize);
                    for _ in 0..argc {
                        args.push(self.pop()?);
                    }
                    args.reverse();

                    let ffi_fn = self
                        .ffi_table
                        .get(rt_idx as usize)
                        .ok_or(VmError::InvalidFfiIndex(rt_idx))?;

                    let result = ffi_fn(&args)?;
                    self.push(result)?;
                }

                CALL_INDIRECT => {
                    let argc = self.read_u16()?;
                    // Pop function pointer from stack
                    let _func_ptr = self.pop()?;
                    // Pop arguments
                    let mut _args = Vec::with_capacity(argc as usize);
                    for _ in 0..argc {
                        _args.push(self.pop()?);
                    }
                    // TODO: Implement indirect call via closure/function pointer
                    self.push(RuntimeValue::NIL)?;
                }

                // =============================================================
                // Collections
                // =============================================================
                ARRAY_LIT => {
                    let dest = self.read_u16()?;
                    let count = self.read_u16()?;
                    let _type_hint = self.read_u16()?;

                    let mut elements = Vec::with_capacity(count as usize);
                    for _ in 0..count {
                        elements.push(self.pop()?);
                    }
                    elements.reverse();

                    let arr = crate::value::rt_array_new(count as u64);
                    for (i, elem) in elements.iter().enumerate() {
                        crate::value::rt_array_set(arr, i as i64, *elem);
                    }
                    self.set_stack(dest, arr)?;
                }

                DICT_LIT => {
                    let dest = self.read_u16()?;
                    let count = self.read_u16()?;

                    let mut pairs = Vec::with_capacity(count as usize * 2);
                    for _ in 0..count * 2 {
                        pairs.push(self.pop()?);
                    }
                    pairs.reverse();

                    let dict = crate::value::rt_dict_new(count as u64);
                    for i in 0..count as usize {
                        let key = pairs[i * 2];
                        let val = pairs[i * 2 + 1];
                        crate::value::rt_dict_set(dict, key, val);
                    }
                    self.set_stack(dest, dict)?;
                }

                TUPLE_LIT => {
                    let dest = self.read_u16()?;
                    let count = self.read_u16()?;

                    let mut elements = Vec::with_capacity(count as usize);
                    for _ in 0..count {
                        elements.push(self.pop()?);
                    }
                    elements.reverse();

                    let tuple = crate::value::rt_tuple_new(count as u64);
                    for (i, elem) in elements.iter().enumerate() {
                        crate::value::rt_tuple_set(tuple, i as u64, *elem);
                    }
                    self.set_stack(dest, tuple)?;
                }

                INDEX_GET => {
                    let dest = self.read_u16()?;
                    let container = self.read_u16()?;
                    let index = self.read_u16()?;
                    let coll = self.get_stack(container)?;
                    let idx = self.get_stack(index)?;
                    let result = crate::value::rt_index_get(coll, idx);
                    self.set_stack(dest, result)?;
                }

                INDEX_SET => {
                    let container = self.read_u16()?;
                    let index = self.read_u16()?;
                    let value = self.read_u16()?;
                    let coll = self.get_stack(container)?;
                    let idx = self.get_stack(index)?;
                    let val = self.get_stack(value)?;
                    crate::value::rt_index_set(coll, idx, val);
                }

                LEN => {
                    let dest = self.read_u16()?;
                    let container = self.read_u16()?;
                    let coll = self.get_stack(container)?;
                    let len = crate::value::rt_array_len(coll);
                    self.set_stack(dest, RuntimeValue::from_int(len))?;
                }

                APPEND => {
                    let container = self.read_u16()?;
                    let value = self.read_u16()?;
                    let coll = self.get_stack(container)?;
                    let val = self.get_stack(value)?;
                    crate::value::rt_array_push(coll, val);
                }

                // =============================================================
                // Pattern Matching
                // =============================================================
                ENUM_MATCH => {
                    let dest = self.read_u16()?;
                    let enum_val = self.read_u16()?;
                    let discriminant = self.read_u16()?;
                    let val = self.get_stack(enum_val)?;
                    let disc = crate::value::rt_enum_discriminant(val);
                    let matches = disc == discriminant as i64;
                    self.set_stack(dest, RuntimeValue::from_bool(matches))?;
                }

                ENUM_PAYLOAD => {
                    let dest = self.read_u16()?;
                    let enum_val = self.read_u16()?;
                    let _field_idx = self.read_u16()?;
                    let val = self.get_stack(enum_val)?;
                    let payload = crate::value::rt_enum_payload(val);
                    self.set_stack(dest, payload)?;
                }

                ENUM_NEW => {
                    let dest = self.read_u16()?;
                    let discriminant = self.read_u16()?;
                    let field_count = self.read_u16()?;

                    let mut fields = Vec::with_capacity(field_count as usize);
                    for _ in 0..field_count {
                        fields.push(self.pop()?);
                    }
                    fields.reverse();

                    let payload = if fields.is_empty() {
                        RuntimeValue::NIL
                    } else {
                        fields[0]
                    };

                    // rt_enum_new takes (enum_id: u32, discriminant: u32, payload: RuntimeValue)
                    let enum_val = crate::value::rt_enum_new(0, discriminant as u32, payload);
                    self.set_stack(dest, enum_val)?;
                }

                IS_SOME => {
                    let dest = self.read_u16()?;
                    let opt = self.read_u16()?;
                    let val = self.get_stack(opt)?;
                    self.set_stack(dest, RuntimeValue::from_bool(!val.is_nil()))?;
                }

                // =============================================================
                // Unknown Opcode
                // =============================================================
                _ => {
                    return Err(VmError::UnknownOpcode(opcode));
                }
            }
        }
    }

    /// Call a function by index with arguments.
    ///
    /// This is the main entry point for executing a function.
    pub fn call_function(&mut self, func_index: u32, args: &[RuntimeValue]) -> VmResult<RuntimeValue> {
        // Get function metadata
        let func = self
            .functions
            .get(func_index as usize)
            .ok_or(VmError::InvalidFunctionIndex(func_index))?
            .clone();

        // Validate argument count
        if args.len() != func.param_count as usize {
            return Err(VmError::FfiCallFailed(format!(
                "Function {} expects {} arguments, got {}",
                func.name,
                func.param_count,
                args.len()
            )));
        }

        // Set up locals for this function
        let frame_pointer = self.locals.len();
        self.locals.resize(frame_pointer + func.local_count as usize, RuntimeValue::NIL);

        // Copy arguments to locals
        for (i, arg) in args.iter().enumerate() {
            self.locals[frame_pointer + i] = *arg;
        }

        // Push call frame
        if self.call_stack.len() >= MAX_CALL_DEPTH {
            return Err(VmError::CallStackOverflow);
        }
        self.call_stack.push(CallFrame {
            function_index: func_index,
            return_address: self.code.len(), // Return to end (will trigger return)
            frame_pointer,
            local_count: func.local_count,
        });

        // Set instruction pointer to function start
        self.ip = func.code_offset;

        // Execute
        self.execute()
    }
}

impl Default for BytecodeVM {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for BytecodeVM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BytecodeVM")
            .field("ip", &self.ip)
            .field("stack_len", &self.stack.len())
            .field("call_depth", &self.call_stack.len())
            .field("locals_len", &self.locals.len())
            .field("code_len", &self.code.len())
            .field("constants_len", &self.constants.len())
            .field("functions_len", &self.functions.len())
            .finish()
    }
}
