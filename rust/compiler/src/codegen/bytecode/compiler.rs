//! MIR-to-bytecode compiler.
//!
//! Compiles MIR functions into bytecode that can be executed by the
//! `BytecodeVM` in `simple-runtime`.
//!
//! **Architecture:**
//! ```text
//! MirFunction
//!   ├── blocks[0] (entry)
//!   │   ├── instructions: [ConstInt, BinOp, ...]
//!   │   └── terminator: Branch { cond, then, else }
//!   ├── blocks[1]
//!   │   ├── instructions: [...]
//!   │   └── terminator: Return(value)
//!   └── ...
//!
//!   ↓ compile_function()
//!
//! BytecodeFunction
//!   ├── code: [u8]           (flat bytecode)
//!   ├── constants: [RuntimeValue]
//!   └── metadata: FunctionMetadata
//! ```
//!
//! **Register Mapping:**
//! MIR uses SSA virtual registers (VReg). Bytecode uses stack slots.
//! Each VReg is mapped to a stack slot index (u16).

use std::collections::HashMap;

use simple_runtime::bytecode::opcodes::{self, InstructionEncoder};
use simple_runtime::bytecode::vm::FunctionMetadata;
use simple_runtime::RuntimeValue;

use crate::hir::{BinOp, UnaryOp};
use crate::mir::{BlockId, CallTarget, MirBlock, MirFunction, MirInst, Terminator, VReg};

/// Compilation error.
#[derive(Debug, Clone)]
pub enum CompileError {
    /// Unsupported MIR instruction.
    UnsupportedInstruction(String),
    /// Too many virtual registers (> u16::MAX).
    TooManyRegisters(u32),
    /// Block not found.
    BlockNotFound(BlockId),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::UnsupportedInstruction(msg) => write!(f, "Unsupported instruction: {}", msg),
            CompileError::TooManyRegisters(count) => write!(f, "Too many registers: {} (max: 65535)", count),
            CompileError::BlockNotFound(id) => write!(f, "Block not found: {:?}", id),
        }
    }
}

impl std::error::Error for CompileError {}

/// Result of compiling a MIR function.
pub struct CompiledFunction {
    /// The compiled bytecode.
    pub code: Vec<u8>,
    /// Constants referenced by the bytecode.
    pub constants: Vec<RuntimeValue>,
    /// Function metadata for the VM.
    pub metadata: FunctionMetadata,
}

/// Result of compiling multiple functions.
pub struct CompiledModule {
    /// All compiled functions.
    pub functions: Vec<CompiledFunction>,
}

/// MIR-to-bytecode compiler.
///
/// Compiles MIR functions into bytecode instructions.
pub struct BytecodeCompiler {
    /// Instruction encoder.
    encoder: InstructionEncoder,

    /// VReg to stack slot mapping.
    vreg_map: HashMap<VReg, u16>,

    /// Next available stack slot.
    next_slot: u16,

    /// Block offsets (BlockId -> bytecode offset).
    block_offsets: HashMap<BlockId, usize>,

    /// Pending jump fixups (encoder position -> target BlockId).
    jump_fixups: Vec<(usize, BlockId)>,

    /// Constant pool.
    constants: Vec<RuntimeValue>,

    /// String constant pool (maps string -> constant index).
    string_pool: HashMap<String, u32>,
}

impl BytecodeCompiler {
    /// Create a new bytecode compiler.
    pub fn new() -> Self {
        Self {
            encoder: InstructionEncoder::new(),
            vreg_map: HashMap::new(),
            next_slot: 0,
            block_offsets: HashMap::new(),
            jump_fixups: Vec::new(),
            constants: Vec::new(),
            string_pool: HashMap::new(),
        }
    }

    /// Allocate a stack slot for a VReg.
    fn alloc_slot(&mut self, vreg: VReg) -> Result<u16, CompileError> {
        if let Some(&slot) = self.vreg_map.get(&vreg) {
            return Ok(slot);
        }
        if self.next_slot == u16::MAX {
            return Err(CompileError::TooManyRegisters(vreg.0));
        }
        let slot = self.next_slot;
        self.next_slot += 1;
        self.vreg_map.insert(vreg, slot);
        Ok(slot)
    }

    /// Get the stack slot for a VReg.
    fn get_slot(&mut self, vreg: VReg) -> Result<u16, CompileError> {
        // Auto-allocate if not seen yet
        self.alloc_slot(vreg)
    }

    /// Add a constant to the pool, returning its index.
    fn add_constant(&mut self, value: RuntimeValue) -> u32 {
        let idx = self.constants.len() as u32;
        self.constants.push(value);
        idx
    }

    /// Add a string constant to the pool, returning its index.
    fn add_string_constant(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.string_pool.get(s) {
            return idx;
        }
        let idx = self.constants.len() as u32;
        // Store string as a RuntimeValue (will be initialized by the loader)
        // For now, store a placeholder
        self.constants.push(RuntimeValue::NIL);
        self.string_pool.insert(s.to_string(), idx);
        idx
    }

    /// Record a pending jump fixup (offset position -> target block).
    fn record_jump_fixup(&mut self, target: BlockId) {
        let pos = self.encoder.position();
        self.jump_fixups.push((pos, target));
        // Emit placeholder offset
        self.encoder.emit_i32(0);
    }

    /// Resolve all pending jump fixups.
    fn resolve_jump_fixups(&mut self) -> Result<(), CompileError> {
        for (fixup_pos, target_block) in &self.jump_fixups {
            let target_offset = self
                .block_offsets
                .get(target_block)
                .ok_or(CompileError::BlockNotFound(*target_block))?;
            // Calculate relative offset from after the i32 operand
            let relative = (*target_offset as isize) - ((*fixup_pos + 4) as isize);
            self.encoder.patch_i32(*fixup_pos, relative as i32);
        }
        Ok(())
    }

    /// Compile a single MIR function to bytecode.
    pub fn compile_function(&mut self, func: &MirFunction) -> Result<CompiledFunction, CompileError> {
        // Reset state
        self.encoder = InstructionEncoder::new();
        self.vreg_map.clear();
        self.next_slot = 0;
        self.block_offsets.clear();
        self.jump_fixups.clear();
        self.constants.clear();
        self.string_pool.clear();

        // Pre-allocate slots for function parameters and emit LOAD instructions
        // to move params from locals (set by call_function) to stack slots
        for (i, _param) in func.params.iter().enumerate() {
            let vreg = VReg(i as u32);
            let slot = i as u16;
            self.vreg_map.insert(vreg, slot);
            self.next_slot = self.next_slot.max((i + 1) as u16);

            // Emit LOAD to move parameter from local[i] to stack slot[i]
            self.encoder.emit_opcode(opcodes::LOAD);
            self.encoder.emit_u16(slot); // dest stack slot
            self.encoder.emit_u16(i as u16); // local index
        }

        let code_offset = 0;

        // Compile blocks in order (entry block first)
        let entry_block_id = func.entry_block;

        // Build block order: entry first, then remaining blocks
        let mut block_order: Vec<&MirBlock> = Vec::new();
        let mut remaining: Vec<&MirBlock> = Vec::new();

        for block in &func.blocks {
            if block.id == entry_block_id {
                block_order.push(block);
            } else {
                remaining.push(block);
            }
        }
        block_order.extend(remaining);

        // Compile each block
        for block in &block_order {
            // Record block offset
            self.block_offsets.insert(block.id, self.encoder.position());

            // Compile each instruction in the block
            for inst in &block.instructions {
                self.compile_instruction(inst)?;
            }

            // Compile terminator
            self.compile_terminator(&block.terminator)?;
        }

        // Resolve jump fixups
        self.resolve_jump_fixups()?;

        let code = self.encoder.as_bytes().to_vec();
        let code_length = code.len();

        let metadata = FunctionMetadata {
            name: func.name.clone(),
            code_offset,
            code_length,
            param_count: func.params.len() as u16,
            local_count: self.next_slot,
        };

        Ok(CompiledFunction {
            code,
            constants: self.constants.clone(),
            metadata,
        })
    }

    /// Compile a single MIR instruction.
    fn compile_instruction(&mut self, inst: &MirInst) -> Result<(), CompileError> {
        match inst {
            // =================================================================
            // Constants
            // =================================================================
            MirInst::ConstInt { dest, value } => {
                let slot = self.alloc_slot(*dest)?;
                self.encoder.emit_opcode(opcodes::CONST_I64);
                self.encoder.emit_u16(slot);
                self.encoder.emit_i64(*value);
            }

            MirInst::ConstFloat { dest, value } => {
                let slot = self.alloc_slot(*dest)?;
                self.encoder.emit_opcode(opcodes::CONST_F64);
                self.encoder.emit_u16(slot);
                self.encoder.emit_f64(*value);
            }

            MirInst::ConstBool { dest, value } => {
                let slot = self.alloc_slot(*dest)?;
                if *value {
                    self.encoder.emit_opcode(opcodes::CONST_TRUE);
                } else {
                    self.encoder.emit_opcode(opcodes::CONST_FALSE);
                }
                self.encoder.emit_u16(slot);
            }

            MirInst::ConstString { dest, value } => {
                let slot = self.alloc_slot(*dest)?;
                let const_idx = self.add_string_constant(value);
                self.encoder.emit_opcode(opcodes::LOAD_STRING);
                self.encoder.emit_u16(slot);
                self.encoder.emit_u32(const_idx);
            }

            // =================================================================
            // Copy
            // =================================================================
            MirInst::Copy { dest, src } => {
                let dest_slot = self.alloc_slot(*dest)?;
                let src_slot = self.get_slot(*src)?;
                self.encoder.emit_opcode(opcodes::DUP);
                self.encoder.emit_u16(src_slot);
                self.encoder.emit_u16(dest_slot);
            }

            // =================================================================
            // Binary Operations
            // =================================================================
            MirInst::BinOp { dest, op, left, right } => {
                let dest_slot = self.alloc_slot(*dest)?;
                let left_slot = self.get_slot(*left)?;
                let right_slot = self.get_slot(*right)?;

                // Push operands onto eval stack
                self.encoder.emit_opcode(opcodes::PUSH);
                self.encoder.emit_u16(left_slot);
                self.encoder.emit_opcode(opcodes::PUSH);
                self.encoder.emit_u16(right_slot);

                // Emit operation
                match op {
                    BinOp::Add => self.encoder.emit_opcode(opcodes::ADD_I64),
                    BinOp::Sub => self.encoder.emit_opcode(opcodes::SUB_I64),
                    BinOp::Mul => self.encoder.emit_opcode(opcodes::MUL_I64),
                    BinOp::Div => self.encoder.emit_opcode(opcodes::DIV_I64),
                    BinOp::Mod => self.encoder.emit_opcode(opcodes::MOD_I64),
                    BinOp::Eq => self.encoder.emit_opcode(opcodes::EQ),
                    BinOp::NotEq => self.encoder.emit_opcode(opcodes::NE),
                    BinOp::Lt => self.encoder.emit_opcode(opcodes::LT),
                    BinOp::Gt => self.encoder.emit_opcode(opcodes::GT),
                    BinOp::LtEq => self.encoder.emit_opcode(opcodes::LE),
                    BinOp::GtEq => self.encoder.emit_opcode(opcodes::GE),
                    BinOp::And | BinOp::AndSuspend => self.encoder.emit_opcode(opcodes::AND),
                    BinOp::Or | BinOp::OrSuspend => self.encoder.emit_opcode(opcodes::OR),
                    _ => {
                        return Err(CompileError::UnsupportedInstruction(format!("BinOp {:?}", op)));
                    }
                }

                // Pop result to destination
                self.encoder.emit_opcode(opcodes::POP);
                self.encoder.emit_u16(dest_slot);
            }

            // =================================================================
            // Unary Operations
            // =================================================================
            MirInst::UnaryOp { dest, op, operand } => {
                let dest_slot = self.alloc_slot(*dest)?;
                let operand_slot = self.get_slot(*operand)?;

                self.encoder.emit_opcode(opcodes::PUSH);
                self.encoder.emit_u16(operand_slot);

                match op {
                    UnaryOp::Neg => self.encoder.emit_opcode(opcodes::NEG_I64),
                    UnaryOp::Not => self.encoder.emit_opcode(opcodes::NOT),
                    UnaryOp::BitNot => {
                        return Err(CompileError::UnsupportedInstruction("UnaryOp::BitNot".to_string()));
                    }
                }

                self.encoder.emit_opcode(opcodes::POP);
                self.encoder.emit_u16(dest_slot);
            }

            // =================================================================
            // Memory (Load/Store)
            // =================================================================
            MirInst::Load { dest, addr, .. } => {
                let dest_slot = self.alloc_slot(*dest)?;
                let addr_slot = self.get_slot(*addr)?;
                self.encoder.emit_opcode(opcodes::LOAD);
                self.encoder.emit_u16(dest_slot);
                self.encoder.emit_u16(addr_slot);
            }

            MirInst::Store { addr, value, .. } => {
                let addr_slot = self.get_slot(*addr)?;
                let value_slot = self.get_slot(*value)?;
                self.encoder.emit_opcode(opcodes::STORE);
                self.encoder.emit_u16(addr_slot);
                self.encoder.emit_u16(value_slot);
            }

            // =================================================================
            // Function Calls
            // =================================================================
            MirInst::Call { dest, target, args } => {
                let func_name = target.name();

                // Push arguments to eval stack
                for arg in args {
                    let arg_slot = self.get_slot(*arg)?;
                    self.encoder.emit_opcode(opcodes::PUSH);
                    self.encoder.emit_u16(arg_slot);
                }

                // Emit FFI call (for now, all calls go through FFI)
                // TODO: In Phase 2, distinguish between bytecode calls and FFI calls
                self.encoder.emit_opcode(opcodes::CALL_FFI);
                self.encoder.emit_u16(0); // FFI index (to be resolved by loader)
                self.encoder.emit_u16(args.len() as u16);

                // Pop result if dest is Some
                if let Some(dest_vreg) = dest {
                    let dest_slot = self.alloc_slot(*dest_vreg)?;
                    self.encoder.emit_opcode(opcodes::POP);
                    self.encoder.emit_u16(dest_slot);
                }
            }

            // =================================================================
            // Collections (Phase 2 - basic support)
            // =================================================================
            MirInst::ArrayLit { dest, elements } => {
                let dest_slot = self.alloc_slot(*dest)?;

                // Push elements to eval stack
                for elem in elements {
                    let elem_slot = self.get_slot(*elem)?;
                    self.encoder.emit_opcode(opcodes::PUSH);
                    self.encoder.emit_u16(elem_slot);
                }

                self.encoder.emit_opcode(opcodes::ARRAY_LIT);
                self.encoder.emit_u16(dest_slot);
                self.encoder.emit_u16(elements.len() as u16);
                self.encoder.emit_u16(0); // type (unused for now)
            }

            MirInst::TupleLit { dest, elements } => {
                let dest_slot = self.alloc_slot(*dest)?;

                for elem in elements {
                    let elem_slot = self.get_slot(*elem)?;
                    self.encoder.emit_opcode(opcodes::PUSH);
                    self.encoder.emit_u16(elem_slot);
                }

                self.encoder.emit_opcode(opcodes::TUPLE_LIT);
                self.encoder.emit_u16(dest_slot);
                self.encoder.emit_u16(elements.len() as u16);
            }

            MirInst::IndexGet {
                dest,
                collection,
                index,
            } => {
                let dest_slot = self.alloc_slot(*dest)?;
                let coll_slot = self.get_slot(*collection)?;
                let idx_slot = self.get_slot(*index)?;
                self.encoder.emit_opcode(opcodes::INDEX_GET);
                self.encoder.emit_u16(dest_slot);
                self.encoder.emit_u16(coll_slot);
                self.encoder.emit_u16(idx_slot);
            }

            MirInst::IndexSet {
                collection,
                index,
                value,
            } => {
                let coll_slot = self.get_slot(*collection)?;
                let idx_slot = self.get_slot(*index)?;
                let val_slot = self.get_slot(*value)?;
                self.encoder.emit_opcode(opcodes::INDEX_SET);
                self.encoder.emit_u16(coll_slot);
                self.encoder.emit_u16(idx_slot);
                self.encoder.emit_u16(val_slot);
            }

            // =================================================================
            // No-ops (safe to skip in bytecode)
            // =================================================================
            MirInst::Drop { .. } | MirInst::EndScope { .. } => {
                // No-op in bytecode (GC handles cleanup)
            }

            // =================================================================
            // Unsupported (Phase 2+)
            // =================================================================
            other => {
                return Err(CompileError::UnsupportedInstruction(format!("{:?}", other)));
            }
        }

        Ok(())
    }

    /// Compile a block terminator.
    fn compile_terminator(&mut self, terminator: &Terminator) -> Result<(), CompileError> {
        match terminator {
            Terminator::Return(Some(vreg)) => {
                let slot = self.get_slot(*vreg)?;
                self.encoder.emit_opcode(opcodes::RET);
                self.encoder.emit_u16(slot);
            }

            Terminator::Return(None) => {
                self.encoder.emit_opcode(opcodes::RET_VOID);
            }

            Terminator::Jump(target) => {
                self.encoder.emit_opcode(opcodes::JMP);
                self.record_jump_fixup(*target);
            }

            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond_slot = self.get_slot(*cond)?;

                // Push condition and branch
                self.encoder.emit_opcode(opcodes::PUSH);
                self.encoder.emit_u16(cond_slot);

                // JMP_IF to then_block
                self.encoder.emit_opcode(opcodes::JMP_IF);
                self.record_jump_fixup(*then_block);

                // Fall through to JMP to else_block
                self.encoder.emit_opcode(opcodes::JMP);
                self.record_jump_fixup(*else_block);
            }

            Terminator::Unreachable => {
                // Emit a trap or return nil
                self.encoder.emit_opcode(opcodes::RET_VOID);
            }
        }

        Ok(())
    }
}

impl Default for BytecodeCompiler {
    fn default() -> Self {
        Self::new()
    }
}

/// Compile a single MIR function to bytecode.
///
/// Convenience function for simple use cases.
pub fn compile_function(func: &MirFunction) -> Result<CompiledFunction, CompileError> {
    let mut compiler = BytecodeCompiler::new();
    compiler.compile_function(func)
}
