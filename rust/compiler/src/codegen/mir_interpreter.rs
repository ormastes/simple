//! MIR-walking interpreter backend implementing `CodegenEmitter`.
//!
//! Unlike the existing tree-walking interpreter (AST-based), this interpreter
//! operates on MIR instructions directly, using `CodegenEmitter` as its interface.
//! Values are represented as `i64` (tagged RuntimeValue format).
//!
//! This enables running MIR without native code generation — useful for:
//! - Debugging codegen issues (compare interpreter vs native results)
//! - Portable execution (no Cranelift/LLVM needed)
//! - Testing the `CodegenEmitter` trait with a simple backend

use std::collections::HashMap;

use crate::hir::{BinOp, NeighborDirection, PointerKind, TypeId, UnaryOp};
use crate::mir::{
    BlockId, CallTarget, ContractKind, Effect, FStringPart, GpuAtomicOp, GpuMemoryScope, MirPattern,
    ParallelBackend, PatternBinding, UnitOverflowBehavior, VReg,
};

use super::emitter_trait::CodegenEmitter;

/// Error type for the MIR interpreter.
#[derive(Debug, Clone)]
pub struct InterpError(pub String);

impl From<String> for InterpError {
    fn from(s: String) -> Self {
        InterpError(s)
    }
}

impl std::fmt::Display for InterpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "InterpError: {}", self.0)
    }
}

impl std::error::Error for InterpError {}

/// MIR interpreter emitter. Evaluates MIR instructions directly using
/// a value map (VReg → i64). Pure operations are computed inline;
/// runtime-dependent operations (collections, FFI) return stub values.
pub struct MirInterpreterEmitter {
    /// Map from virtual register to computed value
    pub values: HashMap<VReg, i64>,
    /// Map from global name to value
    pub globals: HashMap<String, i64>,
    /// Local variable storage (index → value)
    pub locals: Vec<i64>,
}

impl MirInterpreterEmitter {
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
            globals: HashMap::new(),
            locals: Vec::new(),
        }
    }

    fn set(&mut self, dest: VReg, value: i64) {
        self.values.insert(dest, value);
    }

    pub fn get(&self, vreg: VReg) -> i64 {
        self.values.get(&vreg).copied().unwrap_or(0)
    }

    /// Ensure locals has at least `n` slots
    fn ensure_local(&mut self, index: usize) {
        while self.locals.len() <= index {
            self.locals.push(0);
        }
    }
}

impl CodegenEmitter for MirInterpreterEmitter {
    type Value = i64;
    type Error = InterpError;

    // =========================================================================
    // Constants
    // =========================================================================
    fn emit_const_int(&mut self, dest: VReg, value: i64) -> Result<(), Self::Error> {
        self.set(dest, value);
        Ok(())
    }
    fn emit_const_float(&mut self, dest: VReg, value: f64) -> Result<(), Self::Error> {
        self.set(dest, value.to_bits() as i64);
        Ok(())
    }
    fn emit_const_bool(&mut self, dest: VReg, value: bool) -> Result<(), Self::Error> {
        self.set(dest, value as i64);
        Ok(())
    }
    fn emit_const_string(&mut self, dest: VReg, _value: &str) -> Result<(), Self::Error> {
        // Stub: strings need runtime allocation; return placeholder
        self.set(dest, 0);
        Ok(())
    }
    fn emit_const_symbol(&mut self, dest: VReg, _value: &str) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // Basic operations
    // =========================================================================
    fn emit_copy(&mut self, dest: VReg, src: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(src));
        Ok(())
    }
    fn emit_binop(&mut self, dest: VReg, op: BinOp, left: VReg, right: VReg) -> Result<(), Self::Error> {
        let l = self.get(left);
        let r = self.get(right);
        let result = match op {
            BinOp::Add => l.wrapping_add(r),
            BinOp::Sub => l.wrapping_sub(r),
            BinOp::Mul => l.wrapping_mul(r),
            BinOp::Div => {
                if r == 0 {
                    return Err(InterpError("division by zero".into()));
                }
                l.wrapping_div(r)
            }
            BinOp::Mod => {
                if r == 0 {
                    return Err(InterpError("modulo by zero".into()));
                }
                l.wrapping_rem(r)
            }
            BinOp::Eq => (l == r) as i64,
            BinOp::NotEq => (l != r) as i64,
            BinOp::Lt => (l < r) as i64,
            BinOp::LtEq => (l <= r) as i64,
            BinOp::Gt => (l > r) as i64,
            BinOp::GtEq => (l >= r) as i64,
            BinOp::And => l & r,
            BinOp::Or => l | r,
            BinOp::BitAnd => l & r,
            BinOp::BitOr => l | r,
            BinOp::BitXor => l ^ r,
            BinOp::ShiftLeft => l.wrapping_shl(r as u32),
            BinOp::ShiftRight => l.wrapping_shr(r as u32),
            _ => {
                return Err(InterpError(format!("unsupported binop: {:?}", op)));
            }
        };
        self.set(dest, result);
        Ok(())
    }
    fn emit_unary_op(&mut self, dest: VReg, op: UnaryOp, operand: VReg) -> Result<(), Self::Error> {
        let v = self.get(operand);
        let result = match op {
            UnaryOp::Neg => -v,
            UnaryOp::Not => (v == 0) as i64,
            UnaryOp::BitNot => !v,
            _ => return Err(InterpError(format!("unsupported unary op: {:?}", op))),
        };
        self.set(dest, result);
        Ok(())
    }
    fn emit_cast(&mut self, dest: VReg, source: VReg, from_ty: TypeId, to_ty: TypeId) -> Result<(), Self::Error> {
        let v = self.get(source);
        let result = match (from_ty, to_ty) {
            (TypeId::I64, TypeId::F64) => {
                let f = v as f64;
                f.to_bits() as i64
            }
            (TypeId::F64, TypeId::I64) => {
                let f = f64::from_bits(v as u64);
                f as i64
            }
            _ => v, // Identity or unsupported cast
        };
        self.set(dest, result);
        Ok(())
    }
    fn emit_spread(&mut self, dest: VReg, source: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(source));
        Ok(())
    }

    // =========================================================================
    // Memory
    // =========================================================================
    fn emit_load(&mut self, dest: VReg, addr: VReg) -> Result<(), Self::Error> {
        // Stub: interpret addr as local index
        let idx = self.get(addr) as usize;
        let val = self.locals.get(idx).copied().unwrap_or(0);
        self.set(dest, val);
        Ok(())
    }
    fn emit_store(&mut self, addr: VReg, value: VReg) -> Result<(), Self::Error> {
        let idx = self.get(addr) as usize;
        self.ensure_local(idx);
        self.locals[idx] = self.get(value);
        Ok(())
    }
    fn emit_global_load(&mut self, dest: VReg, global_name: &str, _ty: TypeId) -> Result<(), Self::Error> {
        let val = self.globals.get(global_name).copied().unwrap_or(0);
        self.set(dest, val);
        Ok(())
    }
    fn emit_global_store(&mut self, global_name: &str, value: VReg, _ty: TypeId) -> Result<(), Self::Error> {
        self.globals.insert(global_name.to_string(), self.get(value));
        Ok(())
    }
    fn emit_local_addr(&mut self, dest: VReg, local_index: usize) -> Result<(), Self::Error> {
        self.ensure_local(local_index);
        self.set(dest, local_index as i64);
        Ok(())
    }
    fn emit_get_element_ptr(&mut self, dest: VReg, base: VReg, index: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(base).wrapping_add(self.get(index) * 8));
        Ok(())
    }
    fn emit_gc_alloc(&mut self, dest: VReg, _ty: TypeId) -> Result<(), Self::Error> {
        self.set(dest, 0); // Stub
        Ok(())
    }
    fn emit_wait(&mut self, dest: Option<VReg>, _target: VReg) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(d, 0);
        }
        Ok(())
    }

    // =========================================================================
    // Calls
    // =========================================================================
    fn emit_call(&mut self, dest: &Option<VReg>, _target: &CallTarget, _args: &[VReg]) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0); // Stub: can't execute arbitrary functions
        }
        Ok(())
    }
    fn emit_interp_call(&mut self, dest: &Option<VReg>, _func_name: &str, _args: &[VReg]) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0);
        }
        Ok(())
    }
    fn emit_interp_eval(&mut self, dest: VReg, _expr_index: usize) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_indirect_call(
        &mut self,
        dest: &Option<VReg>,
        _callee: VReg,
        _param_types: &[TypeId],
        _return_type: TypeId,
        _args: &[VReg],
        _effect: Effect,
    ) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0);
        }
        Ok(())
    }

    // =========================================================================
    // Collections (stubs — need runtime)
    // =========================================================================
    fn emit_array_lit(&mut self, dest: VReg, _elements: &[VReg]) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_tuple_lit(&mut self, dest: VReg, _elements: &[VReg]) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_lit(&mut self, dest: VReg, _elements: &[VReg]) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_dict_lit(&mut self, dest: VReg, _keys: &[VReg], _values: &[VReg]) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_index_get(&mut self, dest: VReg, _collection: VReg, _index: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_index_set(&mut self, _collection: VReg, _index: VReg, _value: VReg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_slice_op(
        &mut self,
        dest: VReg,
        _collection: VReg,
        _start: Option<VReg>,
        _end: Option<VReg>,
        _step: Option<VReg>,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_fstring_format(&mut self, dest: VReg, _parts: &[FStringPart]) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // SIMD (stubs)
    // =========================================================================
    fn emit_vec_reduction(&mut self, dest: VReg, _source: VReg, _op: &str) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_extract(&mut self, dest: VReg, _vector: VReg, _index: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_with(&mut self, dest: VReg, _vector: VReg, _index: VReg, _value: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_math(&mut self, dest: VReg, _source: VReg, _op: &str) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_shuffle(&mut self, dest: VReg, _source: VReg, _indices: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_blend(&mut self, dest: VReg, _first: VReg, _second: VReg, _indices: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_select(
        &mut self,
        dest: VReg,
        _mask: VReg,
        _if_true: VReg,
        _if_false: VReg,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_load(&mut self, dest: VReg, _array: VReg, _offset: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_store(&mut self, _source: VReg, _array: VReg, _offset: VReg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_vec_gather(&mut self, dest: VReg, _array: VReg, _indices: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_scatter(&mut self, _source: VReg, _array: VReg, _indices: VReg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_vec_fma(&mut self, dest: VReg, _a: VReg, _b: VReg, _c: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_recip(&mut self, dest: VReg, _source: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_masked_load(
        &mut self,
        dest: VReg,
        _array: VReg,
        _offset: VReg,
        _mask: VReg,
        _default: VReg,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_masked_store(
        &mut self,
        _source: VReg,
        _array: VReg,
        _offset: VReg,
        _mask: VReg,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_vec_min_vec(&mut self, dest: VReg, _a: VReg, _b: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_max_vec(&mut self, dest: VReg, _a: VReg, _b: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_vec_clamp(&mut self, dest: VReg, _source: VReg, _lo: VReg, _hi: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_neighbor_load(
        &mut self,
        dest: VReg,
        _array: VReg,
        _direction: NeighborDirection,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // Structs / Fields
    // =========================================================================
    fn emit_struct_init(
        &mut self,
        dest: VReg,
        _struct_size: usize,
        _field_offsets: &[u32],
        _field_types: &[TypeId],
        _field_values: &[VReg],
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_field_get(
        &mut self,
        dest: VReg,
        _object: VReg,
        _byte_offset: usize,
        _field_type: TypeId,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_field_set(
        &mut self,
        _object: VReg,
        _byte_offset: usize,
        _field_type: TypeId,
        _value: VReg,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    // =========================================================================
    // Closures
    // =========================================================================
    fn emit_closure_create(
        &mut self,
        dest: VReg,
        _func_name: &str,
        _closure_size: usize,
        _capture_offsets: &[u32],
        _captures: &[VReg],
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // Methods
    // =========================================================================
    fn emit_method_call_static(
        &mut self,
        dest: &Option<VReg>,
        _receiver: VReg,
        _func_name: &str,
        _args: &[VReg],
    ) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0);
        }
        Ok(())
    }
    fn emit_method_call_virtual(
        &mut self,
        dest: &Option<VReg>,
        _receiver: VReg,
        _vtable_slot: usize,
        _param_types: &[TypeId],
        _return_type: TypeId,
        _args: &[VReg],
    ) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0);
        }
        Ok(())
    }
    fn emit_builtin_method(
        &mut self,
        dest: &Option<VReg>,
        _receiver: VReg,
        _receiver_type: &str,
        _method: &str,
        _args: &[VReg],
    ) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0);
        }
        Ok(())
    }
    fn emit_extern_method_call(
        &mut self,
        dest: &Option<VReg>,
        _receiver: Option<VReg>,
        _class_name: &str,
        _method_name: &str,
        _is_static: bool,
        _args: &[VReg],
    ) -> Result<(), Self::Error> {
        if let Some(d) = dest {
            self.set(*d, 0);
        }
        Ok(())
    }

    // =========================================================================
    // Pattern matching
    // =========================================================================
    fn emit_pattern_test(&mut self, dest: VReg, _subject: VReg, _pattern: &MirPattern) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_pattern_bind(&mut self, dest: VReg, subject: VReg, _binding: &PatternBinding) -> Result<(), Self::Error> {
        self.set(dest, self.get(subject));
        Ok(())
    }

    // =========================================================================
    // Enums / Unions
    // =========================================================================
    fn emit_enum_discriminant(&mut self, dest: VReg, _value: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_enum_payload(&mut self, dest: VReg, _value: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_enum_unit(&mut self, dest: VReg, _variant_name: &str) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_enum_with(&mut self, dest: VReg, _variant_name: &str, _payload: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_union_discriminant(&mut self, dest: VReg, _value: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_union_payload(&mut self, dest: VReg, _value: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_union_wrap(&mut self, dest: VReg, _value: VReg, _type_index: u32) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // Async / Concurrency (stubs)
    // =========================================================================
    fn emit_future_create(&mut self, dest: VReg, _body_block: BlockId) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_await(&mut self, dest: VReg, _future: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_actor_spawn(&mut self, dest: VReg, _body_block: BlockId) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_actor_send(&mut self, _actor: VReg, _message: VReg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_actor_recv(&mut self, dest: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_actor_join(&mut self, dest: VReg, _actor: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_actor_reply(&mut self, _message: VReg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_generator_create(&mut self, dest: VReg, _body_block: BlockId) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_yield(&mut self, _value: VReg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_generator_next(&mut self, dest: VReg, _generator: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // Result / Option
    // =========================================================================
    fn emit_try_unwrap(
        &mut self,
        dest: VReg,
        _value: VReg,
        _error_block: BlockId,
        _error_dest: VReg,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_option_some(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        // Tag: (value << 1) | 1 (Some flag)
        self.set(dest, (self.get(value) << 1) | 1);
        Ok(())
    }
    fn emit_option_none(&mut self, dest: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_result_ok(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        self.set(dest, (self.get(value) << 1) | 1);
        Ok(())
    }
    fn emit_result_err(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(value) << 1);
        Ok(())
    }

    // =========================================================================
    // Contracts
    // =========================================================================
    fn emit_contract_check(
        &mut self,
        condition: VReg,
        kind: ContractKind,
        func_name: &str,
        message: Option<&str>,
    ) -> Result<(), Self::Error> {
        if self.get(condition) == 0 {
            let msg = message.unwrap_or("contract violation");
            return Err(InterpError(format!("{:?} failed in {}: {}", kind, func_name, msg)));
        }
        Ok(())
    }
    fn emit_contract_old_capture(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(value));
        Ok(())
    }

    // =========================================================================
    // Coverage (no-ops in interpreter)
    // =========================================================================
    fn emit_decision_probe(
        &mut self,
        _result: VReg,
        _decision_id: u32,
        _file: &str,
        _line: u32,
        _column: u32,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_condition_probe(
        &mut self,
        _decision_id: u32,
        _condition_id: u32,
        _result: VReg,
        _file: &str,
        _line: u32,
        _column: u32,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_path_probe(&mut self, _path_id: u32, _block_id: u32) -> Result<(), Self::Error> {
        Ok(())
    }

    // =========================================================================
    // Units
    // =========================================================================
    fn emit_unit_bound_check(
        &mut self,
        value: VReg,
        unit_name: &str,
        min: i64,
        max: i64,
        _overflow: UnitOverflowBehavior,
    ) -> Result<(), Self::Error> {
        let v = self.get(value);
        if v < min || v > max {
            return Err(InterpError(format!(
                "unit {} value {} out of bounds [{}, {}]",
                unit_name, v, min, max
            )));
        }
        Ok(())
    }
    fn emit_unit_widen(
        &mut self,
        dest: VReg,
        value: VReg,
        _from_bits: u8,
        _to_bits: u8,
        _signed: bool,
    ) -> Result<(), Self::Error> {
        self.set(dest, self.get(value));
        Ok(())
    }
    fn emit_unit_narrow(
        &mut self,
        dest: VReg,
        value: VReg,
        _from_bits: u8,
        _to_bits: u8,
        _signed: bool,
        _overflow: UnitOverflowBehavior,
    ) -> Result<(), Self::Error> {
        self.set(dest, self.get(value));
        Ok(())
    }
    fn emit_unit_saturate(&mut self, dest: VReg, value: VReg, min: i64, max: i64) -> Result<(), Self::Error> {
        let v = self.get(value);
        self.set(dest, v.clamp(min, max));
        Ok(())
    }

    // =========================================================================
    // Pointers
    // =========================================================================
    fn emit_pointer_new(&mut self, dest: VReg, _kind: PointerKind, value: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(value));
        Ok(())
    }
    fn emit_pointer_ref(&mut self, dest: VReg, _kind: PointerKind, source: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(source));
        Ok(())
    }
    fn emit_pointer_deref(&mut self, dest: VReg, pointer: VReg, _kind: PointerKind) -> Result<(), Self::Error> {
        self.set(dest, self.get(pointer));
        Ok(())
    }

    // =========================================================================
    // Boxing
    // =========================================================================
    fn emit_box_int(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        // RuntimeValue tag: (value << 3) | TAG_INT(0)
        self.set(dest, self.get(value) << 3);
        Ok(())
    }
    fn emit_box_float(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        // RuntimeValue tag: (bits >> 3) << 3 | TAG_FLOAT(2)
        let bits = self.get(value) as u64;
        self.set(dest, (((bits >> 3) << 3) | 2) as i64);
        Ok(())
    }
    fn emit_unbox_int(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        self.set(dest, self.get(value) >> 3);
        Ok(())
    }
    fn emit_unbox_float(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error> {
        let v = self.get(value) as u64;
        self.set(dest, ((v >> 3) << 3) as i64);
        Ok(())
    }

    // =========================================================================
    // GPU (stubs)
    // =========================================================================
    fn emit_gpu_global_id(&mut self, dest: VReg, _dim: u8) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_local_id(&mut self, dest: VReg, _dim: u8) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_group_id(&mut self, dest: VReg, _dim: u8) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_global_size(&mut self, dest: VReg, _dim: u8) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_local_size(&mut self, dest: VReg, _dim: u8) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_num_groups(&mut self, dest: VReg, _dim: u8) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_barrier(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_gpu_mem_fence(&mut self, _scope: GpuMemoryScope) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_gpu_shared_alloc(&mut self, dest: VReg, _element_type: TypeId, _size: u32) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_atomic(&mut self, dest: VReg, _op: GpuAtomicOp, _ptr: VReg, _value: VReg) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_gpu_atomic_cmpxchg(
        &mut self,
        dest: VReg,
        _ptr: VReg,
        _expected: VReg,
        _desired: VReg,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }

    // =========================================================================
    // Parallel (stubs)
    // =========================================================================
    fn emit_par_map(
        &mut self,
        dest: VReg,
        _input: VReg,
        _closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_par_reduce(
        &mut self,
        dest: VReg,
        _input: VReg,
        _initial: VReg,
        _closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_par_filter(
        &mut self,
        dest: VReg,
        _input: VReg,
        _predicate: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error> {
        self.set(dest, 0);
        Ok(())
    }
    fn emit_par_for_each(
        &mut self,
        _input: VReg,
        _closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::{MirInst, VReg};
    use crate::codegen::dispatch::dispatch_instruction;

    #[test]
    fn interp_const_int() {
        let mut e = MirInterpreterEmitter::new();
        let dest = VReg(0);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest, value: 42 }).unwrap();
        assert_eq!(e.get(dest), 42);
    }

    #[test]
    fn interp_binop_add() {
        let mut e = MirInterpreterEmitter::new();
        let a = VReg(0);
        let b = VReg(1);
        let dest = VReg(2);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: a, value: 10 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: b, value: 32 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::BinOp { dest, op: BinOp::Add, left: a, right: b }).unwrap();
        assert_eq!(e.get(dest), 42);
    }

    #[test]
    fn interp_copy() {
        let mut e = MirInterpreterEmitter::new();
        let src = VReg(0);
        let dest = VReg(1);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: src, value: 99 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::Copy { dest, src }).unwrap();
        assert_eq!(e.get(dest), 99);
    }

    #[test]
    fn interp_unary_neg() {
        let mut e = MirInterpreterEmitter::new();
        let src = VReg(0);
        let dest = VReg(1);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: src, value: 42 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::UnaryOp { dest, op: UnaryOp::Neg, operand: src }).unwrap();
        assert_eq!(e.get(dest), -42);
    }

    #[test]
    fn interp_unit_saturate() {
        let mut e = MirInterpreterEmitter::new();
        let src = VReg(0);
        let dest = VReg(1);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: src, value: 300 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::UnitSaturate { dest, value: src, min: 0, max: 255 }).unwrap();
        assert_eq!(e.get(dest), 255);
    }

    #[test]
    fn interp_box_unbox_int() {
        let mut e = MirInterpreterEmitter::new();
        let val = VReg(0);
        let boxed = VReg(1);
        let unboxed = VReg(2);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: val, value: 42 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::BoxInt { dest: boxed, value: val }).unwrap();
        dispatch_instruction(&mut e, &MirInst::UnboxInt { dest: unboxed, value: boxed }).unwrap();
        assert_eq!(e.get(unboxed), 42);
    }

    #[test]
    fn interp_global_store_load() {
        let mut e = MirInterpreterEmitter::new();
        let val = VReg(0);
        let loaded = VReg(1);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: val, value: 42 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::GlobalStore { global_name: "g".to_string(), value: val, ty: TypeId::I64 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::GlobalLoad { dest: loaded, global_name: "g".to_string(), ty: TypeId::I64 }).unwrap();
        assert_eq!(e.get(loaded), 42);
    }

    #[test]
    fn interp_contract_check_passes() {
        let mut e = MirInterpreterEmitter::new();
        let cond = VReg(0);
        dispatch_instruction(&mut e, &MirInst::ConstBool { dest: cond, value: true }).unwrap();
        dispatch_instruction(
            &mut e,
            &MirInst::ContractCheck {
                condition: cond,
                kind: ContractKind::Precondition,
                func_name: "test".to_string(),
                message: None,
            },
        )
        .unwrap();
    }

    #[test]
    fn interp_contract_check_fails() {
        let mut e = MirInterpreterEmitter::new();
        let cond = VReg(0);
        dispatch_instruction(&mut e, &MirInst::ConstBool { dest: cond, value: false }).unwrap();
        let result = dispatch_instruction(
            &mut e,
            &MirInst::ContractCheck {
                condition: cond,
                kind: ContractKind::Precondition,
                func_name: "test".to_string(),
                message: Some("must be true".to_string()),
            },
        );
        assert!(result.is_err());
    }

    #[test]
    fn interp_division_by_zero() {
        let mut e = MirInterpreterEmitter::new();
        let a = VReg(0);
        let b = VReg(1);
        let dest = VReg(2);
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: a, value: 42 }).unwrap();
        dispatch_instruction(&mut e, &MirInst::ConstInt { dest: b, value: 0 }).unwrap();
        let result = dispatch_instruction(&mut e, &MirInst::BinOp { dest, op: BinOp::Div, left: a, right: b });
        assert!(result.is_err());
    }
}
