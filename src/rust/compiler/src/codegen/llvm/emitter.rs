//! LLVM implementation of the `CodegenEmitter` trait.
//!
//! This module provides an LLVM-based emitter that wraps the existing
//! `LlvmBackend` and delegates to functions in `llvm/instructions.rs`
//! and `llvm/functions/`.

#[cfg(feature = "llvm")]
use std::collections::HashMap;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, PointerValue};

#[cfg(feature = "llvm")]
use crate::codegen::emitter_trait::CodegenEmitter;
#[cfg(feature = "llvm")]
use crate::hir::{BinOp, NeighborDirection, PointerKind, TypeId, UnaryOp};
#[cfg(feature = "llvm")]
use crate::mir::{
    BlockId, CallTarget, ContractKind, Effect, FStringPart, GpuAtomicOp, GpuMemoryScope,
    MirPattern, ParallelBackend, PatternBinding, UnitOverflowBehavior, VReg,
};

#[cfg(feature = "llvm")]
use super::LlvmBackend;

/// Type alias for vreg map
#[cfg(feature = "llvm")]
pub type VRegMap = HashMap<VReg, BasicValueEnum<'static>>;

/// LLVM-based emitter wrapping existing `LlvmBackend` infrastructure.
///
/// This struct holds references to the LLVM compilation context
/// and delegates each trait method to the corresponding helper
/// on `LlvmBackend` or generates inline LLVM IR via runtime calls.
#[cfg(feature = "llvm")]
pub struct LlvmEmitter<'a> {
    pub backend: &'a LlvmBackend,
    pub vreg_map: &'a mut VRegMap,
    pub local_allocas: &'a HashMap<usize, PointerValue<'static>>,
    pub builder: &'a Builder<'static>,
    pub module: &'a Module<'static>,
}

#[cfg(feature = "llvm")]
impl LlvmEmitter<'_> {
    /// Look up a vreg value from the map.
    fn get(&self, vreg: VReg) -> Result<BasicValueEnum<'static>, String> {
        self.vreg_map
            .get(&vreg)
            .copied()
            .ok_or_else(|| format!("LLVM emitter: vreg {:?} not found", vreg))
    }

    /// Store a value in the vreg map.
    fn set(&mut self, dest: VReg, val: BasicValueEnum<'static>) {
        self.vreg_map.insert(dest, val);
    }

    /// Call a runtime function by name and return its result.
    fn call_runtime(
        &self,
        name: &str,
        args: &[BasicValueEnum<'static>],
    ) -> Result<BasicValueEnum<'static>, String> {
        let i64_type = self.backend.context.i64_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());

        let func = self.module.get_function(name).unwrap_or_else(|| {
            // Auto-declare: assume all runtime functions take i64 args and return i64
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            self.module.add_function(name, fn_type, None)
        });

        let call_args: Vec<BasicMetadataValueEnum> = args.iter().map(|a| (*a).into()).collect();
        let result = self
            .builder
            .build_call(func, &call_args, name)
            .map_err(|e| format!("LLVM call to '{}' failed: {}", name, e))?;
        result
            .try_as_basic_value()
            .left()
            .ok_or_else(|| format!("'{}' did not return a value", name))
    }

    /// Call a runtime function that returns void.
    fn call_runtime_void(
        &self,
        name: &str,
        args: &[BasicValueEnum<'static>],
    ) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();

        let func = self.module.get_function(name).unwrap_or_else(|| {
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = self
                .backend
                .context
                .void_type()
                .fn_type(&param_types, false);
            self.module.add_function(name, fn_type, None)
        });

        let call_args: Vec<BasicMetadataValueEnum> = args.iter().map(|a| (*a).into()).collect();
        self.builder
            .build_call(func, &call_args, name)
            .map_err(|e| format!("LLVM call to '{}' failed: {}", name, e))?;
        Ok(())
    }

    /// Helper to create an i64 constant.
    fn i64_const(&self, value: i64) -> BasicValueEnum<'static> {
        self.backend
            .context
            .i64_type()
            .const_int(value as u64, true)
            .into()
    }

    /// Helper to create an i32 constant.
    fn i32_const(&self, value: i32) -> BasicValueEnum<'static> {
        self.backend
            .context
            .i32_type()
            .const_int(value as u64, true)
            .into()
    }
}

#[cfg(feature = "llvm")]
impl CodegenEmitter for LlvmEmitter<'_> {
    type Value = BasicValueEnum<'static>;
    type Error = String;

    // =========================================================================
    // Constants
    // =========================================================================
    fn emit_const_int(&mut self, dest: VReg, value: i64) -> Result<(), String> {
        let val = self
            .backend
            .context
            .i64_type()
            .const_int(value as u64, true);
        self.set(dest, val.into());
        Ok(())
    }

    fn emit_const_float(&mut self, dest: VReg, value: f64) -> Result<(), String> {
        let val = self.backend.context.f64_type().const_float(value);
        self.set(dest, val.into());
        Ok(())
    }

    fn emit_const_bool(&mut self, dest: VReg, value: bool) -> Result<(), String> {
        let val = self
            .backend
            .context
            .bool_type()
            .const_int(value as u64, false);
        self.set(dest, val.into());
        Ok(())
    }

    fn emit_const_string(&mut self, dest: VReg, value: &str) -> Result<(), String> {
        let str_val = self.backend.context.const_string(value.as_bytes(), false);
        let global = self.module.add_global(str_val.get_type(), None, "str");
        global.set_initializer(&str_val);
        global.set_constant(true);
        self.set(dest, global.as_pointer_value().into());
        Ok(())
    }

    fn emit_const_symbol(&mut self, dest: VReg, value: &str) -> Result<(), String> {
        let str_val = self.backend.context.const_string(value.as_bytes(), false);
        let global = self
            .module
            .add_global(str_val.get_type(), None, &format!("sym_{}", value));
        global.set_initializer(&str_val);
        global.set_constant(true);
        self.set(dest, global.as_pointer_value().into());
        Ok(())
    }

    // =========================================================================
    // Basic operations
    // =========================================================================
    fn emit_copy(&mut self, dest: VReg, src: VReg) -> Result<(), String> {
        if let Some(val) = self.vreg_map.get(&src).copied() {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_binop(&mut self, dest: VReg, op: BinOp, left: VReg, right: VReg) -> Result<(), String> {
        let lhs = self.get(left)?;
        let rhs = self.get(right)?;
        let result = self
            .backend
            .compile_binop(op, lhs, rhs, self.builder)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_unary_op(&mut self, dest: VReg, op: UnaryOp, operand: VReg) -> Result<(), String> {
        let val = self.get(operand)?;
        let result = self
            .backend
            .compile_unaryop(op, val, self.builder)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_cast(&mut self, dest: VReg, source: VReg, from_ty: TypeId, to_ty: TypeId) -> Result<(), String> {
        let source_val = self.get(source)?;
        let result = self
            .backend
            .compile_cast(source_val, &from_ty, &to_ty, self.builder)
            .map_err(|e: crate::error::CompileError| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_spread(&mut self, dest: VReg, source: VReg) -> Result<(), String> {
        // Spread is a copy at the LLVM level
        if let Some(val) = self.vreg_map.get(&source).copied() {
            self.set(dest, val);
        }
        Ok(())
    }

    // =========================================================================
    // Memory
    // =========================================================================
    fn emit_load(&mut self, dest: VReg, addr: VReg) -> Result<(), String> {
        let addr_val = self.get(addr)?;
        if let BasicValueEnum::PointerValue(ptr) = addr_val {
            let i64_type = self.backend.context.i64_type();
            let loaded = self
                .builder
                .build_load(i64_type, ptr, "load")
                .map_err(|e| format!("LLVM load failed: {}", e))?;
            self.set(dest, loaded);
        } else {
            return Err("Load requires pointer value".to_string());
        }
        Ok(())
    }

    fn emit_store(&mut self, addr: VReg, value: VReg) -> Result<(), String> {
        let addr_val = self.get(addr)?;
        let val = self.get(value)?;
        if let BasicValueEnum::PointerValue(ptr) = addr_val {
            self.builder
                .build_store(ptr, val)
                .map_err(|e| format!("LLVM store failed: {}", e))?;
        } else {
            return Err("Store requires pointer value".to_string());
        }
        Ok(())
    }

    fn emit_global_load(&mut self, dest: VReg, global_name: &str, ty: TypeId) -> Result<(), String> {
        let global = self
            .module
            .get_global(global_name)
            .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
        let llvm_ty = self
            .backend
            .llvm_type(&ty)
            .map_err(|e| e.to_string())?;
        let loaded = self
            .builder
            .build_load(llvm_ty, global.as_pointer_value(), "global_load")
            .map_err(|e| format!("LLVM global load failed: {}", e))?;
        self.set(dest, loaded);
        Ok(())
    }

    fn emit_global_store(&mut self, global_name: &str, value: VReg, _ty: TypeId) -> Result<(), String> {
        let global = self
            .module
            .get_global(global_name)
            .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
        let val = self.get(value)?;
        self.builder
            .build_store(global.as_pointer_value(), val)
            .map_err(|e| format!("LLVM global store failed: {}", e))?;
        Ok(())
    }

    fn emit_local_addr(&mut self, dest: VReg, local_index: usize) -> Result<(), String> {
        let alloca = self
            .local_allocas
            .get(&local_index)
            .ok_or_else(|| format!("Local index {} not found", local_index))?;
        self.set(dest, (*alloca).into());
        Ok(())
    }

    fn emit_get_element_ptr(&mut self, dest: VReg, base: VReg, index: VReg) -> Result<(), String> {
        let base_val = self.get(base)?;
        let idx_val = self.get(index)?;
        if let (BasicValueEnum::PointerValue(ptr), BasicValueEnum::IntValue(idx)) =
            (base_val, idx_val)
        {
            let i8_type = self.backend.context.i8_type();
            let gep = unsafe {
                self.builder
                    .build_gep(i8_type, ptr, &[idx], "gep")
                    .map_err(|e| format!("LLVM GEP failed: {}", e))?
            };
            self.set(dest, gep.into());
        } else {
            return Err("GEP requires pointer base and integer index".to_string());
        }
        Ok(())
    }

    fn emit_gc_alloc(&mut self, dest: VReg, ty: TypeId) -> Result<(), String> {
        let llvm_ty = self.backend.llvm_type(&ty).map_err(|e| e.to_string())?;
        let alloc = self
            .builder
            .build_alloca(llvm_ty, "gc_alloc")
            .map_err(|e| format!("LLVM alloca failed: {}", e))?;
        self.set(dest, alloc.into());
        Ok(())
    }

    fn emit_wait(&mut self, dest: Option<VReg>, target: VReg) -> Result<(), String> {
        let target_val = self.get(target)?;
        let result = self.call_runtime("rt_wait", &[target_val])?;
        if let Some(d) = dest {
            self.set(d, result);
        }
        Ok(())
    }

    // =========================================================================
    // Calls
    // =========================================================================
    fn emit_call(&mut self, dest: &Option<VReg>, target: &CallTarget, args: &[VReg]) -> Result<(), String> {
        let func_name = target.name();
        let i64_type = self.backend.context.i64_type();

        let called_func = self.module.get_function(func_name).unwrap_or_else(|| {
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            self.module.add_function(func_name, fn_type, None)
        });

        let mut arg_vals: Vec<BasicMetadataValueEnum> = Vec::new();
        for arg in args {
            let val = self.get(*arg)?;
            arg_vals.push(val.into());
        }

        let call_site = self
            .builder
            .build_call(called_func, &arg_vals, "call")
            .map_err(|e| format!("LLVM call failed: {}", e))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                self.set(*d, ret_val);
            }
        }
        Ok(())
    }

    fn emit_interp_call(
        &mut self,
        dest: &Option<VReg>,
        func_name: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());

        let interp_call = self.module.get_function("rt_interp_call").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i8_ptr_type.into()],
                false,
            );
            self.module.add_function("rt_interp_call", fn_type, None)
        });

        let name_bytes = func_name.as_bytes();
        let name_const = self.backend.context.const_string(name_bytes, false);
        let name_global = self.module.add_global(name_const.get_type(), None, "func_name");
        name_global.set_initializer(&name_const);
        name_global.set_constant(true);
        let name_ptr = name_global.as_pointer_value();
        let name_len = i64_type.const_int(name_bytes.len() as u64, false);
        let argc = i64_type.const_int(args.len() as u64, false);
        let argv = i8_ptr_type.const_null();

        let call_args = [name_ptr.into(), name_len.into(), argc.into(), argv.into()];
        let call_site = self
            .builder
            .build_call(interp_call, &call_args, "interp_call")
            .map_err(|e| format!("LLVM interp_call failed: {}", e))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                self.set(*d, ret_val);
            }
        }
        Ok(())
    }

    fn emit_interp_eval(&mut self, dest: VReg, expr_index: usize) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();

        let interp_eval = self.module.get_function("rt_interp_eval").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            self.module.add_function("rt_interp_eval", fn_type, None)
        });

        let idx = i64_type.const_int(expr_index as u64, true);
        let call_site = self
            .builder
            .build_call(interp_eval, &[idx.into()], "eval")
            .map_err(|e| format!("LLVM interp_eval failed: {}", e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            self.set(dest, ret_val);
        }
        Ok(())
    }

    fn emit_indirect_call(
        &mut self,
        dest: &Option<VReg>,
        callee: VReg,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
        _effect: Effect,
    ) -> Result<(), String> {
        let callee_val = self.get(callee)?;
        let i8_type = self.backend.context.i8_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());

        if let BasicValueEnum::PointerValue(closure_ptr) = callee_val {
            // Load function pointer from closure (at offset 0)
            let base_ptr = self
                .builder
                .build_pointer_cast(closure_ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| format!("cast failed: {}", e))?;
            let offset_val = self.backend.context.i32_type().const_int(0, false);
            let fn_ptr_slot = unsafe {
                self.builder
                    .build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let fn_ptr_slot = self
                .builder
                .build_pointer_cast(
                    fn_ptr_slot,
                    self.backend.context.ptr_type(inkwell::AddressSpace::default()),
                    "fn_ptr_slot_cast",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            let func_ptr = self
                .builder
                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                .map_err(|e| format!("load failed: {}", e))?;

            if let BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                let mut arg_vals: Vec<BasicMetadataValueEnum> = Vec::new();
                for arg in args {
                    let val = self.get(*arg)?;
                    arg_vals.push(val.into());
                }

                let llvm_param_types: Result<Vec<inkwell::types::BasicMetadataTypeEnum>, String> =
                    param_types
                        .iter()
                        .map(|ty| {
                            self.backend
                                .llvm_type(ty)
                                .map(|t| t.into())
                                .map_err(|e| e.to_string())
                        })
                        .collect();
                let llvm_param_types = llvm_param_types?;

                let fn_type = if return_type == TypeId::VOID {
                    self.backend
                        .context
                        .void_type()
                        .fn_type(&llvm_param_types, false)
                } else {
                    let ret_llvm = self.backend.llvm_type(&return_type).map_err(|e| e.to_string())?;
                    match ret_llvm {
                        inkwell::types::BasicTypeEnum::IntType(t) => {
                            t.fn_type(&llvm_param_types, false)
                        }
                        inkwell::types::BasicTypeEnum::FloatType(t) => {
                            t.fn_type(&llvm_param_types, false)
                        }
                        inkwell::types::BasicTypeEnum::PointerType(t) => {
                            t.fn_type(&llvm_param_types, false)
                        }
                        _ => return Err("Unsupported return type in indirect call".to_string()),
                    }
                };

                let call_site = self
                    .builder
                    .build_indirect_call(fn_type, fn_ptr, &arg_vals, "indirect_call")
                    .map_err(|e| format!("indirect call failed: {}", e))?;

                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        self.set(*d, ret_val);
                    }
                }
            }
        } else {
            return Err("IndirectCall requires closure pointer".to_string());
        }
        Ok(())
    }

    // =========================================================================
    // Collections
    // =========================================================================
    fn emit_array_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();
        let array_type = i64_type.array_type(elements.len() as u32);
        let alloc = self
            .builder
            .build_alloca(array_type, "array")
            .map_err(|e| format!("alloca failed: {}", e))?;

        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get(*elem)?;
            let indices = [
                self.backend.context.i32_type().const_int(0, false),
                self.backend.context.i32_type().const_int(i as u64, false),
            ];
            let gep = unsafe {
                self.builder
                    .build_gep(array_type, alloc, &indices, "elem_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            self.builder
                .build_store(gep, elem_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, alloc.into());
        Ok(())
    }

    fn emit_tuple_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();
        let field_types: Vec<inkwell::types::BasicTypeEnum> =
            elements.iter().map(|_| i64_type.into()).collect();
        let struct_type = self.backend.context.struct_type(&field_types, false);
        let alloc = self
            .builder
            .build_alloca(struct_type, "tuple")
            .map_err(|e| format!("alloca failed: {}", e))?;

        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get(*elem)?;
            let gep = self
                .builder
                .build_struct_gep(struct_type, alloc, i as u32, "tuple_elem")
                .map_err(|e| format!("struct gep failed: {}", e))?;
            self.builder
                .build_store(gep, elem_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, alloc.into());
        Ok(())
    }

    fn emit_vec_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        // Vec lit is the same as array lit at the LLVM level
        self.emit_array_lit(dest, elements)
    }

    fn emit_dict_lit(&mut self, dest: VReg, keys: &[VReg], values: &[VReg]) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());

        let dict_new = self.module.get_function("rt_dict_new").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
            self.module.add_function("rt_dict_new", fn_type, None)
        });

        let dict_insert = self.module.get_function("rt_dict_insert").unwrap_or_else(|| {
            let fn_type = self
                .backend
                .context
                .void_type()
                .fn_type(&[i8_ptr_type.into(), i64_type.into(), i64_type.into()], false);
            self.module.add_function("rt_dict_insert", fn_type, None)
        });

        let capacity = i64_type.const_int(keys.len() as u64, false);
        let dict_ptr = self
            .builder
            .build_call(dict_new, &[capacity.into()], "dict")
            .map_err(|e| format!("dict_new call failed: {}", e))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| "dict_new returned void".to_string())?;

        for (key, value) in keys.iter().zip(values.iter()) {
            let key_val = self.get(*key)?;
            let value_val = self.get(*value)?;
            self.builder
                .build_call(
                    dict_insert,
                    &[dict_ptr.into(), key_val.into(), value_val.into()],
                    "",
                )
                .map_err(|e| format!("dict_insert call failed: {}", e))?;
        }
        self.set(dest, dict_ptr);
        Ok(())
    }

    fn emit_index_get(&mut self, dest: VReg, collection: VReg, index: VReg) -> Result<(), String> {
        let coll_val = self.get(collection)?;
        let idx_val = self.get(index)?;

        if let (BasicValueEnum::PointerValue(ptr), BasicValueEnum::IntValue(idx)) =
            (coll_val, idx_val)
        {
            let i64_type = self.backend.context.i64_type();
            let arr_type = i64_type.array_type(0);
            let indices = [self.backend.context.i32_type().const_int(0, false), idx];
            let gep = unsafe {
                self.builder
                    .build_gep(arr_type, ptr, &indices, "elem_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let loaded = self
                .builder
                .build_load(i64_type, gep, "elem")
                .map_err(|e| format!("load failed: {}", e))?;
            self.set(dest, loaded);
        }
        Ok(())
    }

    fn emit_index_set(&mut self, collection: VReg, index: VReg, value: VReg) -> Result<(), String> {
        let coll_val = self.get(collection)?;
        let idx_val = self.get(index)?;
        let val = self.get(value)?;

        if let (BasicValueEnum::PointerValue(ptr), BasicValueEnum::IntValue(idx)) =
            (coll_val, idx_val)
        {
            let i64_type = self.backend.context.i64_type();
            let arr_type = i64_type.array_type(0);
            let indices = [self.backend.context.i32_type().const_int(0, false), idx];
            let gep = unsafe {
                self.builder
                    .build_gep(arr_type, ptr, &indices, "elem_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            self.builder
                .build_store(gep, val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        Ok(())
    }

    fn emit_slice_op(
        &mut self,
        dest: VReg,
        collection: VReg,
        start: Option<VReg>,
        end: Option<VReg>,
        step: Option<VReg>,
    ) -> Result<(), String> {
        let i64_type = self.backend.context.i64_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());

        let slice_fn = self.module.get_function("rt_slice").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            self.module.add_function("rt_slice", fn_type, None)
        });

        let coll_val = self.get(collection)?;
        let start_val = if let Some(s) = start {
            self.get(s)?
        } else {
            i64_type.const_int(0, false).into()
        };
        let end_val = if let Some(e) = end {
            self.get(e)?
        } else {
            i64_type.const_int(i64::MAX as u64, false).into()
        };
        let step_val = if let Some(s) = step {
            self.get(s)?
        } else {
            i64_type.const_int(1, false).into()
        };

        let call_site = self
            .builder
            .build_call(
                slice_fn,
                &[coll_val.into(), start_val.into(), end_val.into(), step_val.into()],
                "slice",
            )
            .map_err(|e| format!("slice call failed: {}", e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            self.set(dest, ret_val);
        }
        Ok(())
    }

    fn emit_fstring_format(&mut self, dest: VReg, parts: &[FStringPart]) -> Result<(), String> {
        // Delegate to runtime for format string assembly
        let result = self.call_runtime("rt_fstring_format", &[self.i64_const(parts.len() as i64)])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // SIMD / Vector operations — delegate to runtime
    // =========================================================================
    fn emit_vec_reduction(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), String> {
        let src = self.get(source)?;
        let result = self.call_runtime("rt_vec_reduction", &[src])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_extract(&mut self, dest: VReg, vector: VReg, index: VReg) -> Result<(), String> {
        let vec_val = self.get(vector)?;
        let idx = self.get(index)?;
        let result = self.call_runtime("rt_vec_extract", &[vec_val, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_with(&mut self, dest: VReg, vector: VReg, index: VReg, value: VReg) -> Result<(), String> {
        let vec_val = self.get(vector)?;
        let idx = self.get(index)?;
        let val = self.get(value)?;
        let result = self.call_runtime("rt_vec_with", &[vec_val, idx, val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_math(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), String> {
        let src = self.get(source)?;
        let result = self.call_runtime("rt_vec_math", &[src])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_shuffle(&mut self, dest: VReg, source: VReg, indices: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let idx = self.get(indices)?;
        let result = self.call_runtime("rt_vec_shuffle", &[src, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_blend(&mut self, dest: VReg, first: VReg, second: VReg, indices: VReg) -> Result<(), String> {
        let a = self.get(first)?;
        let b = self.get(second)?;
        let idx = self.get(indices)?;
        let result = self.call_runtime("rt_vec_blend", &[a, b, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_select(&mut self, dest: VReg, mask: VReg, if_true: VReg, if_false: VReg) -> Result<(), String> {
        let m = self.get(mask)?;
        let t = self.get(if_true)?;
        let f = self.get(if_false)?;
        let result = self.call_runtime("rt_vec_select", &[m, t, f])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_load(&mut self, dest: VReg, array: VReg, offset: VReg) -> Result<(), String> {
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        let result = self.call_runtime("rt_vec_load", &[arr, off])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_store(&mut self, source: VReg, array: VReg, offset: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        self.call_runtime_void("rt_vec_store", &[src, arr, off])
    }

    fn emit_vec_gather(&mut self, dest: VReg, array: VReg, indices: VReg) -> Result<(), String> {
        let arr = self.get(array)?;
        let idx = self.get(indices)?;
        let result = self.call_runtime("rt_vec_gather", &[arr, idx])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_scatter(&mut self, source: VReg, array: VReg, indices: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let arr = self.get(array)?;
        let idx = self.get(indices)?;
        self.call_runtime_void("rt_vec_scatter", &[src, arr, idx])
    }

    fn emit_vec_fma(&mut self, dest: VReg, a: VReg, b: VReg, c: VReg) -> Result<(), String> {
        let av = self.get(a)?;
        let bv = self.get(b)?;
        let cv = self.get(c)?;
        let result = self.call_runtime("rt_vec_fma", &[av, bv, cv])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_recip(&mut self, dest: VReg, source: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let result = self.call_runtime("rt_vec_recip", &[src])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_masked_load(
        &mut self,
        dest: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
        default: VReg,
    ) -> Result<(), String> {
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        let m = self.get(mask)?;
        let def = self.get(default)?;
        let result = self.call_runtime("rt_vec_masked_load", &[arr, off, m, def])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_masked_store(
        &mut self,
        source: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
    ) -> Result<(), String> {
        let src = self.get(source)?;
        let arr = self.get(array)?;
        let off = self.get(offset)?;
        let m = self.get(mask)?;
        self.call_runtime_void("rt_vec_masked_store", &[src, arr, off, m])
    }

    fn emit_vec_min_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), String> {
        let av = self.get(a)?;
        let bv = self.get(b)?;
        let result = self.call_runtime("rt_vec_min", &[av, bv])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_max_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), String> {
        let av = self.get(a)?;
        let bv = self.get(b)?;
        let result = self.call_runtime("rt_vec_max", &[av, bv])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_vec_clamp(&mut self, dest: VReg, source: VReg, lo: VReg, hi: VReg) -> Result<(), String> {
        let src = self.get(source)?;
        let lo_v = self.get(lo)?;
        let hi_v = self.get(hi)?;
        let result = self.call_runtime("rt_vec_clamp", &[src, lo_v, hi_v])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_neighbor_load(&mut self, dest: VReg, array: VReg, direction: NeighborDirection) -> Result<(), String> {
        let arr = self.get(array)?;
        let dir = self.i64_const(direction as i64);
        let result = self.call_runtime("rt_neighbor_load", &[arr, dir])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Structs / Fields
    // =========================================================================
    fn emit_struct_init(
        &mut self,
        dest: VReg,
        struct_size: usize,
        field_offsets: &[u32],
        field_types: &[TypeId],
        field_values: &[VReg],
    ) -> Result<(), String> {
        let i8_type = self.backend.context.i8_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(struct_size as u32);
        let alloc = self
            .builder
            .build_alloca(array_type, "struct")
            .map_err(|e| format!("alloca failed: {}", e))?;
        let struct_ptr = self
            .builder
            .build_pointer_cast(alloc, i8_ptr_type, "struct_ptr")
            .map_err(|e| format!("cast failed: {}", e))?;

        for ((offset, field_type), value) in
            field_offsets.iter().zip(field_types.iter()).zip(field_values.iter())
        {
            let field_val = self.get(*value)?;
            let offset_val = self.backend.context.i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend
                        .context
                        .ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(typed_ptr, field_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, struct_ptr.into());
        Ok(())
    }

    fn emit_field_get(
        &mut self,
        dest: VReg,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
    ) -> Result<(), String> {
        let obj_val = self.get(object)?;
        if let BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.backend.context.i8_type();
            let i8_ptr_type = self
                .backend
                .context
                .ptr_type(inkwell::AddressSpace::default());
            let base_ptr = self
                .builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| format!("cast failed: {}", e))?;
            let offset_val = self
                .backend
                .context
                .i32_type()
                .const_int(byte_offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let llvm_field_ty = self.backend.llvm_type(&field_type).map_err(|e| e.to_string())?;
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend
                        .context
                        .ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            let loaded = self
                .builder
                .build_load(llvm_field_ty, typed_ptr, "field")
                .map_err(|e| format!("load failed: {}", e))?;
            self.set(dest, loaded);
        } else {
            return Err("FieldGet requires pointer to struct".to_string());
        }
        Ok(())
    }

    fn emit_field_set(
        &mut self,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
        value: VReg,
    ) -> Result<(), String> {
        let obj_val = self.get(object)?;
        let val = self.get(value)?;
        if let BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.backend.context.i8_type();
            let i8_ptr_type = self
                .backend
                .context
                .ptr_type(inkwell::AddressSpace::default());
            let base_ptr = self
                .builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| format!("cast failed: {}", e))?;
            let offset_val = self
                .backend
                .context
                .i32_type()
                .const_int(byte_offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend
                        .context
                        .ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(typed_ptr, val)
                .map_err(|e| format!("store failed: {}", e))?;
        } else {
            return Err("FieldSet requires pointer to struct".to_string());
        }
        Ok(())
    }

    // =========================================================================
    // Closures
    // =========================================================================
    fn emit_closure_create(
        &mut self,
        dest: VReg,
        func_name: &str,
        closure_size: usize,
        capture_offsets: &[u32],
        captures: &[VReg],
    ) -> Result<(), String> {
        let i8_type = self.backend.context.i8_type();
        let i8_ptr_type = self
            .backend
            .context
            .ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(closure_size as u32);
        let alloc = self
            .builder
            .build_alloca(array_type, "closure")
            .map_err(|e| format!("alloca failed: {}", e))?;
        let closure_ptr = self
            .builder
            .build_pointer_cast(alloc, i8_ptr_type, "closure_ptr")
            .map_err(|e| format!("cast failed: {}", e))?;

        // Store function pointer at offset 0
        let func_ptr = self
            .module
            .get_function(func_name)
            .map(|f| f.as_global_value().as_pointer_value())
            .unwrap_or_else(|| i8_ptr_type.const_null());
        let func_ptr_cast = self
            .builder
            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
            .map_err(|e| format!("cast failed: {}", e))?;
        let fn_slot = self
            .builder
            .build_pointer_cast(
                closure_ptr,
                self.backend.context.ptr_type(inkwell::AddressSpace::default()),
                "fn_slot",
            )
            .map_err(|e| format!("cast failed: {}", e))?;
        self.builder
            .build_store(fn_slot, func_ptr_cast)
            .map_err(|e| format!("store failed: {}", e))?;

        // Store captured values at their offsets
        for (offset, value) in capture_offsets.iter().zip(captures.iter()) {
            let capture_val = self.get(*value)?;
            let offset_val = self.backend.context.i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe {
                self.builder
                    .build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr")
                    .map_err(|e| format!("gep failed: {}", e))?
            };
            let typed_ptr = self
                .builder
                .build_pointer_cast(
                    field_ptr,
                    self.backend
                        .context
                        .ptr_type(inkwell::AddressSpace::default()),
                    "cap_typed_ptr",
                )
                .map_err(|e| format!("cast failed: {}", e))?;
            self.builder
                .build_store(typed_ptr, capture_val)
                .map_err(|e| format!("store failed: {}", e))?;
        }
        self.set(dest, closure_ptr.into());
        Ok(())
    }

    // =========================================================================
    // Methods — delegate to runtime
    // =========================================================================
    fn emit_method_call_static(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        func_name: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        // Static method call: prepend receiver to args and call function
        let mut all_args = vec![receiver];
        all_args.extend_from_slice(args);
        self.emit_call(dest, &CallTarget::from_name(func_name), &all_args)
    }

    fn emit_method_call_virtual(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        vtable_slot: usize,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
    ) -> Result<(), String> {
        // Virtual dispatch: call runtime to resolve vtable
        let recv = self.get(receiver)?;
        let slot = self.i64_const(vtable_slot as i64);
        let func_ptr = self.call_runtime("rt_vtable_lookup", &[recv, slot])?;

        // Build indirect call with the resolved function pointer
        let mut all_args = vec![receiver];
        all_args.extend_from_slice(args);

        let mut all_param_types = vec![TypeId::I64]; // receiver type
        all_param_types.extend_from_slice(param_types);

        // Store the function pointer temporarily
        let temp = VReg(u32::MAX - 1);
        self.set(temp, func_ptr);
        self.emit_indirect_call(dest, temp, &all_param_types, return_type, &all_args, Effect::Compute)
    }

    fn emit_builtin_method(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        receiver_type: &str,
        method: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        let rt_name = format!("rt_builtin_{}_{}", receiver_type, method);
        let recv = self.get(receiver)?;
        let mut rt_args = vec![recv];
        for arg in args {
            rt_args.push(self.get(*arg)?);
        }
        let result = self.call_runtime(&rt_name, &rt_args)?;
        if let Some(d) = dest {
            self.set(*d, result);
        }
        Ok(())
    }

    fn emit_extern_method_call(
        &mut self,
        dest: &Option<VReg>,
        receiver: Option<VReg>,
        class_name: &str,
        method_name: &str,
        _is_static: bool,
        args: &[VReg],
    ) -> Result<(), String> {
        let rt_name = format!("{}_{}", class_name, method_name);
        let mut rt_args = Vec::new();
        if let Some(recv) = receiver {
            rt_args.push(self.get(recv)?);
        }
        for arg in args {
            rt_args.push(self.get(*arg)?);
        }
        if rt_args.is_empty() {
            let result = self.call_runtime(&rt_name, &[])?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
        } else {
            let result = self.call_runtime(&rt_name, &rt_args)?;
            if let Some(d) = dest {
                self.set(*d, result);
            }
        }
        Ok(())
    }

    // =========================================================================
    // Pattern matching — delegate to runtime
    // =========================================================================
    fn emit_pattern_test(&mut self, dest: VReg, subject: VReg, _pattern: &MirPattern) -> Result<(), String> {
        let subj = self.get(subject)?;
        let result = self.call_runtime("rt_pattern_test", &[subj])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_pattern_bind(
        &mut self,
        dest: VReg,
        subject: VReg,
        _binding: &PatternBinding,
    ) -> Result<(), String> {
        let subj = self.get(subject)?;
        let result = self.call_runtime("rt_pattern_bind", &[subj])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Enums / Unions — delegate to runtime
    // =========================================================================
    fn emit_enum_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_enum_discriminant", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_enum_payload(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_enum_payload", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_enum_unit(&mut self, dest: VReg, _variant_name: &str) -> Result<(), String> {
        // Enum unit variant: encode as tagged integer (discriminant only)
        let result = self.call_runtime("rt_enum_unit", &[self.i64_const(0)])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_enum_with(&mut self, dest: VReg, _variant_name: &str, payload: VReg) -> Result<(), String> {
        let pay = self.get(payload)?;
        let result = self.call_runtime("rt_enum_with", &[pay])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_union_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_union_discriminant", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_union_payload(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_union_payload", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_union_wrap(&mut self, dest: VReg, value: VReg, type_index: u32) -> Result<(), String> {
        let val = self.get(value)?;
        let idx = self.i64_const(type_index as i64);
        let result = self.call_runtime("rt_union_wrap", &[val, idx])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Async / Concurrency — delegate to runtime
    // =========================================================================
    fn emit_future_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        let block_id = self.i64_const(body_block.0 as i64);
        let result = self.call_runtime("rt_future_create", &[block_id])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_await(&mut self, dest: VReg, future: VReg) -> Result<(), String> {
        let fut = self.get(future)?;
        let result = self.call_runtime("rt_future_await", &[fut])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_spawn(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        let block_id = self.i64_const(body_block.0 as i64);
        let result = self.call_runtime("rt_actor_spawn", &[block_id])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_send(&mut self, actor: VReg, message: VReg) -> Result<(), String> {
        let act = self.get(actor)?;
        let msg = self.get(message)?;
        self.call_runtime_void("rt_actor_send", &[act, msg])
    }

    fn emit_actor_recv(&mut self, dest: VReg) -> Result<(), String> {
        let result = self.call_runtime("rt_actor_recv", &[])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_join(&mut self, dest: VReg, actor: VReg) -> Result<(), String> {
        let act = self.get(actor)?;
        let result = self.call_runtime("rt_actor_join", &[act])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_actor_reply(&mut self, message: VReg) -> Result<(), String> {
        let msg = self.get(message)?;
        self.call_runtime_void("rt_actor_reply", &[msg])
    }

    fn emit_generator_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        let block_id = self.i64_const(body_block.0 as i64);
        let result = self.call_runtime("rt_generator_create", &[block_id])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_yield(&mut self, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        self.call_runtime_void("rt_generator_yield", &[val])
    }

    fn emit_generator_next(&mut self, dest: VReg, generator: VReg) -> Result<(), String> {
        let gen = self.get(generator)?;
        let result = self.call_runtime("rt_generator_next", &[gen])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Result / Option — delegate to runtime
    // =========================================================================
    fn emit_try_unwrap(
        &mut self,
        dest: VReg,
        value: VReg,
        _error_block: BlockId,
        _error_dest: VReg,
    ) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_try_unwrap", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_option_some(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_option_some", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_option_none(&mut self, dest: VReg) -> Result<(), String> {
        let result = self.call_runtime("rt_option_none", &[])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_result_ok(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_result_ok", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_result_err(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_result_err", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Contracts — delegate to runtime
    // =========================================================================
    fn emit_contract_check(
        &mut self,
        condition: VReg,
        _kind: ContractKind,
        _func_name: &str,
        _message: Option<&str>,
    ) -> Result<(), String> {
        let cond = self.get(condition)?;
        self.call_runtime_void("rt_contract_check", &[cond])
    }

    fn emit_contract_old_capture(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        // Old capture: just copy the value (snapshot semantics)
        let val = self.get(value)?;
        self.set(dest, val);
        Ok(())
    }

    // =========================================================================
    // Coverage — delegate to runtime
    // =========================================================================
    fn emit_decision_probe(
        &mut self,
        result: VReg,
        decision_id: u32,
        _file: &str,
        _line: u32,
        _column: u32,
    ) -> Result<(), String> {
        let res = self.get(result)?;
        let id = self.i64_const(decision_id as i64);
        self.call_runtime_void("rt_coverage_decision", &[res, id])
    }

    fn emit_condition_probe(
        &mut self,
        decision_id: u32,
        condition_id: u32,
        result: VReg,
        _file: &str,
        _line: u32,
        _column: u32,
    ) -> Result<(), String> {
        let res = self.get(result)?;
        let did = self.i64_const(decision_id as i64);
        let cid = self.i64_const(condition_id as i64);
        self.call_runtime_void("rt_coverage_condition", &[res, did, cid])
    }

    fn emit_path_probe(&mut self, path_id: u32, block_id: u32) -> Result<(), String> {
        let pid = self.i64_const(path_id as i64);
        let bid = self.i64_const(block_id as i64);
        self.call_runtime_void("rt_coverage_path", &[pid, bid])
    }

    // =========================================================================
    // Units — inline LLVM IR (icmp + select)
    // =========================================================================
    fn emit_unit_bound_check(
        &mut self,
        value: VReg,
        _unit_name: &str,
        min: i64,
        max: i64,
        _overflow: UnitOverflowBehavior,
    ) -> Result<(), String> {
        let val = self.get(value)?;
        let min_val = self.i64_const(min);
        let max_val = self.i64_const(max);
        self.call_runtime_void("rt_unit_bound_check", &[val, min_val, max_val])
    }

    fn emit_unit_widen(
        &mut self,
        dest: VReg,
        value: VReg,
        _from_bits: u8,
        _to_bits: u8,
        _signed: bool,
    ) -> Result<(), String> {
        // Widen: at the LLVM level with uniform i64 representation, this is a copy
        let val = self.get(value)?;
        self.set(dest, val);
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
    ) -> Result<(), String> {
        // Narrow: at the LLVM level with uniform i64, this is a copy (bounds checked elsewhere)
        let val = self.get(value)?;
        self.set(dest, val);
        Ok(())
    }

    fn emit_unit_saturate(&mut self, dest: VReg, value: VReg, min: i64, max: i64) -> Result<(), String> {
        let val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let i64_type = self.backend.context.i64_type();
            let min_v = i64_type.const_int(min as u64, true);
            let max_v = i64_type.const_int(max as u64, true);

            // clamp: max(min, min(val, max))
            let cmp_max = self
                .builder
                .build_int_compare(inkwell::IntPredicate::SLT, int_val, max_v, "cmp_max")
                .map_err(|e| format!("icmp failed: {}", e))?;
            let sel_max = self
                .builder
                .build_select(cmp_max, int_val, max_v, "sel_max")
                .map_err(|e| format!("select failed: {}", e))?;

            if let BasicValueEnum::IntValue(clamped_high) = sel_max {
                let cmp_min = self
                    .builder
                    .build_int_compare(inkwell::IntPredicate::SGT, clamped_high, min_v, "cmp_min")
                    .map_err(|e| format!("icmp failed: {}", e))?;
                let sel_min = self
                    .builder
                    .build_select(cmp_min, clamped_high, min_v, "sel_min")
                    .map_err(|e| format!("select failed: {}", e))?;
                self.set(dest, sel_min);
            } else {
                self.set(dest, val);
            }
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    // =========================================================================
    // Pointers — delegate to runtime
    // =========================================================================
    fn emit_pointer_new(&mut self, dest: VReg, _kind: PointerKind, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        let result = self.call_runtime("rt_pointer_new", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_pointer_ref(&mut self, dest: VReg, _kind: PointerKind, source: VReg) -> Result<(), String> {
        let val = self.get(source)?;
        let result = self.call_runtime("rt_pointer_ref", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_pointer_deref(&mut self, dest: VReg, pointer: VReg, _kind: PointerKind) -> Result<(), String> {
        let val = self.get(pointer)?;
        let result = self.call_runtime("rt_pointer_deref", &[val])?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Memory safety — no-ops (use trait defaults)
    // =========================================================================
    fn emit_drop(&mut self, _value: VReg, _ty: TypeId) -> Result<(), String> {
        Ok(())
    }

    fn emit_end_scope(&mut self, _local_index: usize) -> Result<(), String> {
        Ok(())
    }

    // =========================================================================
    // Boxing (FFI boundary) — inline LLVM IR
    // =========================================================================
    fn emit_box_int(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let mut val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let val_type = int_val.get_type();
            let i64_type = self.backend.context.i64_type();
            let mut int_v = int_val;
            if val_type.get_bit_width() < 64 {
                int_v = self
                    .builder
                    .build_int_s_extend(int_val, i64_type, "sext")
                    .map_err(|e| format!("sext failed: {}", e))?;
            }
            let three = i64_type.const_int(3, false);
            let boxed = self
                .builder
                .build_left_shift(int_v, three, "box_shl")
                .map_err(|e| format!("shl failed: {}", e))?;
            self.set(dest, boxed.into());
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_box_float(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        if let BasicValueEnum::FloatValue(_) = val {
            let i64_type = self.backend.context.i64_type();
            let bits = self
                .builder
                .build_bit_cast(val, i64_type, "f2i")
                .map_err(|e| format!("bitcast failed: {}", e))?;
            if let BasicValueEnum::IntValue(bits_int) = bits {
                let three = i64_type.const_int(3, false);
                let shifted = self
                    .builder
                    .build_right_shift(bits_int, three, false, "ushr")
                    .map_err(|e| format!("ushr failed: {}", e))?;
                let payload = self
                    .builder
                    .build_left_shift(shifted, three, "shl")
                    .map_err(|e| format!("shl failed: {}", e))?;
                let tag = i64_type.const_int(2, false);
                let boxed = self
                    .builder
                    .build_or(payload, tag, "box_or")
                    .map_err(|e| format!("or failed: {}", e))?;
                self.set(dest, boxed.into());
            } else {
                self.set(dest, val);
            }
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_unbox_int(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let i64_type = self.backend.context.i64_type();
            let three = i64_type.const_int(3, false);
            let unboxed = self
                .builder
                .build_right_shift(int_val, three, true, "unbox_sshr")
                .map_err(|e| format!("sshr failed: {}", e))?;
            self.set(dest, unboxed.into());
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    fn emit_unbox_float(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self.get(value)?;
        if let BasicValueEnum::IntValue(int_val) = val {
            let i64_type = self.backend.context.i64_type();
            let f64_type = self.backend.context.f64_type();
            let three = i64_type.const_int(3, false);
            let shifted = self
                .builder
                .build_right_shift(int_val, three, false, "ushr")
                .map_err(|e| format!("ushr failed: {}", e))?;
            let bits = self
                .builder
                .build_left_shift(shifted, three, "shl")
                .map_err(|e| format!("shl failed: {}", e))?;
            let unboxed = self
                .builder
                .build_bit_cast(bits, f64_type, "i2f")
                .map_err(|e| format!("bitcast failed: {}", e))?;
            self.set(dest, unboxed);
        } else {
            self.set(dest, val);
        }
        Ok(())
    }

    // =========================================================================
    // GPU instructions — delegate to LlvmBackend helpers
    // =========================================================================
    fn emit_gpu_global_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_global_id(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_local_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_local_id(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_group_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_group_id(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_global_size(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_global_size(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_local_size(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_local_size(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_num_groups(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_num_groups(dim, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_barrier(&mut self) -> Result<(), String> {
        self.backend
            .compile_gpu_barrier(self.builder, self.module)
            .map_err(|e| e.to_string())
    }

    fn emit_gpu_mem_fence(&mut self, scope: GpuMemoryScope) -> Result<(), String> {
        self.backend
            .compile_gpu_mem_fence(scope, self.builder, self.module)
            .map_err(|e| e.to_string())
    }

    fn emit_gpu_shared_alloc(&mut self, dest: VReg, _element_type: TypeId, size: u32) -> Result<(), String> {
        let result = self
            .backend
            .compile_gpu_shared_alloc(size, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_atomic(&mut self, dest: VReg, op: GpuAtomicOp, ptr: VReg, value: VReg) -> Result<(), String> {
        let ptr_val = self.get(ptr)?;
        let value_val = self.get(value)?;
        let result = self
            .backend
            .compile_gpu_atomic(op, ptr_val, value_val, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_gpu_atomic_cmpxchg(
        &mut self,
        dest: VReg,
        ptr: VReg,
        expected: VReg,
        desired: VReg,
    ) -> Result<(), String> {
        let ptr_val = self.get(ptr)?;
        let expected_val = self.get(expected)?;
        let desired_val = self.get(desired)?;
        let result = self
            .backend
            .compile_gpu_atomic_cmpxchg(ptr_val, expected_val, desired_val, self.builder, self.module)
            .map_err(|e| e.to_string())?;
        self.set(dest, result);
        Ok(())
    }

    // =========================================================================
    // Parallel iterators — delegate to runtime
    // =========================================================================
    fn emit_par_map(
        &mut self,
        dest: VReg,
        input: VReg,
        closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let cls = self.get(closure)?;
        let result = self.call_runtime("rt_par_map", &[inp, cls])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_par_reduce(
        &mut self,
        dest: VReg,
        input: VReg,
        initial: VReg,
        closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let init = self.get(initial)?;
        let cls = self.get(closure)?;
        let result = self.call_runtime("rt_par_reduce", &[inp, init, cls])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_par_filter(
        &mut self,
        dest: VReg,
        input: VReg,
        predicate: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let pred = self.get(predicate)?;
        let result = self.call_runtime("rt_par_filter", &[inp, pred])?;
        self.set(dest, result);
        Ok(())
    }

    fn emit_par_for_each(
        &mut self,
        input: VReg,
        closure: VReg,
        _backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        let inp = self.get(input)?;
        let cls = self.get(closure)?;
        self.call_runtime_void("rt_par_for_each", &[inp, cls])
    }
}
